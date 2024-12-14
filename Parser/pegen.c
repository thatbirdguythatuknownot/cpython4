#include <Python.h>
#include "pycore_ast.h"           // _PyAST_Validate(),
#include "pycore_pystate.h"       // _PyThreadState_GET()
#include <errcode.h>

#include "tokenizer.h"
#include "pegen.h"

// Internal parser functions

asdl_stmt_seq*
_PyPegen_interactive_exit(Parser *p)
{
    if (p->errcode) {
        *(p->errcode) = E_EOF;
    }
    return NULL;
}

Py_ssize_t
_PyPegen_byte_offset_to_character_offset(PyObject *line, Py_ssize_t col_offset)
{
    const char *str = PyUnicode_AsUTF8(line);
    if (!str) {
        return -1;
    }
    Py_ssize_t len = strlen(str);
    if (col_offset > len + 1) {
        col_offset = len + 1;
    }
    assert(col_offset >= 0);
    PyObject *text = PyUnicode_DecodeUTF8(str, col_offset, "replace");
    if (!text) {
        return -1;
    }
    Py_ssize_t size = PyUnicode_GET_LENGTH(text);
    Py_DECREF(text);
    return size;
}

// Here, mark is the start of the node, while p->mark is the end.
// If node==NULL, they should be the same.
int
_PyPegen_insert_memo(Parser *p, int mark, int type, void *node)
{
    if (node) {
        return 0;
    }
    // Insert in front
    Memo *m = _PyArena_Malloc(p->arena, sizeof(Memo));
    if (m == NULL) {
        return -1;
    }
    m->type = type;
    m->node = node;
    m->mark = p->mark;
    m->next = p->tokens[mark]->memo;
    p->tokens[mark]->memo = m;
    return 0;
}

// Like _PyPegen_insert_memo(), but updates an existing node if found.
int
_PyPegen_update_memo(Parser *p, int mark, int type, void *node)
{
    for (Memo *m = p->tokens[mark]->memo; m != NULL; m = m->next) {
        if (m->type == type) {
            // Update existing node.
            m->node = node;
            m->mark = p->mark;
            return 0;
        }
    }
    // Insert new node.
    return _PyPegen_insert_memo(p, mark, type, node);
}

static int
init_normalization(Parser *p)
{
    if (p->normalize) {
        return 1;
    }
    p->normalize = _PyImport_GetModuleAttrString("unicodedata", "normalize");
    if (!p->normalize)
    {
        return 0;
    }
    return 1;
}

static int
growable_comment_array_init(growable_comment_array *arr, size_t initial_size) {
    assert(initial_size > 0);
    arr->items = PyMem_Malloc(initial_size * sizeof(*arr->items));
    arr->size = initial_size;
    arr->num_items = 0;

    return arr->items != NULL;
}

static int
growable_comment_array_add(growable_comment_array *arr, int lineno, char *comment) {
    if (arr->num_items >= arr->size) {
        size_t new_size = arr->size * 2;
        void *new_items_array = PyMem_Realloc(arr->items, new_size * sizeof(*arr->items));
        if (!new_items_array) {
            return 0;
        }
        arr->items = new_items_array;
        arr->size = new_size;
    }

    arr->items[arr->num_items].lineno = lineno;
    arr->items[arr->num_items].comment = comment;  // Take ownership
    arr->num_items++;
    return 1;
}

static void
growable_comment_array_deallocate(growable_comment_array *arr) {
    for (unsigned i = 0; i < arr->num_items; i++) {
        PyMem_Free(arr->items[i].comment);
    }
    PyMem_Free(arr->items);
}

static int
_get_keyword_or_name_type(Parser *p, struct token *new_token)
{
    int name_len = new_token->end_col_offset - new_token->col_offset;
    assert(name_len > 0);

    if (name_len >= p->n_keyword_lists ||
        p->keywords[name_len] == NULL ||
        p->keywords[name_len]->type == -1) {
        return NAME;
    }
    for (KeywordToken *k = p->keywords[name_len]; k != NULL && k->type != -1; k++) {
        if (strncmp(k->str, new_token->start, name_len) == 0) {
            return k->type;
        }
    }
    return NAME;
}

static int
initialize_token(Parser *p, Token *parser_token, struct token *new_token, int token_type) {
    assert(parser_token != NULL);

    parser_token->type = (token_type == NAME) ? _get_keyword_or_name_type(p, new_token) : token_type;
    parser_token->bytes = PyBytes_FromStringAndSize(new_token->start, new_token->end - new_token->start);
    if (parser_token->bytes == NULL) {
        return -1;
    }
    if (_PyArena_AddPyObject(p->arena, parser_token->bytes) < 0) {
        Py_DECREF(parser_token->bytes);
        return -1;
    }

    parser_token->metadata = NULL;
    if (new_token->metadata != NULL) {
        if (_PyArena_AddPyObject(p->arena, new_token->metadata) < 0) {
            Py_DECREF(parser_token->metadata);
            return -1;
        }
        parser_token->metadata = new_token->metadata;
        new_token->metadata = NULL;
    }

    parser_token->level = new_token->level;
    parser_token->lineno = new_token->lineno;
    parser_token->col_offset = p->tok->lineno == p->starting_lineno ? p->starting_col_offset + new_token->col_offset
                                                                    : new_token->col_offset;
    parser_token->end_lineno = new_token->end_lineno;
    parser_token->end_col_offset = p->tok->lineno == p->starting_lineno ? p->starting_col_offset + new_token->end_col_offset
                                                                 : new_token->end_col_offset;

    p->fill += 1;

    if (token_type == ERRORTOKEN && p->tok->done == E_DECODE) {
        return _Pypegen_raise_decode_error(p);
    }

    return (token_type == ERRORTOKEN ? _Pypegen_tokenizer_error(p) : 0);
}

static int
_resize_tokens_array(Parser *p) {
    int newsize = p->size * 2;
    Token **new_tokens = PyMem_Realloc(p->tokens, newsize * sizeof(Token *));
    if (new_tokens == NULL) {
        PyErr_NoMemory();
        return -1;
    }
    p->tokens = new_tokens;

    for (int i = p->size; i < newsize; i++) {
        p->tokens[i] = PyMem_Calloc(1, sizeof(Token));
        if (p->tokens[i] == NULL) {
            p->size = i; // Needed, in order to cleanup correctly after parser fails
            PyErr_NoMemory();
            return -1;
        }
    }
    p->size = newsize;
    return 0;
}

int
_PyPegen_fill_token(Parser *p)
{
    struct token new_token;
    _PyToken_Init(&new_token);
    int type = _PyTokenizer_Get(p->tok, &new_token);

    // Record and skip '# type: ignore' comments
    while (type == TYPE_IGNORE) {
        Py_ssize_t len = new_token.end_col_offset - new_token.col_offset;
        char *tag = PyMem_Malloc(len + 1);
        if (tag == NULL) {
            PyErr_NoMemory();
            goto error;
        }
        strncpy(tag, new_token.start, len);
        tag[len] = '\0';
        // Ownership of tag passes to the growable array
        if (!growable_comment_array_add(&p->type_ignore_comments, p->tok->lineno, tag)) {
            PyErr_NoMemory();
            goto error;
        }
        type = _PyTokenizer_Get(p->tok, &new_token);
    }

    // If we have reached the end and we are in single input mode we need to insert a newline and reset the parsing
    if (p->start_rule == Py_single_input && type == ENDMARKER && p->parsing_started) {
        type = NEWLINE; /* Add an extra newline */
        p->parsing_started = 0;

        if (p->tok->indent && !(p->flags & PyPARSE_DONT_IMPLY_DEDENT)) {
            p->tok->pendin = -p->tok->indent;
            p->tok->indent = 0;
        }
    }
    else {
        p->parsing_started = 1;
    }

    // Check if we are at the limit of the token array capacity and resize if needed
    if ((p->fill == p->size) && (_resize_tokens_array(p) != 0)) {
        goto error;
    }

    Token *t = p->tokens[p->fill];
    return initialize_token(p, t, &new_token, type);
error:
    _PyToken_Free(&new_token);
    return -1;
}

#if defined(Py_DEBUG)
// Instrumentation to count the effectiveness of memoization.
// The array counts the number of tokens skipped by memoization,
// indexed by type.

#define NSTATISTICS _PYPEGEN_NSTATISTICS
#define memo_statistics _PyRuntime.parser.memo_statistics

void
_PyPegen_clear_memo_statistics(void)
{
    for (int i = 0; i < NSTATISTICS; i++) {
        memo_statistics[i] = 0;
    }
}

PyObject *
_PyPegen_get_memo_statistics(void)
{
    PyObject *ret = PyList_New(NSTATISTICS);
    if (ret == NULL) {
        return NULL;
    }
    for (int i = 0; i < NSTATISTICS; i++) {
        PyObject *value = PyLong_FromLong(memo_statistics[i]);
        if (value == NULL) {
            Py_DECREF(ret);
            return NULL;
        }
        // PyList_SetItem borrows a reference to value.
        if (PyList_SetItem(ret, i, value) < 0) {
            Py_DECREF(ret);
            return NULL;
        }
    }
    return ret;
}
#endif

int  // bool
_PyPegen_is_memoized(Parser *p, int type, void *pres)
{
    if (p->mark == p->fill) {
        if (_PyPegen_fill_token(p) < 0) {
            p->error_indicator = 1;
            return -1;
        }
    }

    Token *t = p->tokens[p->mark];

    for (Memo *m = t->memo; m != NULL; m = m->next) {
        if (m->type == type) {
#if defined(PY_DEBUG)
            if (0 <= type && type < NSTATISTICS) {
                long count = m->mark - p->mark;
                // A memoized negative result counts for one.
                if (count <= 0) {
                    count = 1;
                }
                memo_statistics[type] += count;
            }
#endif
            p->mark = m->mark;
            *(void **)(pres) = m->node;
            return 1;
        }
    }
    return 0;
}

int
_PyPegen_lookahead_with_name(int positive, expr_ty (func)(Parser *), Parser *p)
{
    int mark = p->mark;
    void *res = func(p);
    p->mark = mark;
    return (res != NULL) == positive;
}

int
_PyPegen_lookahead_with_string(int positive, expr_ty (func)(Parser *, const char*), Parser *p, const char* arg)
{
    int mark = p->mark;
    void *res = func(p, arg);
    p->mark = mark;
    return (res != NULL) == positive;
}

int
_PyPegen_lookahead_with_int(int positive, Token *(func)(Parser *, int), Parser *p, int arg)
{
    int mark = p->mark;
    void *res = func(p, arg);
    p->mark = mark;
    return (res != NULL) == positive;
}

int
_PyPegen_lookahead(int positive, void *(func)(Parser *), Parser *p)
{
    int mark = p->mark;
    void *res = (void*)func(p);
    p->mark = mark;
    return (res != NULL) == positive;
}

Token *
_PyPegen_expect_token(Parser *p, int type)
{
    if (p->mark == p->fill) {
        if (_PyPegen_fill_token(p) < 0) {
            p->error_indicator = 1;
            return NULL;
        }
    }
    Token *t = p->tokens[p->mark];
    if (t->type != type) {
       return NULL;
    }
    if (_PyPegen_check_restricted(p, type)) {
        return NULL;
    }
    p->mark += 1;
    return t;
}

void*
_PyPegen_expect_forced_result(Parser *p, void* result, const char* expected) {

    if (p->error_indicator == 1) {
        return NULL;
    }
    if (result == NULL) {
        RAISE_SYNTAX_ERROR("expected (%s)", expected);
        return NULL;
    }
    return result;
}

Token *
_PyPegen_expect_forced_token(Parser *p, int type, const char* expected) {

    if (p->error_indicator == 1) {
        return NULL;
    }

    if (p->mark == p->fill) {
        if (_PyPegen_fill_token(p) < 0) {
            p->error_indicator = 1;
            return NULL;
        }
    }
    Token *t = p->tokens[p->mark];
    if (t->type != type) {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(t, "expected '%s'", expected);
        return NULL;
    }
    p->mark += 1;
    return t;
}

expr_ty
_PyPegen_expect_soft_keyword(Parser *p, const char *keyword)
{
    if (p->mark == p->fill) {
        if (_PyPegen_fill_token(p) < 0) {
            p->error_indicator = 1;
            return NULL;
        }
    }
    Token *t = p->tokens[p->mark];
    if (t->type != NAME) {
        return NULL;
    }
    const char *s = PyBytes_AsString(t->bytes);
    if (!s) {
        p->error_indicator = 1;
        return NULL;
    }
    if (strcmp(s, keyword) != 0) {
        return NULL;
    }
    return _PyPegen_name_token(p);
}

Token *
_PyPegen_get_last_nonnwhitespace_token(Parser *p)
{
    assert(p->mark >= 0);
    Token *token = NULL;
    for (int m = p->mark - 1; m >= 0; m--) {
        token = p->tokens[m];
        if (token->type != ENDMARKER && (token->type < NEWLINE || token->type > DEDENT)) {
            break;
        }
    }
    return token;
}

PyObject *
_PyPegen_new_identifier(Parser *p, const char *n)
{
    PyObject *id = PyUnicode_DecodeUTF8(n, strlen(n), NULL);
    if (!id) {
        goto error;
    }
    /* PyUnicode_DecodeUTF8 should always return a ready string. */
    assert(PyUnicode_IS_READY(id));
    /* Check whether there are non-ASCII characters in the
       identifier; if so, normalize to NFKC. */
    if (!PyUnicode_IS_ASCII(id))
    {
        if (!init_normalization(p))
        {
            Py_DECREF(id);
            goto error;
        }
        PyObject *form = PyUnicode_InternFromString("NFKC");
        if (form == NULL)
        {
            Py_DECREF(id);
            goto error;
        }
        PyObject *args[2] = {form, id};
        PyObject *id2 = PyObject_Vectorcall(p->normalize, args, 2, NULL);
        Py_DECREF(id);
        Py_DECREF(form);
        if (!id2) {
            goto error;
        }

        if (!PyUnicode_Check(id2))
        {
            PyErr_Format(PyExc_TypeError,
                         "unicodedata.normalize() must return a string, not "
                         "%.200s",
                         _PyType_Name(Py_TYPE(id2)));
            Py_DECREF(id2);
            goto error;
        }
        id = id2;
    }
    PyUnicode_InternInPlace(&id);
    if (_PyArena_AddPyObject(p->arena, id) < 0)
    {
        Py_DECREF(id);
        goto error;
    }
    return id;

error:
    p->error_indicator = 1;
    return NULL;
}

static expr_ty
_PyPegen_name_from_token(Parser *p, Token* t)
{
    if (t == NULL) {
        return NULL;
    }
    const char *s = PyBytes_AsString(t->bytes);
    if (!s) {
        p->error_indicator = 1;
        return NULL;
    }
    PyObject *id = _PyPegen_new_identifier(p, s);
    if (id == NULL) {
        p->error_indicator = 1;
        return NULL;
    }
    return _PyAST_Name(id, Load, t->lineno, t->col_offset, t->end_lineno,
                       t->end_col_offset, p->arena);
}

expr_ty
_PyPegen_name_token(Parser *p)
{
    Token *t = _PyPegen_expect_token(p, NAME);
    return _PyPegen_name_from_token(p, t);
}

void *
_PyPegen_string_token(Parser *p)
{
    return _PyPegen_expect_token(p, STRING);
}

expr_ty _PyPegen_soft_keyword_token(Parser *p) {
    Token *t = _PyPegen_expect_token(p, NAME);
    if (t == NULL) {
        return NULL;
    }
    char *the_token;
    Py_ssize_t size;
    PyBytes_AsStringAndSize(t->bytes, &the_token, &size);
    for (char **keyword = p->soft_keywords; *keyword != NULL; keyword++) {
        if (strncmp(*keyword, the_token, size) == 0) {
            return _PyPegen_name_from_token(p, t);
        }
    }
    return NULL;
}

static PyObject *
parsenumber_raw(const char *s)
{
    const char *end;
    long x;
    double dx;
    Py_complex compl;
    int imflag;

    assert(s != NULL);
    errno = 0;
    end = s + strlen(s) - 1;
    imflag = *end == 'j' || *end == 'J';
    if (s[0] == '0') {
        x = (long)PyOS_strtoul(s, (char **)&end, 0);
        if (x < 0 && errno == 0) {
            return PyLong_FromString(s, (char **)0, 0);
        }
    }
    else {
        x = PyOS_strtol(s, (char **)&end, 0);
    }
    if (*end == '\0') {
        if (errno != 0) {
            return PyLong_FromString(s, (char **)0, 0);
        }
        return PyLong_FromLong(x);
    }
    /* XXX Huge floats may silently fail */
    if (imflag) {
        compl.real = 0.;
        compl.imag = PyOS_string_to_double(s, (char **)&end, NULL);
        if (compl.imag == -1.0 && PyErr_Occurred()) {
            return NULL;
        }
        return PyComplex_FromCComplex(compl);
    }
    dx = PyOS_string_to_double(s, NULL, NULL);
    if (dx == -1.0 && PyErr_Occurred()) {
        return NULL;
    }
    return PyFloat_FromDouble(dx);
}

static PyObject *
parsenumber(const char *s)
{
    char *dup;
    char *end;
    PyObject *res = NULL;

    assert(s != NULL);

    if (strchr(s, '_') == NULL) {
        return parsenumber_raw(s);
    }
    /* Create a duplicate without underscores. */
    dup = PyMem_Malloc(strlen(s) + 1);
    if (dup == NULL) {
        return PyErr_NoMemory();
    }
    end = dup;
    for (; *s; s++) {
        if (*s != '_') {
            *end++ = *s;
        }
    }
    *end = '\0';
    res = parsenumber_raw(dup);
    PyMem_Free(dup);
    return res;
}

expr_ty
_PyPegen_number_token(Parser *p)
{
    Token *t = _PyPegen_expect_token(p, NUMBER);
    if (t == NULL) {
        return NULL;
    }

    const char *num_raw = PyBytes_AsString(t->bytes);
    if (num_raw == NULL) {
        p->error_indicator = 1;
        return NULL;
    }

    if (p->feature_version < 6 && strchr(num_raw, '_') != NULL) {
        p->error_indicator = 1;
        return RAISE_SYNTAX_ERROR("Underscores in numeric literals are only supported "
                                  "in Python 3.6 and greater");
    }

    PyObject *c = parsenumber(num_raw);

    if (c == NULL) {
        p->error_indicator = 1;
        PyThreadState *tstate = _PyThreadState_GET();
        // The only way a ValueError should happen in _this_ code is via
        // PyLong_FromString hitting a length limit.
        if (tstate->current_exception != NULL &&
            Py_TYPE(tstate->current_exception) == (PyTypeObject *)PyExc_ValueError
        ) {
            PyObject *exc = PyErr_GetRaisedException();
            /* Intentionally omitting columns to avoid a wall of 1000s of '^'s
             * on the error message. Nobody is going to overlook their huge
             * numeric literal once given the line. */
            RAISE_ERROR_KNOWN_LOCATION(
                p, PyExc_SyntaxError,
                t->lineno, -1 /* col_offset */,
                t->end_lineno, -1 /* end_col_offset */,
                "%S - Consider hexadecimal for huge integer literals "
                "to avoid decimal conversion limits.",
                exc);
            Py_DECREF(exc);
        }
        return NULL;
    }

    if (_PyArena_AddPyObject(p->arena, c) < 0) {
        Py_DECREF(c);
        p->error_indicator = 1;
        return NULL;
    }

    return _PyAST_Constant(c, NULL, t->lineno, t->col_offset, t->end_lineno,
                           t->end_col_offset, p->arena);
}

/* Check that the source for a single input statement really is a single
   statement by looking at what is left in the buffer after parsing.
   Trailing whitespace and comments are OK. */
static int // bool
bad_single_statement(Parser *p)
{
    char *cur = p->tok->cur;
    char c = *cur;

    for (;;) {
        while (c == ' ' || c == '\t' || c == '\n' || c == '\014') {
            c = *++cur;
        }

        if (!c) {
            return 0;
        }

        if (c != '#') {
            return 1;
        }

        /* Suck up comment. */
        while (c && c != '\n') {
            c = *++cur;
        }
    }
}

static int
compute_parser_flags(PyCompilerFlags *flags)
{
    int parser_flags = 0;
    if (!flags) {
        return 0;
    }
    if (flags->cf_flags & PyCF_DONT_IMPLY_DEDENT) {
        parser_flags |= PyPARSE_DONT_IMPLY_DEDENT;
    }
    if (flags->cf_flags & PyCF_IGNORE_COOKIE) {
        parser_flags |= PyPARSE_IGNORE_COOKIE;
    }
    if (flags->cf_flags & CO_FUTURE_BARRY_AS_BDFL) {
        parser_flags |= PyPARSE_BARRY_AS_BDFL;
    }
    if (flags->cf_flags & PyCF_TYPE_COMMENTS) {
        parser_flags |= PyPARSE_TYPE_COMMENTS;
    }
    if (flags->cf_flags & PyCF_ALLOW_INCOMPLETE_INPUT) {
        parser_flags |= PyPARSE_ALLOW_INCOMPLETE_INPUT;
    }
    if (flags->cf_flags & CO_FUTURE_BRACES) {
        parser_flags |= PyPARSE_BRACES;
    }
    return parser_flags;
}

/* See comments in symtable.c. */
#define COMPILER_STACK_FRAME_SCALE 2

struct template_fixer {
    int recursion_depth;            /* current recursion depth */
    int recursion_limit;            /* recursion limit */

    Parser *p;

    expr_ty template_subs[PY_MAX_TEMPLATE_SUBS];
    int subn;
};

#define POS(NODE) \
    (NODE)->lineno, (NODE)->col_offset, (NODE)->end_lineno, (NODE)->end_col_offset

#define CALL(TYPE, ...) \
    if (!(fix_ ## TYPE)(state, __VA_ARGS__)) { \
        state->recursion_depth--; \
        return 0; \
    }

#define CALL_OPT(TYPE, ARG, ...) \
    if ((ARG) != NULL && !(fix_ ## TYPE)(state, (ARG), __VA_ARGS__)) { \
        state->recursion_depth--; \
        return 0; \
    }

#define CALL_SEQ(TYPE, ARG, ...) { \
    int i; \
    asdl_ ## TYPE ## _seq *seq = (ARG); /* avoid variable capture */ \
    for (i = 0; i < asdl_seq_LEN(seq); i++) { \
        TYPE ## _ty elt = (TYPE ## _ty)asdl_seq_GET(seq, i); \
        if (elt != NULL && !(fix_ ## TYPE)(state, elt, __VA_ARGS__)) { \
            state->recursion_depth--; \
            return 0; \
        } \
    } \
}

static int
fix_inc_subn(struct template_fixer *state,
             int lineno, int col_offset,
             int end_lineno, int end_col_offset)
{
    if (state->subn >= PY_MAX_TEMPLATE_SUBS) {
        RAISE_ERROR_KNOWN_LOCATION(state->p, PyExc_SyntaxError,
                                   lineno, col_offset, end_lineno, end_col_offset,
                                   "composition/comprehension depth exceeded %d",
                                   PY_MAX_TEMPLATE_SUBS);
        return 0;
    }

    /* Ensure that the data isn't garbage. */
    state->template_subs[state->subn++] = NULL;
    return 1;
}

#define INC_SUBN(NODE) fix_inc_subn(state, POS(NODE))

static int
fix_dec_subn(struct template_fixer *state, int has_last,
             int lineno, int col_offset,
             int end_lineno, int end_col_offset)
{
    if (state->subn <= 0) {
        RAISE_ERROR_KNOWN_LOCATION(state->p, PyExc_SyntaxError,
                                   lineno, col_offset, end_lineno, end_col_offset,
                                   "composition/comprehension depth underflow");
        return 0;
    }

    state->subn--;
    if (has_last) {
        expr_ty sub = state->template_subs[state->subn];
        if (sub) {
            assert(sub->kind == Template_kind);
            sub->v.Template.last = 1;
        }
    }
    return 1;
}

#define DEC_SUBN(NODE, HASLAST) fix_dec_subn(state, (HASLAST), POS(NODE))

static int fix_expr(struct template_fixer *, expr_ty);
static int fix_stmt(struct template_fixer *, stmt_ty);

static int
fix_arg(struct template_fixer *state, arg_ty node_)
{
    CALL_OPT(expr, node_->annotation);
    return 1;
}

static int
fix_arguments(struct template_fixer *state, arguments_ty node_)
{
    CALL_SEQ(arg, node_->posonlyargs);
    CALL_SEQ(arg, node_->args);
    CALL_OPT(arg, node_->vararg);
    CALL_SEQ(arg, node_->kwonlyargs);
    CALL_SEQ(expr, node_->kw_defaults);
    CALL_OPT(arg, node_->kwarg);
    CALL_SEQ(expr, node_->defaults);
    return 1;
}

static int
fix_comprehension(struct template_fixer *state, comprehension_ty node_)
{
    CALL(expr, node_->target);
    CALL(expr, node_->iter);
    CALL_SEQ(expr, node_->ifs);
    return 1;
}

static int
fix_keyword(struct template_fixer *state, keyword_ty node_)
{
    CALL_OPT(expr, node_->value);
    return 1;
}

static int
fix_expr(struct template_fixer *state, expr_ty node_)
{
    if (++state->recursion_depth > state->recursion_limit) {
        PyErr_SetString(PyExc_RecursionError,
                        "maximum recursion depth exceeded during compilation");
        return 0;
    }

    switch (node_->kind) {
    case BoolOp_kind:
        CALL_SEQ(expr, node_->v.BoolOp.values);
        break;
    case BinOp_kind:
        CALL(expr, node_->v.BinOp.left);
        CALL(expr, node_->v.BinOp.right);
        break;
    case UnaryOp_kind:
        CALL(expr, node_->v.UnaryOp.operand);
        break;
    case Lambda_kind:
        CALL(arguments, node_->v.Lambda.args);
        CALL(expr, node_->v.Lambda.body);
        break;
    case IfExp_kind:
        CALL(expr, node_->v.IfExp.test);
        CALL(expr, node_->v.IfExp.body);
        CALL(expr, node_->v.IfExp.orelse);
        break;
    case Dict_kind:
        CALL_SEQ(expr, node_->v.Dict.keys);
        CALL_SEQ(expr, node_->v.Dict.values);
        break;
    case Set_kind:
        CALL_SEQ(expr, node_->v.Set.elts);
        break;
    case ListComp_kind:
        INC_SUBN(node_);
        CALL(expr, node_->v.ListComp.elt);
        CALL_SEQ(comprehension, node_->v.ListComp.generators);
        DEC_SUBN(node_, 0);
        break;
    case TupleComp_kind:
        INC_SUBN(node_);
        CALL(expr, node_->v.TupleComp.elt);
        CALL_SEQ(comprehension, node_->v.TupleComp.generators);
        DEC_SUBN(node_, 0);
        break;
    case SetComp_kind:
        INC_SUBN(node_);
        CALL(expr, node_->v.SetComp.elt);
        CALL_SEQ(comprehension, node_->v.SetComp.generators);
        DEC_SUBN(node_, 0);
        break;
    case DictComp_kind:
        INC_SUBN(node_);
        CALL_OPT(expr, node_->v.DictComp.key);
        CALL(expr, node_->v.DictComp.value);
        CALL_SEQ(comprehension, node_->v.DictComp.generators);
        DEC_SUBN(node_, 0);
        break;
    case GeneratorExp_kind:
        CALL(expr, node_->v.GeneratorExp.elt);
        CALL_SEQ(comprehension, node_->v.GeneratorExp.generators);
        break;
    case Await_kind:
        CALL(expr, node_->v.Await.value);
        break;
    case Yield_kind:
        CALL_OPT(expr, node_->v.Yield.value);
        break;
    case YieldFrom_kind:
        CALL(expr, node_->v.YieldFrom.value);
        break;
    case Compare_kind:
        CALL(expr, node_->v.Compare.left);
        CALL_SEQ(expr, node_->v.Compare.comparators);
        break;
    case Call_kind:
        CALL(expr, node_->v.Call.func);
        CALL_SEQ(expr, node_->v.Call.args);
        CALL_SEQ(keyword, node_->v.Call.keywords);
        break;
    case FormattedValue_kind:
        CALL(expr, node_->v.FormattedValue.value);
        CALL_OPT(expr, node_->v.FormattedValue.format_spec);
        break;
    case JoinedStr_kind:
        CALL_SEQ(expr, node_->v.JoinedStr.values);
        break;
    case Attribute_kind:
        CALL(expr, node_->v.Attribute.value);
        break;
    case Subscript_kind:
        CALL(expr, node_->v.Subscript.value);
        CALL(expr, node_->v.Subscript.slice);
        break;
    case Starred_kind:
        CALL(expr, node_->v.Starred.value);
        break;
    case Slice_kind:
        CALL_OPT(expr, node_->v.Slice.lower);
        CALL_OPT(expr, node_->v.Slice.upper);
        CALL_OPT(expr, node_->v.Slice.step);
        break;
    case List_kind:
        CALL_SEQ(expr, node_->v.List.elts);
        break;
    case Tuple_kind:
        CALL_SEQ(expr, node_->v.Tuple.elts);
        break;
    case NamedExpr_kind:
        CALL(expr, node_->v.NamedExpr.value);
        break;
    case Composition_kind:
        CALL(expr, node_->v.Composition.arg);
        INC_SUBN(node_);
        CALL(expr, node_->v.Composition.func);
        DEC_SUBN(node_, 1);
        if (state->template_subs[state->subn]) {
            node_->v.Composition.has_templates = 1;
            if (node_->v.Composition.aware) {
                RAISE_ERROR_KNOWN_LOCATION(
                    state->p, PyExc_SyntaxError, POS(node_),
                    "cannot have none-aware templated pipe"
                );
                return 0;
            }
        }
        break;
    case CompoundExpr_kind:
        CALL(stmt, node_->v.CompoundExpr.value);
        break;
    case BlockExpr_kind:
        CALL_SEQ(stmt, node_->v.BlockExpr.body);
        break;
    case ExprTarget_kind:
        CALL(expr, node_->v.ExprTarget.value);
        break;
    case Template_kind:
        if (node_->v.Template.level >= state->subn) {
            RAISE_ERROR_KNOWN_LOCATION(state->p, PyExc_SyntaxError, POS(node_),
                                       "template index out of range");
            return 0;
        }
        state->template_subs[state->subn - node_->v.Template.level - 1] = node_;
        break;
    case Name_kind:
    case Constant_kind:
        // nothing further to do
        break;
    // No default case, so the compiler will emit a warning if new expression
    // kinds are added without being handled here
    }

    state->recursion_depth--;
    return 1;
}

static int
fix_type_param(struct template_fixer *state, type_param_ty node_)
{
    switch (node_->kind) {
        case TypeVar_kind:
            CALL_OPT(expr, node_->v.TypeVar.bound);
            break;
        case ParamSpec_kind:
        case TypeVarTuple_kind:
            break;
    }
    return 1;
}

static int
fix_withitem(struct template_fixer *state, withitem_ty node_)
{
    CALL(expr, node_->context_expr);
    CALL_OPT(expr, node_->optional_vars);
    return 1;
}

static int
fix_excepthandler(struct template_fixer *state, excepthandler_ty node_)
{
    switch (node_->kind) {
    case ExceptHandler_kind:
        CALL_OPT(expr, node_->v.ExceptHandler.type);
        CALL_SEQ(stmt, node_->v.ExceptHandler.body);
        break;
    // No default case, so the compiler will emit a warning if new handler
    // kinds are added without being handled here
    }
    return 1;
}

static int
fix_pattern(struct template_fixer *state, pattern_ty node_)
{
    // Currently, this is really only used to form complex/negative numeric
    // constants in MatchValue and MatchMapping nodes
    // We still recurse into all subexpressions and subpatterns anyway
    if (++state->recursion_depth > state->recursion_limit) {
        PyErr_SetString(PyExc_RecursionError,
                        "maximum recursion depth exceeded during compilation");
        return 0;
    }

    switch (node_->kind) {
        case MatchValue_kind:
            CALL(expr, node_->v.MatchValue.value);
            break;
        case MatchSingleton_kind:
            break;
        case MatchSequence_kind:
            CALL_SEQ(pattern, node_->v.MatchSequence.patterns);
            break;
        case MatchMapping_kind:
            CALL_SEQ(expr, node_->v.MatchMapping.keys);
            CALL_SEQ(pattern, node_->v.MatchMapping.patterns);
            break;
        case MatchClass_kind:
            CALL(expr, node_->v.MatchClass.cls);
            CALL_SEQ(pattern, node_->v.MatchClass.patterns);
            CALL_SEQ(pattern, node_->v.MatchClass.kwd_patterns);
            break;
        case MatchStar_kind:
            break;
        case MatchAs_kind:
            CALL_OPT(pattern, node_->v.MatchAs.pattern);
            break;
        case MatchOr_kind:
            CALL_SEQ(pattern, node_->v.MatchOr.patterns);
            break;
    // No default case, so the compiler will emit a warning if new pattern
    // kinds are added without being handled here
    }

    state->recursion_depth--;
    return 1;
}

static int
fix_match_case(struct template_fixer *state, match_case_ty node_)
{
    CALL(pattern, node_->pattern);
    CALL_OPT(expr, node_->guard);
    CALL_SEQ(stmt, node_->body);
    return 1;
}

static int
fix_stmt(struct template_fixer *state, stmt_ty node_)
{
    if (++state->recursion_depth > state->recursion_limit) {
        PyErr_SetString(PyExc_RecursionError,
                        "maximum recursion depth exceeded during compilation");
        return 0;
    }

    switch (node_->kind) {
    case FunctionDef_kind:
        CALL_SEQ(type_param, node_->v.FunctionDef.type_params);
        CALL(arguments, node_->v.FunctionDef.args);
        CALL_SEQ(stmt, node_->v.FunctionDef.body);
        CALL_SEQ(expr, node_->v.FunctionDef.decorator_list);
        CALL_OPT(expr, node_->v.FunctionDef.returns);
        break;
    case AsyncFunctionDef_kind:
        CALL_SEQ(type_param, node_->v.AsyncFunctionDef.type_params);
        CALL(arguments, node_->v.AsyncFunctionDef.args);
        CALL_SEQ(stmt, node_->v.AsyncFunctionDef.body);
        CALL_SEQ(expr, node_->v.AsyncFunctionDef.decorator_list);
        CALL_OPT(expr, node_->v.AsyncFunctionDef.returns);
        break;
    case ClassDef_kind:
        CALL_SEQ(type_param, node_->v.ClassDef.type_params);
        CALL_SEQ(expr, node_->v.ClassDef.bases);
        CALL_SEQ(keyword, node_->v.ClassDef.keywords);
        CALL_SEQ(stmt, node_->v.ClassDef.body);
        CALL_SEQ(expr, node_->v.ClassDef.decorator_list);
        break;
    case Return_kind:
        CALL_OPT(expr, node_->v.Return.value);
        break;
    case Delete_kind:
        CALL_SEQ(expr, node_->v.Delete.targets);
        break;
    case Assign_kind:
        CALL_SEQ(expr, node_->v.Assign.targets);
        CALL(expr, node_->v.Assign.value);
        break;
    case AugAssign_kind:
        CALL(expr, node_->v.AugAssign.target);
        CALL_OPT(expr, node_->v.AugAssign.value);
        break;
    case AnnAssign_kind:
        CALL(expr, node_->v.AnnAssign.target);
        CALL(expr, node_->v.AnnAssign.annotation);
        CALL_OPT(expr, node_->v.AnnAssign.value);
        break;
    case TypeAlias_kind:
        CALL(expr, node_->v.TypeAlias.name);
        CALL_SEQ(type_param, node_->v.TypeAlias.type_params);
        CALL(expr, node_->v.TypeAlias.value);
        break;
    case For_kind:
        CALL(expr, node_->v.For.target);
        CALL(expr, node_->v.For.iter);
        CALL_SEQ(stmt, node_->v.For.body);
        CALL_SEQ(stmt, node_->v.For.orelse);
        break;
    case AsyncFor_kind:
        CALL(expr, node_->v.AsyncFor.target);
        CALL(expr, node_->v.AsyncFor.iter);
        CALL_SEQ(stmt, node_->v.AsyncFor.body);
        CALL_SEQ(stmt, node_->v.AsyncFor.orelse);
        break;
    case While_kind:
        CALL(expr, node_->v.While.test);
        CALL_SEQ(stmt, node_->v.While.body);
        CALL_SEQ(stmt, node_->v.While.orelse);
        break;
    case If_kind:
        CALL(expr, node_->v.If.test);
        CALL_SEQ(stmt, node_->v.If.body);
        CALL_SEQ(stmt, node_->v.If.orelse);
        break;
    case With_kind:
        CALL_SEQ(withitem, node_->v.With.items);
        CALL_SEQ(stmt, node_->v.With.body);
        break;
    case AsyncWith_kind:
        CALL_SEQ(withitem, node_->v.AsyncWith.items);
        CALL_SEQ(stmt, node_->v.AsyncWith.body);
        break;
    case Raise_kind:
        CALL_OPT(expr, node_->v.Raise.exc);
        CALL_OPT(expr, node_->v.Raise.cause);
        break;
    case Try_kind:
        CALL_SEQ(stmt, node_->v.Try.body);
        CALL_SEQ(excepthandler, node_->v.Try.handlers);
        CALL_SEQ(stmt, node_->v.Try.orelse);
        CALL_SEQ(stmt, node_->v.Try.finalbody);
        break;
    case TryStar_kind:
        CALL_SEQ(stmt, node_->v.TryStar.body);
        CALL_SEQ(excepthandler, node_->v.TryStar.handlers);
        CALL_SEQ(stmt, node_->v.TryStar.orelse);
        CALL_SEQ(stmt, node_->v.TryStar.finalbody);
        break;
    case Assert_kind:
        CALL(expr, node_->v.Assert.test);
        CALL_OPT(expr, node_->v.Assert.msg);
        break;
    case Expr_kind:
        CALL(expr, node_->v.Expr.value);
        break;
    case Switch_kind:
        // TODO: switch case
        break;
    case Match_kind:
        CALL(expr, node_->v.Match.subject);
        CALL_SEQ(match_case, node_->v.Match.cases);
        break;
    // The following statements don't contain any subexpressions to be checked
    case Import_kind:
    case ImportFrom_kind:
    case Global_kind:
    case Nonlocal_kind:
    case Goto_kind:
    case Label_kind:
    case Pass_kind:
    case Break_kind:
    case Continue_kind:
        break;
    // No default case, so the compiler will emit a warning if new statement
    // kinds are added without being handled here
    }

    state->recursion_depth--;
    return 1;
}

static int
fix_mod(struct template_fixer *state, mod_ty node_)
{
    if (++state->recursion_depth > state->recursion_limit) {
        PyErr_SetString(PyExc_RecursionError,
                        "maximum recursion depth exceeded during compilation");
        return 0;
    }

    switch (node_->kind) {
    case Module_kind:
        CALL_SEQ(stmt, node_->v.Module.body);
        break;
    case Interactive_kind:
        CALL_SEQ(stmt, node_->v.Interactive.body);
        break;
    case Expression_kind:
        CALL(expr, node_->v.Expression.body);
        break;
    case FunctionType_kind:
        CALL_SEQ(expr, node_->v.FunctionType.argtypes);
        CALL(expr, node_->v.FunctionType.returns);
        break;
    // No default case so compiler emits warning for unhandled cases
    }

    state->recursion_depth--;
    return 1;
}

#undef POS
#undef CALL
#undef CALL_OPT
#undef CALL_SEQ

int
_PyPegen_fix_templates(Parser *p, mod_ty mod)
{
    struct template_fixer state;
    PyThreadState *tstate;
    int starting_recursion_depth;

    /* Setup recursion depth check counters */
    tstate = _PyThreadState_GET();
    if (!tstate) {
        return 0;
    }
    /* Be careful here to prevent overflow. */
    int recursion_depth = C_RECURSION_LIMIT - tstate->c_recursion_remaining;
    starting_recursion_depth = recursion_depth * COMPILER_STACK_FRAME_SCALE;
    state.recursion_depth = starting_recursion_depth;
    state.recursion_limit = C_RECURSION_LIMIT * COMPILER_STACK_FRAME_SCALE;
    state.p = p;
    state.subn = 0;

    int res = fix_mod(&state, mod);

    assert(state.subn == 0);

    /* Check that the recursion depth counting balanced correctly */
    if (res && state.recursion_depth != starting_recursion_depth) {
        PyErr_Format(PyExc_SystemError,
            "AST validator recursion depth mismatch (before=%d, after=%d)",
            starting_recursion_depth, state.recursion_depth);
        return 0;
    }

    return res;
}

// Parser API

Parser *
_PyPegen_Parser_New(struct tok_state *tok, int start_rule, int flags,
                    int *restricted, int *restrici, int feature_version,
                    int *errcode, PyArena *arena)
{
    Parser *p = PyMem_Malloc(sizeof(Parser));
    if (p == NULL) {
        return (Parser *) PyErr_NoMemory();
    }
    assert(tok != NULL);
    tok->type_comments = (flags & PyPARSE_TYPE_COMMENTS) > 0;
    p->tok = tok;
    p->keywords = NULL;
    p->n_keyword_lists = -1;
    p->soft_keywords = NULL;
    p->tokens = PyMem_Malloc(sizeof(Token *));
    if (!p->tokens) {
        PyMem_Free(p);
        return (Parser *) PyErr_NoMemory();
    }
    p->tokens[0] = PyMem_Calloc(1, sizeof(Token));
    if (!p->tokens[0]) {
        PyMem_Free(p->tokens);
        PyMem_Free(p);
        return (Parser *) PyErr_NoMemory();
    }
    if (!growable_comment_array_init(&p->type_ignore_comments, 10)) {
        PyMem_Free(p->tokens[0]);
        PyMem_Free(p->tokens);
        PyMem_Free(p);
        return (Parser *) PyErr_NoMemory();
    }

    p->mark = 0;
    p->fill = 0;
    p->size = 1;

    p->errcode = errcode;
    p->arena = arena;
    p->start_rule = start_rule;
    p->parsing_started = 0;
    p->normalize = NULL;
    p->error_indicator = 0;

    p->starting_lineno = 0;
    p->starting_col_offset = 0;
    p->flags = flags;
    p->feature_version = feature_version;
    p->known_err_token = NULL;
    p->level = 0;
    p->call_invalid_rules = 0;
    if (restrici == NULL) {
        restrici = PyMem_Calloc(1, sizeof(int));
        p->ialloc = 1;
    }
    else {
        p->ialloc = 0;
    }
    if (restricted == NULL) {
        restricted = PyMem_Calloc(35, sizeof(int));
        if (restricted == NULL) {
            PyMem_Free(p->type_ignore_comments.items);
            PyMem_Free(p->tokens[0]);
            PyMem_Free(p->tokens);
            PyMem_Free(p);
            return (Parser *) PyErr_NoMemory();
        }
        *restrici = 0;
        p->edalloc = 1;
    }
    else {
        p->edalloc = 0;
    }
    p->restricted = restricted;
    p->restrici = restrici;
#ifdef Py_DEBUG
    p->debug = _Py_GetConfig()->parser_debug;
#endif
    return p;
}

void
_PyPegen_Parser_Free(Parser *p)
{
    Py_XDECREF(p->normalize);
    for (int i = 0; i < p->size; i++) {
        PyMem_Free(p->tokens[i]);
    }
    PyMem_Free(p->tokens);
    growable_comment_array_deallocate(&p->type_ignore_comments);
    PyMem_Free(p);
}

static void
reset_parser_state_for_error_pass(Parser *p)
{
    for (int i = 0; i < p->fill; i++) {
        p->tokens[i]->memo = NULL;
    }
    p->mark = 0;
    p->call_invalid_rules = 1;
    // Don't try to get extra tokens in interactive mode when trying to
    // raise specialized errors in the second pass.
    p->tok->interactive_underflow = IUNDERFLOW_STOP;
}

static inline int
_is_end_of_source(Parser *p) {
    int err = p->tok->done;
    return err == E_EOF || err == E_EOFS || err == E_EOLS;
}

void *
_PyPegen_run_parser(Parser *p)
{
    void *res = _PyPegen_parse(p);
    assert(p->level == 0);
    if (res == NULL) {
        if ((p->flags & PyPARSE_ALLOW_INCOMPLETE_INPUT) &&  _is_end_of_source(p)) {
            PyErr_Clear();
            return RAISE_SYNTAX_ERROR("incomplete input");
        }
        if (PyErr_Occurred() && !PyErr_ExceptionMatches(PyExc_SyntaxError)) {
            return NULL;
        }
       // Make a second parser pass. In this pass we activate heavier and slower checks
        // to produce better error messages and more complete diagnostics. Extra "invalid_*"
        // rules will be active during parsing.
        Token *last_token = p->tokens[p->fill - 1];
        reset_parser_state_for_error_pass(p);
        _PyPegen_parse(p);

        // Set SyntaxErrors accordingly depending on the parser/tokenizer status at the failure
        // point.
        _Pypegen_set_syntax_error(p, last_token);
       return NULL;
    }

    if (p->start_rule == Py_single_input && bad_single_statement(p)) {
        p->tok->done = E_BADSINGLE; // This is not necessary for now, but might be in the future
        return RAISE_SYNTAX_ERROR("multiple statements found while compiling a single statement");
    }

    // test_peg_generator defines _Py_TEST_PEGEN to not call PyAST_Validate()
#if defined(Py_DEBUG) && !defined(_Py_TEST_PEGEN)
    if (p->start_rule == Py_single_input ||
        p->start_rule == Py_file_input ||
        p->start_rule == Py_eval_input)
    {
        if (!_PyAST_Validate(res)) {
            return NULL;
        }
    }
#endif

    return res;
}

mod_ty
_PyPegen_run_parser_from_file_pointer(FILE *fp, int start_rule, PyObject *filename_ob,
                             const char *enc, const char *ps1, const char *ps2,
                             PyCompilerFlags *flags, int *restricted, int *restrici,
                             int *errcode, PyArena *arena)
{
    struct tok_state *tok = _PyTokenizer_FromFile(fp, enc, ps1, ps2);
    if (tok == NULL) {
        if (PyErr_Occurred()) {
            _PyPegen_raise_tokenizer_init_error(filename_ob);
            return NULL;
        }
        return NULL;
    }
    if (!tok->fp || ps1 != NULL || ps2 != NULL ||
        PyUnicode_CompareWithASCIIString(filename_ob, "<stdin>") == 0) {
        tok->fp_interactive = 1;
    }
    // This transfers the ownership to the tokenizer
    tok->filename = Py_NewRef(filename_ob);

    // From here on we need to clean up even if there's an error
    mod_ty result = NULL;

    int parser_flags = compute_parser_flags(flags);
    Parser *p = _PyPegen_Parser_New(tok, start_rule, parser_flags, restricted,
                                    restrici, PY_MINOR_VERSION, errcode, arena);
    if (p == NULL) {
        goto error;
    }

    result = _PyPegen_run_parser(p);
    _PyPegen_Parser_Free(p);

error:
    _PyTokenizer_Free(tok);
    return result;
}

mod_ty
_PyPegen_run_parser_from_string(const char *str, int start_rule, PyObject *filename_ob,
                       PyCompilerFlags *flags, PyArena *arena)
{
    int exec_input = start_rule == Py_file_input;

    struct tok_state *tok;
    if (flags != NULL && flags->cf_flags & PyCF_IGNORE_COOKIE) {
        tok = _PyTokenizer_FromUTF8(str, exec_input, 0);
    } else {
        tok = _PyTokenizer_FromString(str, exec_input, 0);
    }
    if (tok == NULL) {
        if (PyErr_Occurred()) {
            _PyPegen_raise_tokenizer_init_error(filename_ob);
        }
        return NULL;
    }
    // This transfers the ownership to the tokenizer
    tok->filename = Py_NewRef(filename_ob);

    // We need to clear up from here on
    mod_ty result = NULL;

    int parser_flags = compute_parser_flags(flags);
    int feature_version = flags && (flags->cf_flags & PyCF_ONLY_AST) ?
        flags->cf_feature_version : PY_MINOR_VERSION;
    Parser *p = _PyPegen_Parser_New(tok, start_rule, parser_flags, NULL, NULL,
                                    feature_version, NULL, arena);
    if (p == NULL) {
        goto error;
    }

    result = _PyPegen_run_parser(p);
    _PyPegen_Parser_Free(p);

error:
    _PyTokenizer_Free(tok);
    return result;
}

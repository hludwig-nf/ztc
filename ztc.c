#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>
#include <errno.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <signal.h>
#include <math.h>
#include <stdint.h>

#include <sys/utsname.h>
#include <dlfcn.h>

#include <openssl/sha.h>

#define ZTC_VERSION     "0.26"   /* ztc itself; understands both language versions */
#define ZTC_VERSION_P26 "0.1"    /* ztc as seen by -ztv=p26 */

/* -ztv=p26    -> ZTSL p26   (ztc 0.1, original syntax, default)
 * -ztv=ztsl26 -> ZTSL 26    (ztc 0.26, def_mod / run.func / argument guards) */
typedef enum { ZTV_P26, ZTV_ZTSL26 } ZtVer;
static ZtVer g_ztv    = ZTV_P26;
static bool  g_memchk = false;   /* -libmemchk (built in) */

static void *xmalloc(size_t n) {
    void *p = malloc(n);
    if (!p) {
        fprintf(stderr, "E: out of memory (requested %zu bytes)\n", n);
        exit(EXIT_FAILURE);
    }
    return p;
}

static char *xstrdup(const char *s) {
    char *p = strdup(s);
    if (!p) {
        fprintf(stderr, "E: out of memory (strdup)\n");
        exit(EXIT_FAILURE);
    }
    return p;
}

static char *xstrndup(const char *s, size_t n) {
    char *p = strndup(s, n);
    if (!p) {
        fprintf(stderr, "E: out of memory (strndup)\n");
        exit(EXIT_FAILURE);
    }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n);
    if (!q) {
        fprintf(stderr, "E: out of memory (realloc %zu)\n", n);
        exit(EXIT_FAILURE);
    }
    return q;
}

static void zt_warn(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("W: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
}

static void zt_error(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("E: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
}

static int levenshtein(const char *a, const char *b) {
    size_t la = strlen(a), lb = strlen(b);
    if (la == 0) return (int)lb;
    if (lb == 0) return (int)la;
    int *prev = xmalloc(sizeof(int) * (lb + 1));
    int *curr = xmalloc(sizeof(int) * (lb + 1));
    for (size_t j = 0; j <= lb; j++) prev[j] = (int)j;
    for (size_t i = 1; i <= la; i++) {
        curr[0] = (int)i;
        for (size_t j = 1; j <= lb; j++) {
            int cost = (tolower((unsigned char)a[i-1]) ==
                        tolower((unsigned char)b[j-1])) ? 0 : 1;
            int del = prev[j] + 1;
            int ins = curr[j-1] + 1;
            int sub = prev[j-1] + cost;
            int m = del < ins ? del : ins;
            curr[j] = m < sub ? m : sub;
        }
        int *tmp = prev; prev = curr; curr = tmp;
    }
    int d = prev[lb];
    free(prev);
    free(curr);
    return d;
}

static const char *suggest_keyword(const char *word) {
    static const char *keywords[] = {
        "ztsl.start", "ztsl.end",
        "ztslo.start", "ztslo.end",
        "define", "variable", "as",
        "if", "then", "else", "or", "is", "not",
        "func", "sys.exec", "text.show",
        "shell", "exec",
        "empty", "file", "returns",
        "read_file", "delete_file", "create_file",
        "write_on_file", "append_file", "ccompat",
        "calculate",
        "def_mod", "run.func", "sys.exec.silent", "endif",
        "mem.alloc", "mem.free", "mem.write", "mem.show",
        NULL
    };
    size_t wlen = 0;
    while (word[wlen] && !isspace((unsigned char)word[wlen]) &&
           word[wlen] != '"' && word[wlen] != '(') {
        wlen++;
    }
    if (wlen == 0) return NULL;
    char *first = xstrndup(word, wlen);
    int best_d = 1000;
    const char *best = NULL;
    for (size_t i = 0; keywords[i]; i++) {
        int d = levenshtein(first, keywords[i]);
        if (d < best_d) { best_d = d; best = keywords[i]; }
    }
    free(first);
    if (best_d <= 2) return best;
    return NULL;
}

static char *str_trim(char *s) {
    if (!s) return NULL;
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s == '\0') return s;
    char *end = s + strlen(s) - 1;
    while (end > s && isspace((unsigned char)*end)) {
        *end = '\0';
        end--;
    }
    return s;
}

static char *str_trim_dup(const char *s) {
    char *dup = xstrdup(s);
    char *t = str_trim(dup);
    if (t != dup) memmove(dup, t, strlen(t) + 1);
    return dup;
}

typedef struct {
    char  *data;
    size_t len;
    size_t cap;
} dstring;

static void dstr_init(dstring *d) {
    d->cap = 64;
    d->len = 0;
    d->data = xmalloc(d->cap);
    d->data[0] = '\0';
}

static void dstr_free(dstring *d) {
    free(d->data);
    d->data = NULL;
    d->len = d->cap = 0;
}

static void dstr_reserve(dstring *d, size_t need) {
    if (d->cap >= need + 1) return;
    while (d->cap < need + 1) d->cap *= 2;
    d->data = xrealloc(d->data, d->cap);
}

static void dstr_append(dstring *d, const char *s, size_t n) {
    dstr_reserve(d, d->len + n);
    memcpy(d->data + d->len, s, n);
    d->len += n;
    d->data[d->len] = '\0';
}

static void dstr_append_cstr(dstring *d, const char *s) {
    dstr_append(d, s, strlen(s));
}

static void dstr_append_char(dstring *d, char c) {
    dstr_reserve(d, d->len + 1);
    d->data[d->len++] = c;
    d->data[d->len] = '\0';
}

static void dstr_appendf(dstring *d, const char *fmt, ...) {
    va_list ap, ap2;
    va_start(ap, fmt);
    va_copy(ap2, ap);
    int n = vsnprintf(NULL, 0, fmt, ap);
    va_end(ap);
    if (n >= 0) {
        dstr_reserve(d, d->len + (size_t)n);
        vsnprintf(d->data + d->len, (size_t)n + 1, fmt, ap2);
        d->len += (size_t)n;
    }
    va_end(ap2);
}

typedef struct {
    char **lines;
    size_t count;
} LineBuf;

static void linebuf_init(LineBuf *lb) {
    lb->lines = NULL;
    lb->count = 0;
}

static void linebuf_free(LineBuf *lb) {
    for (size_t i = 0; i < lb->count; i++) {
        
        if (lb->lines[i]) free(lb->lines[i]);
    }
    free(lb->lines);
    lb->lines = NULL;
    lb->count = 0;
}

static void linebuf_push(LineBuf *lb, char *line) {
    
    lb->lines = xrealloc(lb->lines, sizeof(char *) * (lb->count + 1));
    lb->lines[lb->count++] = line;
}

static char *read_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return NULL; }
    long sz = ftell(f);
    if (sz < 0) { fclose(f); return NULL; }
    rewind(f);
    char *buf = xmalloc((size_t)sz + 1);
    size_t got = fread(buf, 1, (size_t)sz, f);
    fclose(f);
    buf[got] = '\0';
    return buf;
}

static void file_to_lines(const char *content, LineBuf *lb) {
    bool in_code_fence = false;
    const char *p = content;
    dstring cur;
    dstr_init(&cur);

    while (*p) {
        
        if (!in_code_fence && *p == '#') {
            
            while (*p && *p != '\n') p++;
            continue;
        }

        
        if (*p == '`' && p[1] == '`' && p[2] == '`') {
            in_code_fence = !in_code_fence;
            
            dstr_append_cstr(&cur, "```");
            p += 3;
            continue;
        }

        if (*p == '\n') {
            /* Inside a ``` block the body is kept verbatim (indentation and
             * blank lines survive: text.show / write_on_file used to lose
             * both). The fence lines themselves are still trimmed. */
            const char *t = cur.data;
            while (*t && isspace((unsigned char)*t)) t++;
            bool fence_line = (strncmp(t, "```", 3) == 0);
            char *line;
            if (in_code_fence && !fence_line) {
                line = xstrdup(cur.data);
                size_t ll = strlen(line);
                while (ll > 0 && line[ll - 1] == '\r') line[--ll] = '\0';
                linebuf_push(lb, line);
            } else {
                line = str_trim_dup(cur.data);
                if (line[0] != '\0') linebuf_push(lb, line);
                else free(line);
            }
            dstr_free(&cur);
            dstr_init(&cur);
            p++;
            continue;
        }

        dstr_append_char(&cur, *p);
        p++;
    }

    
    if (cur.len > 0) {
        char *line = str_trim_dup(cur.data);
        if (line[0] != '\0') linebuf_push(lb, line);
        else free(line);
    }
    dstr_free(&cur);
}

typedef enum {
    K_DEFINE,
    K_IF,
    K_EXEC,
    K_SHOW,
    K_DELETE,
    K_CREATE,
    K_WRITE,
    K_APPEND,
    K_CCOMPAT,
    K_FLOATCALC,
    K_RUNFUNC,
    K_MEMALLOC,
    K_MEMFREE,
    K_MEMWRITE,
    K_MEMSHOW,
    K_LIBCALL,
} StmtKind;

typedef enum {
    COND_EQ,
    COND_EMPTYFILE,
    COND_ARG_PASSED,   /* if argument NAME is passed [with %ea%] */
    COND_ARG_UNDEF,    /* if argument is not defined */
} CondKind;

typedef enum {
    SUBJ_VAR,
    SUBJ_READFILE,
} CondSubj;

typedef struct Stmt Stmt;

typedef struct {
    

    CondKind kind;
    CondSubj subj;
    char    *var;           
    char    *path;          
    bool     is_is;        
    char   **values;       
    size_t   nvalues;
    char    *argname;      /* COND_ARG_PASSED */
    bool     need_ea;      /* ... with %ea% */
    Stmt    *then_branch;  
    Stmt    *else_branch;
} Cond;

struct Stmt {
    StmtKind  kind;
    Stmt     *next;
    union {
        struct { char *name; char *value; } define;
        Cond     cond;
        struct { bool is_shell; bool silent; char *code; } exec;
        struct { char *code; } show;
        struct { char *path; } delfile;
        struct { char *path; } mkfile;
        struct { char *path; char *code; } writefile;
        struct { char *code; } ccompat;
        struct { int width; char op; char *lhs_raw; char *rhs_raw; char *varname; } floatcalc;
        struct { char *name; } runfunc;
        struct { char *name; char *num; char *text; } mem;
        struct { size_t idx; char **args; int nargs; char *varname; } libcall;
    };
};

typedef struct Func {
    char   *name;
    Stmt   *body;
    struct Func *next;
} Func;

typedef struct Var {
    char   *name;
    char   *value;
    struct Var *next;
} Var;

/* ---- ZTSL module ABI: what a def_mod library exports ----
 *   const ztsl_module ztsl_module_<name> = { 1, "<name>", stmts };
 * 'stmts' ends with { NULL, NULL }. A statement receives its arguments as
 * text and returns 0 (ok) or non-zero (error); '*out' is a string malloc'd by
 * the library (the result, or the error message). */
#define ZTSL_ABI 1
typedef int (*ZtslStmtFn)(int argc, const char *const *argv, char **out);
typedef struct { const char *name; ZtslStmtFn fn; } ZtslStmtEntry;
typedef struct { unsigned abi; const char *name; const ZtslStmtEntry *stmts; } ZtslModule;

typedef struct { char *name; ZtslStmtFn fn; size_t mod; } LibStmt;

typedef struct {
    Func *funcs;
    Var  *vars;
    bool  inline_ztslo_used;
    char **mods;      /* def_mod names (ztsl26) */
    void **modh;      /* dlopen handles, parallel to mods */
    size_t nmods;
    LibStmt *lstmts;  /* statements provided by libraries */
    size_t nlstmts;
} Program;

typedef struct {
    LineBuf *lb;
    size_t   pos;
    bool     error;
    char    *err_msg;
    int      if_depth;   /* nesting of 'if' being parsed */
    Program *prog;       /* for library statements */
} Parser;

static void parse_error(Parser *p, const char *msg) {
    if (!p->error) {
        p->error = true;
        p->err_msg = xstrdup(msg);
    }
}

static const char *peek(Parser *p) {
    while (p->pos < p->lb->count) {
        const char *line = p->lb->lines[p->pos];
        if (line[0] == '\0') { p->pos++; continue; }
        return line;
    }
    return NULL;
}

static char *consume(Parser *p) {
    while (p->pos < p->lb->count) {
        char *line = p->lb->lines[p->pos];
        p->pos++;
        if (line[0] == '\0') { free(line); continue; }
        

        p->lb->lines[p->pos - 1] = NULL;
        return line;
    }
    return NULL;
}

static bool starts_with_kw(const char *line, const char *kw) {
    size_t n = strlen(kw);
    if (strlen(line) < n) return false;
    for (size_t i = 0; i < n; i++) {
        if (tolower((unsigned char)line[i]) != tolower((unsigned char)kw[i]))
            return false;
    }
    char c = line[n];
    if (c == '\0' || isspace((unsigned char)c) || c == ';') return true;
    return false;
}

static char *extract_quoted(const char *s, const char **endp) {
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s != '"') { if (endp) *endp = s; return NULL; }
    s++;
    const char *start = s;
    while (*s && *s != '"') {
        if (*s == '\\' && s[1]) s++;
        s++;
    }
    if (*s != '"') { if (endp) *endp = s; return NULL; }
    char *out = xstrndup(start, (size_t)(s - start));
    s++;
    if (endp) *endp = s;
    return out;
}

static char **split_args(const char *cmd, int *argc_out);
static void free_args(char **argv);

static void stmt_free(Stmt *s) {
    while (s) {
        Stmt *next = s->next;
        switch (s->kind) {
            case K_DEFINE:
                free(s->define.name);
                free(s->define.value);
                break;
            case K_IF:
                free(s->cond.var);
                free(s->cond.path);
                free(s->cond.argname);
                for (size_t i = 0; i < s->cond.nvalues; i++)
                    free(s->cond.values[i]);
                free(s->cond.values);
                stmt_free(s->cond.then_branch);
                stmt_free(s->cond.else_branch);
                break;
            case K_EXEC:
                free(s->exec.code);
                break;
            case K_SHOW:
                free(s->show.code);
                break;
            case K_DELETE:
                free(s->delfile.path);
                break;
            case K_CREATE:
                free(s->mkfile.path);
                break;
            case K_WRITE:
            case K_APPEND:
                free(s->writefile.path);
                free(s->writefile.code);
                break;
            case K_CCOMPAT:
                free(s->ccompat.code);
                break;
            case K_FLOATCALC:
                free(s->floatcalc.lhs_raw);
                free(s->floatcalc.rhs_raw);
                free(s->floatcalc.varname);
                break;
            case K_RUNFUNC:
                free(s->runfunc.name);
                break;
            case K_MEMALLOC:
            case K_MEMFREE:
            case K_MEMWRITE:
            case K_MEMSHOW:
                free(s->mem.name);
                free(s->mem.num);
                free(s->mem.text);
                break;
            case K_LIBCALL:
                free_args(s->libcall.args);
                free(s->libcall.varname);
                break;
        }
        free(s);
        s = next;
    }
}

static void func_free(Func *f) {
    while (f) {
        Func *next = f->next;
        free(f->name);
        stmt_free(f->body);
        free(f);
        f = next;
    }
}

static void var_free(Var *v) {
    while (v) {
        Var *next = v->next;
        free(v->name);
        free(v->value);
        free(v);
        v = next;
    }
}

static char *parse_code_block(Parser *p, bool *is_shell, bool allow_tags) {
    char *line = consume(p);
    if (!line) {
        parse_error(p, "expected code block, got EOF");
        return NULL;
    }
    
    if (strncmp(line, "```", 3) != 0) {
        parse_error(p, "expected ``` to open code block");
        free(line);
        return NULL;
    }
    const char *tag = line + 3;
    while (*tag && isspace((unsigned char)*tag)) tag++;
    if (tag[0] == '\0') {
        
        *is_shell = true;
    } else if (!allow_tags) {
        
        zt_error("text.show does not accept shell/exec tags; use bare ```");
        free(line);
        parse_error(p, "text.show with forbidden tag");
        return NULL;
    } else if (strcmp(tag, "shell") == 0) {
        *is_shell = true;
    } else if (strcmp(tag, "exec") == 0) {
        *is_shell = false;
    } else {
        zt_error("unknown code fence tag '%s' (expected shell/exec)", tag);
        free(line);
        parse_error(p, "unknown code fence tag");
        return NULL;
    }
    free(line);

    dstring code;
    dstr_init(&code);

    while (p->pos < p->lb->count) {
        char *l = p->lb->lines[p->pos];
        if (strcmp(l, "```") == 0) {
            
            p->lb->lines[p->pos] = NULL;
            p->pos++;
            free(l);
            return code.data;
        }
        dstr_append_cstr(&code, l);
        dstr_append_char(&code, '\n');
        p->pos++;
    }

    dstr_free(&code);
    parse_error(p, "unterminated code block (missing closing ```)");
    return NULL;
}

static char *parse_raw_block(Parser *p) {
    char *line = consume(p);
    if (!line) {
        parse_error(p, "expected code block, got EOF");
        return NULL;
    }
    if (strncmp(line, "```", 3) != 0) {
        parse_error(p, "expected ``` to open code block");
        free(line);
        return NULL;
    }
    free(line);

    dstring code;
    dstr_init(&code);

    while (p->pos < p->lb->count) {
        char *l = p->lb->lines[p->pos];
        if (strcmp(l, "```") == 0) {
            p->lb->lines[p->pos] = NULL;
            p->pos++;
            free(l);
            return code.data;
        }
        dstr_append_cstr(&code, l);
        dstr_append_char(&code, '\n');
        p->pos++;
    }

    dstr_free(&code);
    parse_error(p, "unterminated code block (missing closing ```)");
    return NULL;
}

static Stmt *parse_stmt(Parser *p);
static Stmt *parse_stmt_list(Parser *p, const char *terminator);

static Stmt *parse_define(Parser *p, char *first_line) {
    (void)first_line;
    char *line = consume(p);
    if (!line) { parse_error(p, "EOF in define"); return NULL; }

    

    char *save = line;

    char *cursor = save;
    
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    
    char *var_kw = cursor;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    if (*cursor) { *cursor++ = '\0'; }
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    if (var_kw[0] == '\0' || strcasecmp(var_kw, "variable") != 0) {
        parse_error(p, "expected 'variable' after 'define'");
        free(save);
        return NULL;
    }
    
    char *name = cursor;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    if (*cursor) *cursor++ = '\0';
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    if (name[0] == '\0') {
        parse_error(p, "expected variable name");
        free(save);
        return NULL;
    }
    
    char *as_kw = cursor;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    if (*cursor) *cursor++ = '\0';
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    if (as_kw[0] == '\0' || strcasecmp(as_kw, "as") != 0) {
        parse_error(p, "expected 'as' after variable name");
        free(save);
        return NULL;
    }
    
    const char *endp = NULL;
    char *value = extract_quoted(cursor, &endp);
    if (!value) {
        parse_error(p, "expected quoted value after 'as'");
        free(save);
        return NULL;
    }
    
    char *name_copy = xstrdup(name);
    free(save);

    Stmt *s = xmalloc(sizeof(Stmt));
    memset(s, 0, sizeof(*s));
    s->kind = K_DEFINE;
    s->define.name  = name_copy;
    s->define.value = value;
    return s;
}

static bool match_word_boundary(const char *s, const char *word, size_t wlen) {
    if (strncasecmp(s, word, wlen) != 0) return false;
    char c = s[wlen];
    return (c == '\0' || isspace((unsigned char)c) || c == ';');
}

static bool match_float_calc_kw(const char *line, int *width_out, size_t *len_out) {
    if (strncasecmp(line, "float", 5) != 0) return false;
    const char *p = line + 5;
    const char *dstart = p;
    while (isdigit((unsigned char)*p)) p++;
    if (p == dstart) return false;
    int width = atoi(dstart);
    if (strncasecmp(p, "_calculate", 10) != 0) return false;
    const char *after = p + 10;
    if (!(*after == '\0' || isspace((unsigned char)*after) || *after == ';'))
        return false;
    *width_out = width;
    *len_out = (size_t)(after - line);
    return true;
}

#define ZTSL_LIBDIR "/usr/lib/ztsl"

/* def_mod NAME -> /usr/lib/ztsl/NAME-<arch>.so (libs are written in C).
 * 'libztsl' is the built-in runtime: ztc ignores it and compiles the program. */
static char *mod_path(const char *name) {
    struct utsname u;
    const char *arch = (uname(&u) == 0) ? u.machine : "unknown";
    size_t n = strlen(ZTSL_LIBDIR) + strlen(name) + strlen(arch) + 8;
    char *path = xmalloc(n);
    snprintf(path, n, "%s/%s-%s.so", ZTSL_LIBDIR, name, arch);
    return path;
}

/* symbol a module exports: ztsl_module_<name> (non-alphanumerics become '_') */
static char *mod_symbol(const char *name) {
    size_t n = strlen(name) + 16;
    char *sym = xmalloc(n);
    snprintf(sym, n, "ztsl_module_%s", name);
    for (char *c = sym + 12; *c; c++)
        if (!isalnum((unsigned char)*c)) *c = '_';
    return sym;
}

static bool is_builtin_stmt_name(const char *n) {
    static const char *kw[] = {
        "define", "if", "else", "endif", "func", "sys.exec", "sys.exec.silent",
        "text.show", "delete_file", "create_file", "write_on_file", "append_file",
        "ccompat", "run.func", "def_mod", "mem.alloc", "mem.free", "mem.write",
        "mem.show", "ztsl.start", "ztsl.end", "ztslo.start", "ztslo.end", NULL
    };
    for (size_t i = 0; kw[i]; i++)
        if (strcasecmp(n, kw[i]) == 0) return true;
    size_t nl = strlen(n);
    if (strncasecmp(n, "float", 5) == 0 && nl > 15 &&
        strcasecmp(n + nl - 10, "_calculate") == 0) return true;
    return false;
}

/* index of the library statement that starts 'line', or -1 */
static long find_lib_stmt(const Program *prog, const char *line) {
    if (!prog) return -1;
    for (size_t i = 0; i < prog->nlstmts; i++) {
        size_t n = strlen(prog->lstmts[i].name);
        if (strncmp(line, prog->lstmts[i].name, n) == 0 &&
            (line[n] == '\0' || isspace((unsigned char)line[n])))
            return (long)i;
    }
    return -1;
}

/* def_mod: records the module and loads it (dlopen) so its statements can be
 * parsed. Takes ownership of 'name'. Returns false (with a parse error) when
 * the library is missing, cannot be loaded, or breaks the ABI. */
static bool prog_load_mod(Parser *p, Program *prog, char *name) {
    for (size_t i = 0; i < prog->nmods; i++)
        if (strcmp(prog->mods[i], name) == 0) { free(name); return true; }
    size_t idx = prog->nmods;
    prog->mods = xrealloc(prog->mods, sizeof(char *) * (idx + 1));
    prog->modh = xrealloc(prog->modh, sizeof(void *) * (idx + 1));
    prog->mods[idx] = name;
    prog->modh[idx] = NULL;
    prog->nmods++;
    if (strcmp(name, "libztsl") == 0) return true;

    char *path = mod_path(name);
    if (access(path, R_OK) != 0) {
        zt_error("def_mod %s: %s not found", name, path);
        free(path);
        parse_error(p, "def_mod library not found");
        return false;
    }
    void *h = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (!h) {
        const char *why = dlerror();
        zt_error("def_mod %s: cannot load %s: %s", name, path, why ? why : "?");
        free(path);
        parse_error(p, "def_mod library cannot be loaded");
        return false;
    }
    prog->modh[idx] = h;
    char *sym = mod_symbol(name);
    const ZtslModule *m = (const ZtslModule *)dlsym(h, sym);
    free(path);
    if (!m) {         /* a plain C library used only through ccompat */
        free(sym);
        return true;
    }
    if (m->abi != ZTSL_ABI || !m->name || strcmp(m->name, name) != 0 || !m->stmts) {
        zt_error("def_mod %s: %s is not a valid ZTSL module (abi %u, expected %d; "
                 "name '%s')", name, sym, m->abi, ZTSL_ABI, m->name ? m->name : "?");
        free(sym);
        parse_error(p, "invalid ZTSL module");
        return false;
    }
    free(sym);
    for (const ZtslStmtEntry *e = m->stmts; e->name; e++) {
        bool bad = (e->name[0] == '\0' || !e->fn);
        for (const char *c = e->name; *c; c++)
            if (isspace((unsigned char)*c) || *c == '"') bad = true;
        if (bad || is_builtin_stmt_name(e->name)) {
            zt_error("def_mod %s: statement name '%s' is invalid or reserved",
                     name, e->name ? e->name : "(null)");
            parse_error(p, "bad library statement name");
            return false;
        }
        if (find_lib_stmt(prog, e->name) >= 0) {
            zt_error("def_mod %s: statement '%s' is already provided by another module",
                     name, e->name);
            parse_error(p, "duplicate library statement");
            return false;
        }
        prog->lstmts = xrealloc(prog->lstmts, sizeof(LibStmt) * (prog->nlstmts + 1));
        prog->lstmts[prog->nlstmts].name = xstrdup(e->name);
        prog->lstmts[prog->nlstmts].fn = e->fn;
        prog->lstmts[prog->nlstmts].mod = idx;
        prog->nlstmts++;
    }
    return true;
}

static void prog_free_mods(Program *prog) {
    for (size_t i = 0; i < prog->nmods; i++) {
        free(prog->mods[i]);
        if (prog->modh && prog->modh[i]) dlclose(prog->modh[i]);
    }
    for (size_t i = 0; i < prog->nlstmts; i++) free(prog->lstmts[i].name);
    free(prog->mods);
    free(prog->modh);
    free(prog->lstmts);
    prog->mods = NULL;
    prog->modh = NULL;
    prog->lstmts = NULL;
    prog->nmods = prog->nlstmts = 0;
}

static bool reject_if_misplaced_statement(Parser *p, const char *line) {
    int width; size_t kwlen;
    if (match_float_calc_kw(line, &width, &kwlen)) {
        zt_error("'floatNN_calculate' is a statement and must be inside "
                "a func \"name\" { ... } body, not here: '%s'", line);
        parse_error(p, "floatNN_calculate outside a func body");
        return true;
    }

    if (starts_with_kw(line, "define")) {
        zt_error("'define' must be inside a func \"name\" { ... } body "
                "or a ztslo.start/ztslo.end block, not here: '%s'", line);
        parse_error(p, "define outside a func body or ztslo block");
        return true;
    }

    if (find_lib_stmt(p->prog, line) >= 0) {
        zt_error("library statement must be inside a func \"name\" "
                "{ ... } body, not here: '%s'", line);
        parse_error(p, "library statement outside a func body");
        return true;
    }

    static const char *stmt_keywords[] = {
        "if", "sys.exec", "text.show",
        "delete_file", "create_file",
        "write_on_file", "append_file",
        "ccompat",
        "sys.exec.silent", "run.func",
        "mem.alloc", "mem.free", "mem.write", "mem.show",
        NULL
    };
    for (size_t i = 0; stmt_keywords[i]; i++) {
        if (starts_with_kw(line, stmt_keywords[i])) {
            zt_error("'%s' is a statement and must be inside a func \"name\" "
                    "{ ... } body, not here: '%s'", stmt_keywords[i], line);
            parse_error(p, "statement outside a func body");
            return true;
        }
    }
    return false;
}

static char *skip_ws(char *s) {
    while (*s && isspace((unsigned char)*s)) s++;
    return s;
}

/* Consumes the whole word 'w' (case-insensitive) plus the blanks after it. */
static bool take_word(char **sp, const char *w) {
    size_t n = strlen(w);
    if (!match_word_boundary(*sp, w, n)) return false;
    *sp = skip_ws(*sp + n);
    return true;
}

/* Reads a "quoted" or bare name. Returns a malloc'd string or NULL. */
static char *take_name(char **sp) {
    char *s = skip_ws(*sp);
    if (*s == '"') {
        const char *endp = NULL;
        char *out = extract_quoted(s, &endp);
        if (!out) return NULL;
        *sp = skip_ws((char *)endp);
        return out;
    }
    char *start = s;
    while (*s && !isspace((unsigned char)*s)) s++;
    if (s == start) return NULL;
    char *out = xstrndup(start, (size_t)(s - start));
    *sp = skip_ws(s);
    return out;
}

static bool require_ztsl26(Parser *p, const char *what) {
    if (g_ztv == ZTV_ZTSL26) return true;
    zt_error("'%s' is only available with -ztv=ztsl26", what);
    parse_error(p, "ztsl26-only construct used in p26 mode");
    return false;
}

/* <library statement> ARG... [as variable "name"] */
static Stmt *parse_libcall(Parser *p, long idx) {
    char *l = consume(p);
    size_t nl = strlen(p->prog->lstmts[idx].name);
    int argc = 0;
    char **argv = split_args(l + nl, &argc);
    free(l);
    char *varname = NULL;
    if (argc >= 3 && strcasecmp(argv[argc - 3], "as") == 0 &&
        strcasecmp(argv[argc - 2], "variable") == 0) {
        varname = xstrdup(argv[argc - 1]);
        free(argv[argc - 3]);
        free(argv[argc - 2]);
        free(argv[argc - 1]);
        argv[argc - 3] = NULL;
        argc -= 3;
    }
    Stmt *s = xmalloc(sizeof(Stmt));
    memset(s, 0, sizeof(*s));
    s->kind = K_LIBCALL;
    s->libcall.idx = (size_t)idx;
    s->libcall.args = argv;
    s->libcall.nargs = argc;
    s->libcall.varname = varname;
    return s;
}

/* "if argument ..." */
static bool is_arg_guard_line(const char *line) {
    if (!starts_with_kw(line, "if")) return false;
    line += 2;
    while (*line && isspace((unsigned char)*line)) line++;
    return match_word_boundary(line, "argument", 8);
}

static Stmt *parse_if(Parser *p) {
    char *line = consume(p);
    if (!line) { parse_error(p, "EOF in if"); return NULL; }

    
    char *s = line;
    while (*s && isspace((unsigned char)*s)) s++;
    s += 2;  
    while (*s && isspace((unsigned char)*s)) s++;

    
    CondSubj subj = SUBJ_VAR;
    char *var = NULL;
    char *fpath = NULL;
    char *argname = NULL;
    bool need_ea = false;
    bool is_is = true;
    CondKind ckind = COND_EQ;
    char **values = NULL;
    size_t nvalues = 0, cap = 0;
    bool seen_then = false;

    if (g_ztv == ZTV_ZTSL26 && match_word_boundary(s, "argument", 8)) {
        /* if argument <name> is passed [with %ea%]  |  if argument is not defined */
        s = skip_ws(s + 8);
        if (take_word(&s, "is")) {
            if (!take_word(&s, "not") || !take_word(&s, "defined")) {
                parse_error(p, "expected 'if argument is not defined'");
                free(line);
                return NULL;
            }
            ckind = COND_ARG_UNDEF;
        } else {
            argname = take_name(&s);
            if (!argname || !take_word(&s, "is") || !take_word(&s, "passed")) {
                parse_error(p, "expected 'if argument <name> is passed [with %ea%]'");
                free(line);
                free(argname);
                return NULL;
            }
            ckind = COND_ARG_PASSED;
            if (take_word(&s, "with")) {
                if (!take_word(&s, "%ea%")) {
                    parse_error(p, "expected '%ea%' after 'with'");
                    free(line);
                    free(argname);
                    return NULL;
                }
                need_ea = true;
            }
        }
        if (take_word(&s, "then")) seen_then = true;
        free(line);
        goto if_build;
    } else if (match_word_boundary(s, "read_file", 9)) {
        s += 9;
        while (*s && isspace((unsigned char)*s)) s++;
        const char *endp = NULL;
        fpath = extract_quoted(s, &endp);
        if (!fpath) {
            parse_error(p, "expected quoted path after 'read_file'");
            free(line);
            return NULL;
        }
        subj = SUBJ_READFILE;
        s = (char *)endp;
        while (*s && isspace((unsigned char)*s)) s++;
    } else {
        char *var_start = s;
        while (*s && !isspace((unsigned char)*s)) s++;
        if (*s == '\0') {
            parse_error(p, "expected operator in if");
            free(line);
            return NULL;
        }
        *s++ = '\0';
        var = xstrdup(var_start);
        while (*s && isspace((unsigned char)*s)) s++;
    }

    

    /* NB: "is not an empty file" is 20 characters (it used to be 21: the
     * matcher read one byte past the terminator and never matched when
     * 'then' followed on the same line). */
    if (subj == SUBJ_VAR && match_word_boundary(s, "is not an empty file", 20)) {
        ckind = COND_EMPTYFILE;
        is_is = false;
        s += 20;
    } else if (subj == SUBJ_VAR && match_word_boundary(s, "is an empty file", 16)) {
        ckind = COND_EMPTYFILE;
        is_is = true;
        s += 16;
    } else if (match_word_boundary(s, "is not", 6)) {
        is_is = false;
        s += 6;
    } else if (strncasecmp(s, "returns", 7) == 0 &&
               (s[7] == '\0' || isspace((unsigned char)s[7]))) {
        is_is = true;
        s += 7;
    } else if (match_word_boundary(s, "is", 2)) {
        is_is = true;
        s += 2;
        while (*s && isspace((unsigned char)*s)) s++;
        /* "result is =! 0" */
        if (strncmp(s, "=!", 2) == 0 || strncmp(s, "!=", 2) == 0) {
            is_is = false;
            s += 2;
        }
    } else if (strncmp(s, "=!", 2) == 0) {
        is_is = false;
        s += 2;
    } else if (strncmp(s, "!=", 2) == 0) {
        is_is = false;
        s += 2;
    } else {
        parse_error(p, "expected 'is', 'is not', 'returns', '=!' or '!=' in if");
        free(line);
        free(var);
        free(fpath);
        return NULL;
    }
    while (*s && isspace((unsigned char)*s)) s++;

    if (ckind == COND_EMPTYFILE) {
        
        if (strncasecmp(s, "then", 4) == 0 &&
            (s[4] == '\0' || isspace((unsigned char)s[4]) || s[4] == ';')) {
            s += 4;
            while (*s && (isspace((unsigned char)*s) || *s == ';')) s++;
            seen_then = true;
        }
        free(line);
        goto if_build;
    }

    

    while (*s) {
        if (*s == '"') {
            const char *endp = NULL;
            char *v = extract_quoted(s, &endp);
            if (!v) {
                parse_error(p, "bad quoted value in if");
                free(line);
                free(var);
                free(fpath);
                var = NULL;
                fpath = NULL;
                goto if_fail;
            }
            if (nvalues == cap) {
                cap = cap ? cap * 2 : 4;
                values = xrealloc(values, sizeof(char *) * (cap + 1));
            }
            values[nvalues++] = v;
            values[nvalues] = NULL;
            s = (char *)endp;
        } else {
            
            char *start = s;
            while (*s && !isspace((unsigned char)*s)) s++;
            char saved = *s;
            *s = '\0';
            char *v;
            if (strcasecmp(start, "empty") == 0) {
                
                v = xstrdup("");
            } else {
                v = xstrdup(start);
            }
            *s = saved;
            if (nvalues == cap) {
                cap = cap ? cap * 2 : 4;
                values = xrealloc(values, sizeof(char *) * (cap + 1));
            }
            values[nvalues++] = v;
            values[nvalues] = NULL;
        }
        while (*s && isspace((unsigned char)*s)) s++;

        
        if (strncasecmp(s, "or", 2) == 0 &&
            (s[2] == '\0' || isspace((unsigned char)s[2]))) {
            s += 2;
            while (*s && isspace((unsigned char)*s)) s++;
            continue;
        }
        
        if (strncasecmp(s, "then", 4) == 0 &&
            (s[4] == '\0' || isspace((unsigned char)s[4]) || s[4] == ';')) {
            s += 4;
            while (*s && (isspace((unsigned char)*s) || *s == ';')) s++;
            seen_then = true;
            break;
        }
        
        if (*s == '\0') break;
    }

    free(line);

if_build:
    
    if (!seen_then) {
        const char *next = peek(p);
        if (next && starts_with_kw(next, "then")) {
            char *nl = consume(p);
            free(nl);
        }
    }

    Stmt *stmt = xmalloc(sizeof(Stmt));
    memset(stmt, 0, sizeof(*stmt));
    stmt->kind = K_IF;
    stmt->cond.kind    = ckind;
    stmt->cond.subj    = subj;
    stmt->cond.var     = var;  
    var = NULL;
    stmt->cond.path    = fpath;
    fpath = NULL;
    stmt->cond.is_is   = is_is;
    stmt->cond.argname = argname;
    stmt->cond.need_ea = need_ea;
    stmt->cond.values  = values;
    stmt->cond.nvalues  = nvalues;
    stmt->cond.then_branch = NULL;
    stmt->cond.else_branch = NULL;

    
    p->if_depth++;
    stmt->cond.then_branch = parse_stmt_list(p, "else");
    if (p->error) {
        p->if_depth--;
        stmt_free(stmt);
        return NULL;
    }

    
    const char *nx = peek(p);
    if (nx && starts_with_kw(nx, "else")) {
        char *el = consume(p);
        free(el);
        stmt->cond.else_branch = parse_stmt_list(p, NULL);
        if (p->error) {
            p->if_depth--;
            stmt_free(stmt);
            return NULL;
        }
    }
    p->if_depth--;

    
    const char *maybe_endif = peek(p);
    if (maybe_endif && starts_with_kw(maybe_endif, "endif")) {
        char *ei = consume(p);
        free(ei);
    }

    return stmt;

if_fail:
    free(var);
    free(fpath);
    for (size_t i = 0; i < nvalues; i++) free(values[i]);
    free(values);
    return NULL;
}

static Stmt *parse_stmt_list(Parser *p, const char *terminator) {
    Stmt *head = NULL, *tail = NULL;
    while (true) {
        const char *line = peek(p);
        if (!line) break;

        
        if (terminator && starts_with_kw(line, terminator)) break;

        
        if (line[0] == '}') break;

        /* ztsl26: 'if argument ...' is always a top-level guard of a func, so
         * it closes any 'if' still open (the draft syntax has no 'endif'). */
        if (g_ztv == ZTV_ZTSL26 && p->if_depth > 0 && is_arg_guard_line(line)) break;

        if (starts_with_kw(line, "endif")) break;

        
        if (starts_with_kw(line, "ztsl.end") || starts_with_kw(line, "zstl.end"))
            break;

        if (starts_with_kw(line, "ztslo.end") || starts_with_kw(line, "zstlo.end")) break;

        Stmt *s = parse_stmt(p);
        if (!s) {
            if (p->error) {
                stmt_free(head);
                return NULL;
            }
            continue;
        }
        if (!head) {
            head = tail = s;
        } else {
            tail->next = s;
            tail = s;
        }
    }
    return head;
}

static Stmt *parse_stmt(Parser *p) {
    const char *line = peek(p);
    if (!line) return NULL;

    
    if (starts_with_kw(line, "define")) {
        return parse_define(p, NULL);
    }
    
    if (starts_with_kw(line, "if")) {
        return parse_if(p);
    }
    
    if (starts_with_kw(line, "sys.exec.silent")) {
        if (!require_ztsl26(p, "sys.exec.silent")) return NULL;
        char *l = consume(p);
        free(l);
        bool is_shell;
        char *code = parse_code_block(p, &is_shell, true);
        if (!code) return NULL;
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_EXEC;
        s->exec.is_shell = is_shell;
        s->exec.silent = true;
        s->exec.code = code;
        return s;
    }

    if (starts_with_kw(line, "run.func")) {
        if (!require_ztsl26(p, "run.func")) return NULL;
        char *l = consume(p);
        char *cur = skip_ws(l + 8);
        char *name = take_name(&cur);
        free(l);
        if (!name) {
            parse_error(p, "expected function name after 'run.func'");
            return NULL;
        }
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_RUNFUNC;
        s->runfunc.name = name;
        return s;
    }

    if (starts_with_kw(line, "mem.alloc") || starts_with_kw(line, "mem.free") ||
        starts_with_kw(line, "mem.write") || starts_with_kw(line, "mem.show")) {
        StmtKind mk;
        size_t kwlen;
        const char *usage;
        if (starts_with_kw(line, "mem.alloc")) {
            mk = K_MEMALLOC; kwlen = 9;
            usage = "usage: mem.alloc \"name\" SIZE";
        } else if (starts_with_kw(line, "mem.free")) {
            mk = K_MEMFREE; kwlen = 8;
            usage = "usage: mem.free \"name\"";
        } else if (starts_with_kw(line, "mem.write")) {
            mk = K_MEMWRITE; kwlen = 9;
            usage = "usage: mem.write \"name\" OFFSET \"text\"";
        } else {
            mk = K_MEMSHOW; kwlen = 8;
            usage = "usage: mem.show \"name\"";
        }
        char *l = consume(p);
        char *cur = skip_ws(l + kwlen);
        char *mname = take_name(&cur);
        char *num = NULL, *text = NULL;
        bool ok = (mname != NULL);
        if (ok && (mk == K_MEMALLOC || mk == K_MEMWRITE)) {
            num = take_name(&cur);
            ok = (num != NULL);
        }
        if (ok && mk == K_MEMWRITE) {
            const char *endp = NULL;
            text = extract_quoted(cur, &endp);
            ok = (text != NULL);
        }
        free(l);
        if (!ok) {
            zt_error("%s", usage);
            parse_error(p, "bad mem statement");
            free(mname);
            free(num);
            free(text);
            return NULL;
        }
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = mk;
        s->mem.name = mname;
        s->mem.num  = num;
        s->mem.text = text;
        return s;
    }

    if (starts_with_kw(line, "sys.exec")) {
        char *l = consume(p);
        free(l);
        bool is_shell;
        char *code = parse_code_block(p, &is_shell, true);
        if (!code) return NULL;
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_EXEC;
        s->exec.is_shell = is_shell;
        s->exec.code = code;
        return s;
    }
    
    if (starts_with_kw(line, "text.show")) {
        char *l = consume(p);
        free(l);
        bool is_shell;
        char *code = parse_code_block(p, &is_shell, false);
        if (!code) return NULL;
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_SHOW;
        s->show.code = code;
        return s;
    }
    
    if (starts_with_kw(line, "delete_file") || starts_with_kw(line, "create_file")) {
        bool is_delete = starts_with_kw(line, "delete_file");
        char *l = consume(p);
        const char *cursor = l + (is_delete ? 11 : 11);
        while (*cursor && isspace((unsigned char)*cursor)) cursor++;
        const char *endp = NULL;
        char *path = extract_quoted(cursor, &endp);
        free(l);
        if (!path) {
            parse_error(p, is_delete ? "expected quoted path after 'delete_file'"
                                      : "expected quoted path after 'create_file'");
            return NULL;
        }
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        if (is_delete) {
            s->kind = K_DELETE;
            s->delfile.path = path;
        } else {
            s->kind = K_CREATE;
            s->mkfile.path = path;
        }
        return s;
    }
    
    if (starts_with_kw(line, "write_on_file") || starts_with_kw(line, "append_file")) {
        bool is_write = starts_with_kw(line, "write_on_file");
        char *l = consume(p);
        const char *cursor = l + (is_write ? 13 : 11);
        while (*cursor && isspace((unsigned char)*cursor)) cursor++;
        const char *endp = NULL;
        char *path = extract_quoted(cursor, &endp);
        free(l);
        if (!path) {
            parse_error(p, is_write ? "expected quoted path after 'write_on_file'"
                                     : "expected quoted path after 'append_file'");
            return NULL;
        }
        char *code = parse_raw_block(p);
        if (!code) { free(path); return NULL; }
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = is_write ? K_WRITE : K_APPEND;
        s->writefile.path = path;
        s->writefile.code = code;
        return s;
    }
    {
        int width; size_t kwlen;
        if (match_float_calc_kw(line, &width, &kwlen)) {
            if (width != 32 && width != 42 && width != 64 &&
                width != 76 && width != 128) {
                zt_error("unsupported float width '%d' "
                        "(expected 32, 42, 64, 76 or 128)", width);
                char *l = consume(p);
                free(l);
                parse_error(p, "unsupported float width");
                return NULL;
            }
            char *l = consume(p);
            const char *cursor = l + kwlen;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            const char *start = cursor;
            while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
            if (cursor == start) {
                parse_error(p, "expected left operand in float calculation");
                free(l);
                return NULL;
            }
            char *lhs = xstrndup(start, (size_t)(cursor - start));
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            char op = *cursor;
            if (op != '+' && op != '-' && op != '*' && op != '/') {
                zt_error("expected +, -, * or / in float calculation");
                free(lhs);
                free(l);
                parse_error(p, "bad operator in float calculation");
                return NULL;
            }
            cursor++;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            start = cursor;
            while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
            if (cursor == start) {
                parse_error(p, "expected right operand in float calculation");
                free(lhs);
                free(l);
                return NULL;
            }
            char *rhs = xstrndup(start, (size_t)(cursor - start));
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            if (!match_word_boundary(cursor, "as", 2)) {
                parse_error(p, "expected 'as' in float calculation");
                free(lhs);
                free(rhs);
                free(l);
                return NULL;
            }
            cursor += 2;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            if (!match_word_boundary(cursor, "variable", 8)) {
                parse_error(p, "expected 'variable' in float calculation");
                free(lhs);
                free(rhs);
                free(l);
                return NULL;
            }
            cursor += 8;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            const char *endp = NULL;
            char *varname = extract_quoted(cursor, &endp);
            free(l);
            if (!varname) {
                parse_error(p, "expected quoted variable name after 'variable'");
                free(lhs);
                free(rhs);
                return NULL;
            }

            Stmt *s = xmalloc(sizeof(Stmt));
            memset(s, 0, sizeof(*s));
            s->kind = K_FLOATCALC;
            s->floatcalc.width  = width;
            s->floatcalc.op     = op;
            s->floatcalc.lhs_raw = lhs;
            s->floatcalc.rhs_raw = rhs;
            s->floatcalc.varname = varname;
            return s;
        }
    }
    
    if (starts_with_kw(line, "ccompat")) {
        char *l = consume(p);
        free(l);
        char *code = parse_raw_block(p);
        if (!code) return NULL;
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_CCOMPAT;
        s->ccompat.code = code;
        return s;
    }

    
    {
        long li = find_lib_stmt(p->prog, line);
        if (li >= 0) return parse_libcall(p, li);
    }

    char *l = consume(p);
    if (l) {
        const char *sug = suggest_keyword(l);
        if (sug) {
            zt_error("unknown line: '%s' (did you mean '%s'?)", l, sug);
            free(l);
            parse_error(p, "unknown line with suggestion");
            return NULL;
        }
        zt_warn("skipping unknown line: %s", l);
        free(l);
    }
    return NULL;
}

static Func *parse_func(Parser *p) {
    char *line = consume(p);
    if (!line) { parse_error(p, "EOF in func"); return NULL; }

    
    const char *s = line + 4;  
    while (*s && isspace((unsigned char)*s)) s++;

    char *name = NULL;
    if (*s == '"') {
        const char *endp = NULL;
        name = extract_quoted(s, &endp);
        free(line);
        if (!name) {
            parse_error(p, "expected quoted function name after 'func'");
            return NULL;
        }
    } else {
        
        const char *start = s;
        while (*s && !isspace((unsigned char)*s)) s++;
        if (s == start) {
            free(line);
            parse_error(p, "expected function name after 'func'");
            return NULL;
        }
        name = xstrndup(start, (size_t)(s - start));
        free(line);
    }

    Func *f = xmalloc(sizeof(Func));
    memset(f, 0, sizeof(*f));
    f->name = name;

    
    f->body = parse_stmt_list(p, NULL);
    if (p->error) {
        func_free(f);
        return NULL;
    }

    
    const char *cl = peek(p);
    if (!cl || cl[0] != '}') {
        parse_error(p, "expected '}' to close func");
        func_free(f);
        return NULL;
    }
    char *cll = consume(p);
    free(cll);

    return f;
}

static void parse_ztslo_block(Parser *p, Program *prog) {
    char *line = consume(p);  
    free(line);
    prog->inline_ztslo_used = true;

    while (true) {
        const char *l = peek(p);
        if (!l) { parse_error(p, "EOF in ztslo block"); return; }
        if (starts_with_kw(l, "zstlo.end")) {
            zt_warn("typo 'zstlo.end'; did you mean 'ztslo.end'?");
        }
        if (starts_with_kw(l, "ztslo.end") || starts_with_kw(l, "zstlo.end")) {
            char *e = consume(p);
            free(e);
            return;
        }
        if (starts_with_kw(l, "define")) {
            Stmt *s = parse_define(p, NULL);
            if (!s) {
                if (p->error) return;
                continue;
            }
            
            Var *v = xmalloc(sizeof(Var));
            v->name  = xstrdup(s->define.name);
            v->value = xstrdup(s->define.value);
            v->next = prog->vars;
            prog->vars = v;
            stmt_free(s);
            continue;
        }
        
        if (l[0] == '}' && l[1] == '\0') {
            char *skip = consume(p);
            free(skip);
            continue;
        }
        
        char *skip = consume(p);
        if (skip) {
            if (reject_if_misplaced_statement(p, skip)) {
                free(skip);
                return;
            }
            const char *sug = suggest_keyword(skip);
            if (sug) {
                zt_error("unknown line in ztslo: '%s' (did you mean '%s'?)", skip, sug);
                free(skip);
                parse_error(p, "unknown line with suggestion");
                return;
            }
            zt_warn("skipping line in ztslo: %s", skip);
            free(skip);
        }
    }
}

static void parse_ztsl_block(Parser *p, Program *prog) {
    char *line = consume(p);  
    free(line);

    while (true) {
        const char *l = peek(p);
        if (!l) { parse_error(p, "EOF in ztsl block"); return; }
        if (starts_with_kw(l, "zstl.end")) {
            zt_warn("typo 'zstl.end'; did you mean 'ztsl.end'?");
        }
        if (starts_with_kw(l, "ztsl.end") || starts_with_kw(l, "zstl.end")) {
            char *e = consume(p);
            free(e);
            return;
        }
        if (starts_with_kw(l, "ztslo.start")) {
            parse_ztslo_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (starts_with_kw(l, "zstlo.start")) {
            zt_warn("typo 'zstlo.start'; did you mean 'ztslo.start'?");
            parse_ztslo_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (starts_with_kw(l, "zstlo.end")) {
            zt_warn("typo 'zstlo.end'; did you mean 'ztslo.end'?");
        }
        if (starts_with_kw(l, "ztslo.end") || starts_with_kw(l, "zstlo.end")) {
            
            char *e = consume(p);
            free(e);
            continue;
        }
        if (starts_with_kw(l, "func")) {
            Func *f = parse_func(p);
            if (!f) {
                if (p->error) return;
                continue;
            }
            f->next = prog->funcs;
            prog->funcs = f;
            continue;
        }
        
        if (l[0] == '}' && l[1] == '\0') {
            char *skip = consume(p);
            free(skip);
            continue;
        }
        
        char *skip = consume(p);
        if (skip) {
            if (reject_if_misplaced_statement(p, skip)) {
                free(skip);
                return;
            }
            const char *sug = suggest_keyword(skip);
            if (sug) {
                zt_error("unknown top-level line: '%s' (did you mean '%s'?)", skip, sug);
                free(skip);
                parse_error(p, "unknown line with suggestion");
                return;
            }
            zt_warn("skipping top-level line: %s", skip);
            free(skip);
        }
    }
}

static void parse_program(Parser *p, Program *prog) {
    while (true) {
        const char *l = peek(p);
        if (!l) break;
        if (starts_with_kw(l, "zstl.start")) {
            zt_warn("typo 'zstl.start'; did you mean 'ztsl.start'?");
        } else if (starts_with_kw(l, "zstl.end")) {
            zt_warn("typo 'zstl.end'; did you mean 'ztsl.end'?");
        }
        if (starts_with_kw(l, "def_mod")) {
            if (!require_ztsl26(p, "def_mod")) return;
            char *dl = consume(p);
            char *cur = skip_ws(dl + 7);
            char *mname = take_name(&cur);
            free(dl);
            if (!mname) {
                parse_error(p, "expected module name after 'def_mod'");
                return;
            }
            if (!prog_load_mod(p, prog, mname)) return;
            continue;
        }
        if (starts_with_kw(l, "ztsl.start") || starts_with_kw(l, "zstl.start")) {
            parse_ztsl_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (starts_with_kw(l, "ztslo.start")) {
            parse_ztslo_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (l[0] == '}' && l[1] == '\0') {
            char *skip = consume(p);
            free(skip);
            continue;
        }
        char *skip = consume(p);
        if (skip) {
            if (reject_if_misplaced_statement(p, skip)) {
                free(skip);
                return;
            }
            const char *sug = suggest_keyword(skip);
            if (sug) {
                zt_error("unknown top-level line: '%s' (did you mean '%s'?)", skip, sug);
                free(skip);
                parse_error(p, "unknown line with suggestion");
                return;
            }
            zt_warn("skipping top-level line: %s", skip);
            free(skip);
        }
    }
}

static Var *var_find(Var *head, const char *name) {
    for (Var *v = head; v; v = v->next)
        if (strcasecmp(v->name, name) == 0) return v;
    return NULL;
}

static void var_set(Var **head, const char *name, const char *value) {
    Var *v = var_find(*head, name);
    if (v) {
        free(v->value);
        v->value = xstrdup(value);
        return;
    }
    v = xmalloc(sizeof(Var));
    v->name  = xstrdup(name);
    v->value = xstrdup(value);
    v->next = *head;
    *head = v;
}

static char *subst_vars(const char *s, Var *vars) {
    dstring out;
    dstr_init(&out);
    const char *p = s;
    while (*p) {
        if (*p == '@') {
            
            const char *start = p + 1;
            const char *q = start;
            if (isalpha((unsigned char)*q) || *q == '_') {
                while (isalnum((unsigned char)*q) || *q == '_') q++;
                size_t namelen = (size_t)(q - start);
                char *name = xstrndup(start, namelen);
                Var *v = var_find(vars, name);
                if (v) {
                    dstr_append_cstr(&out, v->value);
                } else {
                    
                    dstr_append_char(&out, '@');
                    dstr_append_cstr(&out, name);
                }
                free(name);
                p = q;
                continue;
            }
        }
        dstr_append_char(&out, *p);
        p++;
    }
    return out.data;
}

/* A named block of manual memory used by mem.alloc / mem.free / mem.write /
 * mem.show in interpreted runs. */
typedef struct {
    char          *name;
    unsigned char *data;
    size_t         size;
    bool           live;
    unsigned long  seq;
} MemH;

typedef struct {
    Program *prog;
    Var    **vars;
    bool     verbose;
    bool     dry_run;        /* true: generate C instead of executing */
    bool     force;
    dstring  gen_c;
    /* program arguments (ztsl26): %a% = args[0], %ea% = args[1] */
    char   **args;
    int      nargs;
    bool     handled;        /* some 'if argument ...' already matched */
    int      depth;          /* run.func nesting */
    /* interpreted manual memory */
    MemH    *mem;
    size_t   nmem;
    unsigned long seq;
    /* transpile: handle names -> zt_h[] indexes */
    char   **hnames;
    size_t   nhnames;
    /* results of library statements ("as variable"): expanded like %ea%,
     * so a value can never inject shell syntax */
    Var     *rvars;
    char   **rtvars;
    size_t   nrtvars;
} ExecCtx;

/* ---- memchk failure path (shared by the interpreter) ----
 * "E: Value Out of Bounds (2147483649)" is INT32_MAX + 2, i.e. the result of
 * pushing an int32 calculation past its range, followed by a segfault. */
__attribute__((noreturn)) static void zt_memchk_abort(void) {
    volatile long long edge = 2147483648LL;   /* INT32_MAX + 1 */
    long long r = edge + 1;
    fflush(stdout);
    fprintf(stderr, "E: Value Out of Bounds (%lld)\n", r);
    fflush(stderr);
    signal(SIGSEGV, SIG_DFL);
    raise(SIGSEGV);
    _exit(139);
}

/* A memory violation: with -libmemchk it aborts as above; without it, the
 * interpreter still refuses to touch memory it should not (plain error). */
static int mem_violation(const char *what, const char *name) {
    if (g_memchk) zt_memchk_abort();
    zt_error("%s: %s", what, name);
    return 1;
}

static MemH *mem_find(ExecCtx *ctx, const char *name) {
    for (size_t i = 0; i < ctx->nmem; i++)
        if (strcmp(ctx->mem[i].name, name) == 0) return &ctx->mem[i];
    return NULL;
}

static bool parse_size(const char *s, size_t *out) {
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s == '\0' || *s == '-') return false;
    char *e = NULL;
    errno = 0;
    unsigned long long v = strtoull(s, &e, 0);
    if (errno != 0 || e == s || *e != '\0') return false;
    *out = (size_t)v;
    return true;
}

static char *unescape_dup(const char *s) {
    dstring o;
    dstr_init(&o);
    for (; *s; s++) {
        if (*s == '\\' && s[1]) {
            s++;
            switch (*s) {
                case 'n':  dstr_append_char(&o, '\n'); break;
                case 't':  dstr_append_char(&o, '\t'); break;
                case 'r':  dstr_append_char(&o, '\r'); break;
                case '\\': dstr_append_char(&o, '\\'); break;
                case '"':  dstr_append_char(&o, '"');  break;
                default:   dstr_append_char(&o, '\\'); dstr_append_char(&o, *s); break;
            }
        } else {
            dstr_append_char(&o, *s);
        }
    }
    return o.data;
}

static int mem_do_alloc(ExecCtx *ctx, const char *name, const char *num) {
    size_t n;
    if (!parse_size(num, &n)) {
        zt_error("mem.alloc %s: invalid size '%s'", name, num);
        return 1;
    }
    MemH *h = mem_find(ctx, name);
    if (h && h->live) return mem_violation("memory leak (handle reallocated while live)", name);
    if (!h) {
        ctx->mem = xrealloc(ctx->mem, sizeof(MemH) * (ctx->nmem + 1));
        h = &ctx->mem[ctx->nmem++];
        memset(h, 0, sizeof(*h));
        h->name = xstrdup(name);
    }
    h->data = calloc(n ? n : 1, 1);
    if (!h->data) {
        zt_error("mem.alloc %s: out of memory (%zu bytes)", name, n);
        return 1;
    }
    h->size = n;
    h->live = true;
    h->seq  = ++ctx->seq;
    return 0;
}

static int mem_do_free(ExecCtx *ctx, const char *name) {
    MemH *h = mem_find(ctx, name);
    if (!h) { zt_error("mem.free: unknown handle '%s'", name); return 1; }
    if (!h->live) return mem_violation("double free", name);
    free(h->data);
    h->data = NULL;
    h->live = false;
    return 0;
}

static int mem_do_write(ExecCtx *ctx, const char *name, const char *off_s, const char *text) {
    MemH *h = mem_find(ctx, name);
    if (!h) { zt_error("mem.write: unknown handle '%s'", name); return 1; }
    if (!h->live) return mem_violation("use after free", name);
    size_t off;
    if (!parse_size(off_s, &off)) {
        zt_error("mem.write %s: invalid offset '%s'", name, off_s);
        return 1;
    }
    size_t len = strlen(text);
    if (off > h->size || len + 1 > h->size - off)
        return mem_violation("buffer overflow", name);
    memcpy(h->data + off, text, len + 1);
    return 0;
}

static int mem_do_show(ExecCtx *ctx, const char *name) {
    MemH *h = mem_find(ctx, name);
    if (!h) { zt_error("mem.show: unknown handle '%s'", name); return 1; }
    if (!h->live) return mem_violation("use after free", name);
    if (h->size == 0 || !memchr(h->data, '\0', h->size))
        return mem_violation("buffer overflow (read past end)", name);
    fputs((const char *)h->data, stdout);
    fflush(stdout);
    return 0;
}

/* Any block allocated after sequence number 'start' that is still live is a leak. */
static int mem_leak_since(ExecCtx *ctx, unsigned long start) {
    for (size_t i = 0; i < ctx->nmem; i++)
        if (ctx->mem[i].live && ctx->mem[i].seq > start)
            return mem_violation("memory leak", ctx->mem[i].name);
    return 0;
}

static void mem_free_all(ExecCtx *ctx) {
    for (size_t i = 0; i < ctx->nmem; i++) {
        free(ctx->mem[i].name);
        free(ctx->mem[i].data);
    }
    free(ctx->mem);
    ctx->mem = NULL;
    ctx->nmem = 0;
}

/* ---- %a% / %ea% expansion (ztsl26) ----
 * %a% is the first program argument, %ea% the one after it. With quote=true
 * the values are single-quoted so they cannot inject shell syntax. */
static char *expand_args(char **args, int nargs, Var *rvars, const char *tmpl, bool quote) {
    dstring out;
    dstr_init(&out);
    for (const char *p = tmpl; *p; ) {
        const char *val = NULL;
        size_t adv = 0;
        if (strncmp(p, "%ea%", 4) == 0) { val = nargs > 1 ? args[1] : ""; adv = 4; }
        else if (strncmp(p, "%a%", 3) == 0) { val = nargs > 0 ? args[0] : ""; adv = 3; }
        if (!val && *p == '@' && (isalpha((unsigned char)p[1]) || p[1] == '_')) {
            const char *q = p + 1;
            while (isalnum((unsigned char)*q) || *q == '_') q++;
            char *nm = xstrndup(p + 1, (size_t)(q - p - 1));
            Var *rv = var_find(rvars, nm);
            free(nm);
            if (rv) { val = rv->value; adv = (size_t)(q - p); }
        }
        if (!val) { dstr_append_char(&out, *p++); continue; }
        p += adv;
        if (!quote) { dstr_append_cstr(&out, val); continue; }
        dstr_append_char(&out, '\'');
        for (; *val; val++) {
            if (*val == '\'') dstr_append_cstr(&out, "'\\''");
            else dstr_append_char(&out, *val);
        }
        dstr_append_char(&out, '\'');
    }
    return out.data;
}

/* ---- program structure queries (ztsl26) ---- */
static Func *find_func(Program *prog, const char *name) {
    for (Func *f = prog->funcs; f; f = f->next)
        if (strcmp(f->name, name) == 0) return f;
    return NULL;
}

static bool stmts_define_arg(Stmt *s, const char *name) {
    for (; s; s = s->next) {
        if (s->kind != K_IF) continue;
        if (s->cond.kind == COND_ARG_PASSED && strcmp(s->cond.argname, name) == 0) return true;
        if (stmts_define_arg(s->cond.then_branch, name)) return true;
        if (stmts_define_arg(s->cond.else_branch, name)) return true;
    }
    return false;
}

static bool prog_arg_defined(Program *prog, const char *name) {
    for (Func *f = prog->funcs; f; f = f->next)
        if (stmts_define_arg(f->body, name)) return true;
    return false;
}

static void stmts_collect_args(Stmt *s, char ***names, size_t *nn) {
    for (; s; s = s->next) {
        if (s->kind != K_IF) continue;
        if (s->cond.kind == COND_ARG_PASSED) {
            bool dup = false;
            for (size_t i = 0; i < *nn; i++)
                if (strcmp((*names)[i], s->cond.argname) == 0) dup = true;
            if (!dup) {
                *names = xrealloc(*names, sizeof(char *) * (*nn + 1));
                (*names)[(*nn)++] = s->cond.argname;
            }
        }
        stmts_collect_args(s->cond.then_branch, names, nn);
        stmts_collect_args(s->cond.else_branch, names, nn);
    }
}

static bool stmts_run_func(Stmt *s, const char *name) {
    for (; s; s = s->next) {
        if (s->kind == K_RUNFUNC && strcmp(s->runfunc.name, name) == 0) return true;
        if (s->kind == K_IF) {
            if (stmts_run_func(s->cond.then_branch, name)) return true;
            if (stmts_run_func(s->cond.else_branch, name)) return true;
        }
    }
    return false;
}

static bool prog_runs_func(Program *prog, const char *name) {
    for (Func *f = prog->funcs; f; f = f->next)
        if (stmts_run_func(f->body, name)) return true;
    return false;
}

static bool func_starts_with_guard(Func *fn) {
    return fn->body && fn->body->kind == K_IF &&
           (fn->body->cond.kind == COND_ARG_PASSED ||
            fn->body->cond.kind == COND_ARG_UNDEF);
}

/* ztsl26 entry points: a func starting with an 'if argument' guard, or any func
 * nobody reaches through run.func. The rest (e.g. 'help') only run when called. */
static bool func_is_entry(Program *prog, Func *fn) {
    return func_starts_with_guard(fn) || !prog_runs_func(prog, fn->name);
}

static bool eval_arg_cond(ExecCtx *ctx, Cond *c, int *usage_rc) {
    if (c->kind == COND_ARG_UNDEF) {
        bool undef = !ctx->handled &&
                     (ctx->nargs < 1 || !prog_arg_defined(ctx->prog, ctx->args[0]));
        if (undef) ctx->handled = true;
        return undef;
    }
    if (ctx->nargs < 1 || strcmp(ctx->args[0], c->argname) != 0) return false;
    ctx->handled = true;
    if (c->need_ea && ctx->nargs < 2) {
        zt_error("command '%s' requires an argument", c->argname);
        *usage_rc = 2;
        return false;
    }
    return true;
}

static bool path_is_empty_file(const char *path) {
    struct stat st;
    if (stat(path, &st) != 0) {
        
        return true;
    }
    if (!S_ISREG(st.st_mode)) {
        
        return false;
    }
    return st.st_size == 0;
}

static double quantize_mantissa_bits(double v, int keep_bits) {
    
    if (v == 0.0 || !isfinite(v) || keep_bits >= 52) return v;
    uint64_t bits;
    memcpy(&bits, &v, sizeof(bits));
    int drop = 52 - keep_bits;
    uint64_t half = (uint64_t)1 << (drop - 1);
    uint64_t mask = ((uint64_t)1 << drop) - 1;
    uint64_t frac = bits & mask;
    bits &= ~mask;
    if (frac >= half) bits += ((uint64_t)1 << drop);
    memcpy(&v, &bits, sizeof(bits));
    return v;
}

static char *compute_float_calc(int width, const char *lhs_s, char op,
                                const char *rhs_s) {
    char buf[80];

    if (width == 32) {
        float a = strtof(lhs_s, NULL);
        float b = strtof(rhs_s, NULL);
        float r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0f) { return NULL; }
                r = a / b;
                break;
        }
        snprintf(buf, sizeof(buf), "%.9g", (double)r);
    } else if (width == 64 || width == 42) {
        double a = strtod(lhs_s, NULL);
        double b = strtod(rhs_s, NULL);
        double r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0) { return NULL; }
                r = a / b;
                break;
        }
        if (width == 42) r = quantize_mantissa_bits(r, 30);
        snprintf(buf, sizeof(buf), "%.17g", r);
    } else if (width == 76) {
        
        long double a = strtold(lhs_s, NULL);
        long double b = strtold(rhs_s, NULL);
        long double r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0L) { return NULL; }
                r = a / b;
                break;
        }
        snprintf(buf, sizeof(buf), "%.21Lg", r);
    } else { 
        
        __float128 a = strtold(lhs_s, NULL);
        __float128 b = strtold(rhs_s, NULL);
        __float128 r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0L) { return NULL; }
                r = a / b;
                break;
        }
        
        long double disp = (long double)r;
        snprintf(buf, sizeof(buf), "%.21Lg", disp);
    }
    return xstrdup(buf);
}

static bool eval_cond(Cond *c, Var *vars, Var *rvars) {
    if (c->kind == COND_EMPTYFILE) {
        Var *v = var_find(vars, c->var);
        if (!v) v = var_find(rvars, c->var);
        const char *path = v ? v->value : "";
        bool empty = path_is_empty_file(path);
        return c->is_is ? empty : !empty;
    }

    char *file_content = NULL;
    const char *val;
    if (c->subj == SUBJ_READFILE) {
        char *path = subst_vars(c->path, vars);
        file_content = read_file(path);
        free(path);
        if (!file_content) file_content = xstrdup("");
        val = file_content;
    } else {
        Var *v = var_find(vars, c->var);
        if (!v) v = var_find(rvars, c->var);
        val = v ? v->value : "";
    }

    bool result = false;
    if (c->is_is) {
        
        for (size_t i = 0; i < c->nvalues; i++) {
            char *sv = subst_vars(c->values[i], vars);
            bool eq = (strcmp(sv, val) == 0);
            free(sv);
            if (eq) { result = true; break; }
        }
    } else {
        
        result = true;
        for (size_t i = 0; i < c->nvalues; i++) {
            char *sv = subst_vars(c->values[i], vars);
            bool eq = (strcmp(sv, val) == 0);
            free(sv);
            if (eq) { result = false; break; }
        }
    }
    free(file_content);
    return result;
}

static char **split_args(const char *cmd, int *argc_out) {
    
    int argc = 0;
    const char *p = cmd;
    bool in_quote = false;
    while (*p) {
        while (*p && isspace((unsigned char)*p) && !in_quote) p++;
        if (!*p) break;
        argc++;
        while (*p && (!isspace((unsigned char)*p) || in_quote)) {
            if (*p == '"') in_quote = !in_quote;
            p++;
        }
    }
    if (argc == 0) {
        *argc_out = 0;
        return NULL;
    }
    char **argv = xmalloc(sizeof(char *) * (size_t)(argc + 1));
    int i = 0;
    p = cmd;
    in_quote = false;
    while (*p) {
        while (*p && isspace((unsigned char)*p) && !in_quote) p++;
        if (!*p) break;
        const char *start = p;
        dstring tok;
        dstr_init(&tok);
        while (*p && (!isspace((unsigned char)*p) || in_quote)) {
            if (*p == '"') {
                in_quote = !in_quote;
                p++;
                continue;
            }
            dstr_append_char(&tok, *p);
            p++;
        }
        (void)start;
        argv[i++] = tok.data;
    }
    argv[argc] = NULL;
    *argc_out = argc;
    return argv;
}

static void free_args(char **argv) {
    if (!argv) return;
    for (int i = 0; argv[i]; i++) free(argv[i]);
    free(argv);
}

static int run_shell(const char *cmd) {
    int rc = system(cmd);
    if (rc == -1) {
        zt_error("system() failed: %s", strerror(errno));
        return -1;
    }
    if (WIFEXITED(rc)) return WEXITSTATUS(rc);
    if (WIFSIGNALED(rc)) {
        zt_error("command terminated by signal %d", WTERMSIG(rc));
        return 128 + WTERMSIG(rc);
    }
    return rc;
}

static int run_exec_argv(char **argv, bool silent) {
    if (!argv || !argv[0]) {
        zt_error("empty exec command");
        return -1;
    }

    fflush(NULL);
    pid_t pid = fork();
    if (pid < 0) {
        zt_error("fork() failed: %s", strerror(errno));
        return -1;
    }
    if (pid == 0) {
        if (silent) {
            int fd = open("/dev/null", O_WRONLY);
            if (fd >= 0) {
                dup2(fd, STDOUT_FILENO);
                dup2(fd, STDERR_FILENO);
                close(fd);
            }
        }
        execvp(argv[0], argv);
        fprintf(stderr, "E: execvp(%s) failed: %s\n",
                argv[0], strerror(errno));
        _exit(127);
    }

    int status = 0;
    pid_t w;
    do {
        w = waitpid(pid, &status, 0);
    } while (w < 0 && errno == EINTR);

    if (w < 0) {
        zt_error("waitpid() failed: %s", strerror(errno));
        return -1;
    }
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    if (WIFSIGNALED(status)) {
        zt_error("%s terminated by signal %d", argv[0], WTERMSIG(status));
        return 128 + WTERMSIG(status);
    }
    return 0;
}

static int run_exec(const char *cmd) {
    int argc = 0;
    char **argv = split_args(cmd, &argc);
    if (argc == 0 || !argv) {
        zt_error("empty exec command");
        free_args(argv);
        return -1;
    }
    int rc = run_exec_argv(argv, false);
    free_args(argv);
    return rc;
}

/* ztsl26 command runner. exec: %a%/%ea% are expanded per argument AFTER the
 * line is split, so a value with spaces stays one argument. shell: values are
 * single-quoted. silent: stdout/stderr go to /dev/null. */
static int run_cmd26(ExecCtx *ctx, const char *code, bool is_shell, bool silent) {
    int rc;
    if (is_shell) {
        char *cmd = expand_args(ctx->args, ctx->nargs, ctx->rvars, code, true);
        if (silent) {
            dstring full;
            dstr_init(&full);
            dstr_append_cstr(&full, "( ");
            dstr_append_cstr(&full, cmd);
            dstr_append_cstr(&full, "\n) >/dev/null 2>&1");
            rc = run_shell(full.data);
            dstr_free(&full);
        } else {
            rc = run_shell(cmd);
        }
        free(cmd);
        return rc;
    }
    int argc = 0;
    char **argv = split_args(code, &argc);
    if (argc == 0 || !argv) {
        zt_error("empty exec command");
        free_args(argv);
        return -1;
    }
    for (int i = 0; i < argc; i++) {
        char *e = expand_args(ctx->args, ctx->nargs, ctx->rvars, argv[i], false);
        free(argv[i]);
        argv[i] = e;
    }
    rc = run_exec_argv(argv, silent);
    free_args(argv);
    return rc;
}

static void c_escape_append(dstring *out, const char *s) {
    dstr_append_char(out, '"');
    for (; *s; s++) {
        switch (*s) {
            case '"':  dstr_append_cstr(out, "\\\""); break;
            case '\\': dstr_append_cstr(out, "\\\\"); break;
            case '\n': dstr_append_cstr(out, "\\n");  break;
            case '\r': dstr_append_cstr(out, "\\r");  break;
            case '\t': dstr_append_cstr(out, "\\t");  break;
            default:
                if ((unsigned char)*s < 0x20) {
                    char buf[8];
                    snprintf(buf, sizeof(buf), "\\x%02x",
                             (unsigned char)*s);
                    dstr_append_cstr(out, buf);
                } else {
                    dstr_append_char(out, *s);
                }
                break;
        }
    }
    dstr_append_char(out, '"');
}

static int exec_stmt(ExecCtx *ctx, Stmt *s);

static int exec_stmt_list(ExecCtx *ctx, Stmt *list) {
    for (Stmt *s = list; s; s = s->next) {
        int rc = exec_stmt(ctx, s);
        if (rc != 0) return rc;
    }
    return 0;
}

/* Conditions that can only be decided when the compiled program runs
 * (arguments, last command result). The rest are folded at transpile time. */
static bool ctx_has_rtvar(const ExecCtx *ctx, const char *name) {
    for (size_t i = 0; i < ctx->nrtvars; i++)
        if (strcasecmp(ctx->rtvars[i], name) == 0) return true;
    return false;
}

static bool cond_is_runtime(const ExecCtx *ctx, const Cond *c) {
    if (c->kind == COND_ARG_PASSED || c->kind == COND_ARG_UNDEF) return true;
    if (g_ztv != ZTV_ZTSL26 || c->kind != COND_EQ || c->subj != SUBJ_VAR || !c->var)
        return false;
    return strcasecmp(c->var, "result") == 0 || ctx_has_rtvar(ctx, c->var);
}

/* names assigned by library statements (known before code generation, so an
 * 'if' may come before the assignment in the source and still be right) */
static void stmts_collect_rtvars(Stmt *s, ExecCtx *ctx) {
    for (; s; s = s->next) {
        if (s->kind == K_LIBCALL && s->libcall.varname &&
            !ctx_has_rtvar(ctx, s->libcall.varname)) {
            ctx->rtvars = xrealloc(ctx->rtvars, sizeof(char *) * (ctx->nrtvars + 1));
            ctx->rtvars[ctx->nrtvars++] = s->libcall.varname;
        }
        if (s->kind == K_IF) {
            stmts_collect_rtvars(s->cond.then_branch, ctx);
            stmts_collect_rtvars(s->cond.else_branch, ctx);
        }
    }
}

static int hindex(ExecCtx *ctx, const char *name) {
    for (size_t i = 0; i < ctx->nhnames; i++)
        if (strcmp(ctx->hnames[i], name) == 0) return (int)i;
    ctx->hnames = xrealloc(ctx->hnames, sizeof(char *) * (ctx->nhnames + 1));
    ctx->hnames[ctx->nhnames] = xstrdup(name);
    return (int)ctx->nhnames++;
}

static int func_index(Program *prog, const char *name) {
    int i = 0;
    for (Func *f = prog->funcs; f; f = f->next, i++)
        if (strcmp(f->name, name) == 0) return i;
    return -1;
}

static int gen_exec26(ExecCtx *ctx, const char *code, bool is_shell, bool silent) {
    dstring *g = &ctx->gen_c;
    if (is_shell) {
        dstr_append_cstr(g, "    zt_result = zt_run_shell(");
        c_escape_append(g, code);
        dstr_appendf(g, ", %d);\n", silent ? 1 : 0);
    } else {
        int argc = 0;
        char **argv = split_args(code, &argc);
        if (argc == 0 || !argv) {
            zt_error("empty exec command");
            free_args(argv);
            return 1;
        }
        dstr_append_cstr(g, "    { const char *za[] = {");
        for (int i = 0; i < argc; i++) {
            c_escape_append(g, argv[i]);
            dstr_append_cstr(g, ", ");
        }
        dstr_appendf(g, "NULL}; zt_result = zt_run_exec(za, %d); }\n", silent ? 1 : 0);
        free_args(argv);
    }
    if (!silent) dstr_append_cstr(g, "    if (zt_result != 0) return 1;\n");
    return 0;
}

/* if argument ... / if result ... : emitted as a real C if/else. Note that
 * 'define' inside such a branch still takes effect at transpile time. */
static int gen_runtime_if(ExecCtx *ctx, Stmt *s) {
    Cond *c = &s->cond;
    dstring *g = &ctx->gen_c;
    dstr_append_cstr(g, "    {\n");
    if (c->kind == COND_ARG_PASSED) {
        dstr_append_cstr(g, "    int zc = zt_arg_passed(");
        c_escape_append(g, c->argname);
        dstr_appendf(g, ", %d);\n    if (zt_usage_err) return 2;\n", c->need_ea ? 1 : 0);
    } else if (c->kind == COND_ARG_UNDEF) {
        dstr_append_cstr(g, "    int zc = zt_arg_undef();\n");
    } else {
        dstr_append_cstr(g, "    int zc = ");
        dstr_append_cstr(g, c->is_is ? "(" : "!(");
        if (c->nvalues == 0) dstr_append_cstr(g, "0");
        for (size_t i = 0; i < c->nvalues; i++) {
            char *sv = subst_vars(c->values[i], *ctx->vars);
            if (i) dstr_append_cstr(g, " || ");
            if (strcasecmp(c->var, "result") == 0) {
                dstr_append_cstr(g, "zt_res_eq(");
            } else {
                dstr_append_cstr(g, "zt_var_eq(");
                c_escape_append(g, c->var);
                dstr_append_cstr(g, ", ");
            }
            c_escape_append(g, sv);
            dstr_append_cstr(g, ")");
            free(sv);
        }
        dstr_append_cstr(g, ");\n");
    }
    dstr_append_cstr(g, "    if (zc) {\n");
    int rc = exec_stmt_list(ctx, c->then_branch);
    if (rc == 0) {
        dstr_append_cstr(g, "    } else {\n");
        rc = exec_stmt_list(ctx, c->else_branch);
    }
    dstr_append_cstr(g, "    }\n    }\n");
    return rc;
}

/* mem.* in generated C. Without memchk this is plain manual memory (malloc /
 * free / memcpy, no checks). With memchk, malloc/free are the guarded ones and
 * mem.write also checks its bounds explicitly. */
static int gen_mem(ExecCtx *ctx, StmtKind k, const char *name, const char *num,
                   const char *text) {
    dstring *g = &ctx->gen_c;
    int h = hindex(ctx, name);
    switch (k) {
        case K_MEMALLOC: {
            size_t n;
            if (!parse_size(num, &n)) {
                zt_error("mem.alloc %s: invalid size '%s'", name, num);
                return 1;
            }
            dstr_appendf(g, "    zt_h[%d] = (char *)malloc(%zu);\n"
                            "    zt_hn[%d] = %zu;\n"
                            "    if (!zt_h[%d]) return 1;\n", h, n, h, n, h);
            break;
        }
        case K_MEMFREE:
            dstr_appendf(g, "    if (!zt_h[%d]) { fputs(\"E: mem.free: handle '%s' was never allocated\\n\", stderr); return 1; }\n", h, name);
            dstr_appendf(g, "    free(zt_h[%d]);\n", h);
            break;
        case K_MEMWRITE: {
            size_t off;
            if (!parse_size(num, &off)) {
                zt_error("mem.write %s: invalid offset '%s'", name, num);
                return 1;
            }
            size_t len = strlen(text);
            dstr_appendf(g, "    if (!zt_h[%d]) { fputs(\"E: mem.write: handle '%s' was never allocated\\n\", stderr); return 1; }\n", h, name);
            dstr_append_cstr(g, "    { const char *zs = ");
            c_escape_append(g, text);
            dstr_append_cstr(g, ";\n");
            if (g_memchk) {
                size_t total = off + len + 1;   /* bytes that must fit, text + NUL */
                if (total < off) {
                    zt_error("mem.write %s: offset too large", name);
                    return 1;
                }
                dstr_appendf(g, "      if (zt_hn[%d] < %zu) ztm_abort();\n", h, total);
            }
            dstr_appendf(g, "      memcpy(zt_h[%d] + %zu, zs, %zu); }\n", h, off, len + 1);
            break;
        }
        case K_MEMSHOW:
            dstr_appendf(g, "    if (!zt_h[%d]) { fputs(\"E: mem.show: handle '%s' was never allocated\\n\", stderr); return 1; }\n", h, name);
            dstr_appendf(g, "    { const char *zp = zt_h[%d]; for (size_t zk = 0; zp[zk]; zk++) putchar(zp[zk]); fflush(stdout); }\n", h);
            break;
        default:
            break;
    }
    return 0;
}

static int run_mem(ExecCtx *ctx, StmtKind k, const char *name, const char *num,
                   const char *text) {
    if (ctx->verbose)
        fprintf(stderr, "[mem] %s\n", name);
    switch (k) {
        case K_MEMALLOC: return mem_do_alloc(ctx, name, num);
        case K_MEMFREE:  return mem_do_free(ctx, name);
        case K_MEMWRITE: return mem_do_write(ctx, name, num, text);
        case K_MEMSHOW:  return mem_do_show(ctx, name);
        default:         return 0;
    }
}

static int exec_mem(ExecCtx *ctx, Stmt *s) {
    char *name = subst_vars(s->mem.name, *ctx->vars);
    char *num  = s->mem.num ? subst_vars(s->mem.num, *ctx->vars) : NULL;
    char *text = NULL;
    if (s->mem.text) {
        char *t = subst_vars(s->mem.text, *ctx->vars);
        text = unescape_dup(t);
        free(t);
    }
    int rc = ctx->dry_run ? gen_mem(ctx, s->kind, name, num, text)
                          : run_mem(ctx, s->kind, name, num, text);
    free(name);
    free(num);
    free(text);
    return rc;
}

static int exec_stmt(ExecCtx *ctx, Stmt *s) {
    switch (s->kind) {
        case K_DEFINE: {
            char *val = subst_vars(s->define.value, *ctx->vars);
            var_set(ctx->vars, s->define.name, val);
            if (ctx->verbose)
                fprintf(stderr, "[define] %s = %s\n", s->define.name, val);
            free(val);
            return 0;
        }
        case K_IF: {
            if (ctx->dry_run && cond_is_runtime(ctx, &s->cond))
                return gen_runtime_if(ctx, s);
            bool ok;
            if (s->cond.kind == COND_ARG_PASSED || s->cond.kind == COND_ARG_UNDEF) {
                int usage_rc = 0;
                ok = eval_arg_cond(ctx, &s->cond, &usage_rc);
                if (usage_rc != 0) return usage_rc;
            } else {
                ok = eval_cond(&s->cond, *ctx->vars, ctx->rvars);
            }
            if (ctx->verbose) {
                if (s->cond.kind == COND_ARG_PASSED) {
                    fprintf(stderr, "[if] argument %s is passed%s -> %s\n",
                            s->cond.argname, s->cond.need_ea ? " with %ea%" : "",
                            ok ? "true" : "false");
                } else if (s->cond.kind == COND_ARG_UNDEF) {
                    fprintf(stderr, "[if] argument is not defined -> %s\n",
                            ok ? "true" : "false");
                } else {
                    const char *subj_desc = (s->cond.subj == SUBJ_READFILE)
                        ? s->cond.path : s->cond.var;
                    const char *subj_label = (s->cond.subj == SUBJ_READFILE)
                        ? "read_file " : "";
                    if (s->cond.kind == COND_EMPTYFILE) {
                        fprintf(stderr, "[if] %s%s %s an empty file -> %s\n",
                                subj_label, subj_desc, s->cond.is_is ? "is" : "is not",
                                ok ? "true" : "false");
                    } else {
                        fprintf(stderr, "[if] %s%s %s -> %s\n",
                                subj_label, subj_desc, s->cond.is_is ? "is" : "is not",
                                ok ? "true" : "false");
                    }
                }
            }
            return exec_stmt_list(ctx, ok ? s->cond.then_branch
                                          : s->cond.else_branch);
        }
        case K_EXEC: {
            char *code = subst_vars(s->exec.code, *ctx->vars);
            if (ctx->dry_run) {
                int grc = 0;
                if (g_ztv == ZTV_ZTSL26) {
                    grc = gen_exec26(ctx, code, s->exec.is_shell, s->exec.silent);
                } else if (s->exec.is_shell) {
                    dstr_append_cstr(&ctx->gen_c, "    if (system(");
                    c_escape_append(&ctx->gen_c, code);
                    dstr_append_cstr(&ctx->gen_c, ") != 0) return 1;\n");
                } else {
                    dstr_append_cstr(&ctx->gen_c, "    if (do_exec(");
                    c_escape_append(&ctx->gen_c, code);
                    dstr_append_cstr(&ctx->gen_c, ") != 0) return 1;\n");
                }
                free(code);
                return grc;
            }
            if (ctx->verbose) {
                fprintf(stderr, "[%s%s] %s\n",
                        s->exec.is_shell ? "shell" : "exec",
                        s->exec.silent ? ".silent" : "", code);
            }
            int rc;
            if (g_ztv == ZTV_ZTSL26) {
                rc = run_cmd26(ctx, code, s->exec.is_shell, s->exec.silent);
                char rbuf[16];
                snprintf(rbuf, sizeof(rbuf), "%d", rc);
                var_set(ctx->vars, "result", rbuf);
                if (s->exec.silent) rc = 0;   /* the program checks 'result' itself */
            } else if (s->exec.is_shell) {
                rc = run_shell(code);
            } else {
                rc = run_exec(code);
            }
            free(code);
            return rc;
        }
        case K_SHOW: {
            char *code = subst_vars(s->show.code, *ctx->vars);
            if (ctx->dry_run) {
                if (g_ztv == ZTV_ZTSL26) {
                    dstr_append_cstr(&ctx->gen_c, "    zt_show(");
                    c_escape_append(&ctx->gen_c, code);
                    dstr_append_cstr(&ctx->gen_c, ");\n");
                } else {
                    dstr_append_cstr(&ctx->gen_c, "    fputs(");
                    c_escape_append(&ctx->gen_c, code);
                    dstr_append_cstr(&ctx->gen_c, ", stdout); fflush(stdout);\n");
                }
            } else if (g_ztv == ZTV_ZTSL26) {
                char *e = expand_args(ctx->args, ctx->nargs, ctx->rvars, code, false);
                fputs(e, stdout);
                fflush(stdout);
                free(e);
            } else {
                fputs(code, stdout);
                fflush(stdout);
            }
            free(code);
            return 0;
        }
        case K_DELETE: {
            char *path = subst_vars(s->delfile.path, *ctx->vars);
            if (ctx->dry_run) {
                dstr_append_cstr(&ctx->gen_c, "    if (remove(");
                c_escape_append(&ctx->gen_c, path);
                dstr_append_cstr(&ctx->gen_c,
                    ") != 0 && errno != ENOENT) return 1;\n");
                free(path);
                return 0;
            }
            if (ctx->verbose) fprintf(stderr, "[delete_file] %s\n", path);
            errno = 0;
            int rc = 0;
            if (remove(path) != 0 && errno != ENOENT) {
                zt_error("delete_file %s: %s", path, strerror(errno));
                rc = 1;
            }
            free(path);
            return rc;
        }
        case K_CREATE: {
            char *path = subst_vars(s->mkfile.path, *ctx->vars);
            if (ctx->dry_run) {
                dstr_append_cstr(&ctx->gen_c, "    { FILE *ztc_f = fopen(");
                c_escape_append(&ctx->gen_c, path);
                dstr_append_cstr(&ctx->gen_c,
                    ", \"a\"); if (!ztc_f) return 1; fclose(ztc_f); }\n");
                free(path);
                return 0;
            }
            if (ctx->verbose) fprintf(stderr, "[create_file] %s\n", path);
            FILE *f = fopen(path, "a");
            if (!f) {
                zt_error("create_file %s: %s", path, strerror(errno));
                free(path);
                return 1;
            }
            fclose(f);
            free(path);
            return 0;
        }
        case K_WRITE:
        case K_APPEND: {
            char *path = subst_vars(s->writefile.path, *ctx->vars);
            char *content = subst_vars(s->writefile.code, *ctx->vars);
            const char *mode = (s->kind == K_WRITE) ? "w" : "a";
            if (ctx->dry_run) {
                dstr_append_cstr(&ctx->gen_c, "    { FILE *ztc_f = fopen(");
                c_escape_append(&ctx->gen_c, path);
                dstr_append_cstr(&ctx->gen_c, ", ");
                c_escape_append(&ctx->gen_c, mode);
                dstr_append_cstr(&ctx->gen_c,
                    "); if (!ztc_f) return 1; fputs(");
                c_escape_append(&ctx->gen_c, content);
                dstr_append_cstr(&ctx->gen_c, ", ztc_f); fclose(ztc_f); }\n");
                free(path);
                free(content);
                return 0;
            }
            if (ctx->verbose)
                fprintf(stderr, "[%s] %s\n",
                        s->kind == K_WRITE ? "write_on_file" : "append_file",
                        path);
            FILE *f = fopen(path, mode);
            if (!f) {
                zt_error("%s %s: %s",
                        s->kind == K_WRITE ? "write_on_file" : "append_file",
                        path, strerror(errno));
                free(path);
                free(content);
                return 1;
            }
            fputs(content, f);
            fclose(f);
            free(path);
            free(content);
            return 0;
        }
        case K_CCOMPAT: {
            if (ctx->dry_run) {
                char *code = subst_vars(s->ccompat.code, *ctx->vars);
                dstr_append_cstr(&ctx->gen_c, "    {\n");
                dstr_append_cstr(&ctx->gen_c, code);
                dstr_append_cstr(&ctx->gen_c, "\n    }\n");
                free(code);
                return 0;
            }
            zt_warn("ccompat requires -e/-o (C transpile) mode; "
                    "skipping raw C block in interpreted run");
            return 0;
        }
        case K_FLOATCALC: {
            char *lhs_s = subst_vars(s->floatcalc.lhs_raw, *ctx->vars);
            char *rhs_s = subst_vars(s->floatcalc.rhs_raw, *ctx->vars);
            char *result = compute_float_calc(s->floatcalc.width, lhs_s,
                    s->floatcalc.op, rhs_s);
            free(lhs_s);
            free(rhs_s);
            if (!result) {
                zt_error("float%d_calculate: division by zero",
                        s->floatcalc.width);
                return 1;
            }
            var_set(ctx->vars, s->floatcalc.varname, result);
            if (ctx->verbose)
                fprintf(stderr, "[float%d_calculate] %s = %s\n",
                        s->floatcalc.width, s->floatcalc.varname, result);
            free(result);
            return 0;
        }
        case K_RUNFUNC: {
            if (ctx->dry_run) {
                int fi = func_index(ctx->prog, s->runfunc.name);
                if (fi < 0) {
                    zt_error("run.func: no such function: %s", s->runfunc.name);
                    return 1;
                }
                dstr_appendf(&ctx->gen_c,
                    "    { int zr = zf_%d(); ZTM_CHK(); if (zr != 0) return zr; }\n", fi);
                return 0;
            }
            Func *fn = find_func(ctx->prog, s->runfunc.name);
            if (!fn) {
                zt_error("run.func: no such function: %s", s->runfunc.name);
                return 1;
            }
            if (ctx->depth >= 64) {
                zt_error("run.func %s: recursion too deep", s->runfunc.name);
                return 1;
            }
            if (ctx->verbose) fprintf(stderr, "[run.func] %s\n", fn->name);
            ctx->depth++;
            int rc = exec_stmt_list(ctx, fn->body);
            ctx->depth--;
            return rc;
        }
        case K_MEMALLOC:
        case K_MEMFREE:
        case K_MEMWRITE:
        case K_MEMSHOW:
            return exec_mem(ctx, s);
        case K_LIBCALL: {
            const LibStmt *ls = &ctx->prog->lstmts[s->libcall.idx];
            int n = s->libcall.nargs;
            if (ctx->dry_run) {
                /* the call happens when the compiled program runs; @vars known
                 * now are substituted, %a%/%ea% and library results are left
                 * for run time */
                char *sym = mod_symbol(ctx->prog->mods[ls->mod]);
                dstring *g = &ctx->gen_c;
                dstr_append_cstr(g, "    { const char *za[] = {");
                for (int i = 0; i < n; i++) {
                    char *t = subst_vars(s->libcall.args[i], *ctx->vars);
                    c_escape_append(g, t);
                    dstr_append_cstr(g, ", ");
                    free(t);
                }
                dstr_appendf(g, "NULL};\n    if (zt_libcall(&%s, ", sym);
                c_escape_append(g, ls->name);
                dstr_appendf(g, ", za, %d, ", n);
                if (s->libcall.varname) c_escape_append(g, s->libcall.varname);
                else dstr_append_cstr(g, "NULL");
                dstr_append_cstr(g, ") != 0) return 1; }\n");
                free(sym);
                return 0;
            }
            char **av = xmalloc(sizeof(char *) * ((size_t)n + 1));
            for (int i = 0; i < n; i++) {
                char *t = subst_vars(s->libcall.args[i], *ctx->vars);
                av[i] = expand_args(ctx->args, ctx->nargs, ctx->rvars, t, false);
                free(t);
            }
            av[n] = NULL;
            if (ctx->verbose) fprintf(stderr, "[lib] %s (%d args)\n", ls->name, n);
            char *out = NULL;
            int rc = ls->fn(n, (const char *const *)av, &out);
            free_args(av);
            if (rc != 0) {
                zt_error("%s: %s", ls->name, out ? out : "failed");
                free(out);
                return 1;
            }
            if (s->libcall.varname) {
                var_set(&ctx->rvars, s->libcall.varname, out ? out : "");
            } else if (out) {
                fputs(out, stdout);
                fputc('\n', stdout);
                fflush(stdout);
            }
            free(out);
            return 0;
        }
    }
    return 0;
}

static char *sha256_hex(const char *data, size_t len);

static void serialize_stmt(dstring *out, Stmt *s);

static void serialize_stmt_list(dstring *out, Stmt *s) {
    for (Stmt *cur = s; cur; cur = cur->next) {
        serialize_stmt(out, cur);
    }
}

static void serialize_stmt(dstring *out, Stmt *s) {
    if (!s) return;
    switch (s->kind) {
        case K_DEFINE:
            dstr_append_cstr(out, "DEFINE ");
            dstr_append_cstr(out, s->define.name);
            dstr_append_cstr(out, " AS ");
            dstr_append_cstr(out, s->define.value);
            dstr_append_char(out, '\n');
            break;
        case K_IF:
            dstr_append_cstr(out, "IF ");
            if (s->cond.subj == SUBJ_READFILE) {
                dstr_append_cstr(out, "READFILE ");
                dstr_append_cstr(out, s->cond.path);
            } else {
                if (s->cond.kind == COND_ARG_PASSED) {
                    dstr_append_cstr(out, "ARG ");
                    dstr_append_cstr(out, s->cond.argname);
                    dstr_append_cstr(out, s->cond.need_ea ? " WITHEA" : "");
                } else if (s->cond.kind == COND_ARG_UNDEF) {
                    dstr_append_cstr(out, "ARGUNDEF");
                } else {
                    dstr_append_cstr(out, s->cond.var);
                }
            }
            if (s->cond.kind == COND_EMPTYFILE) {
                dstr_append_cstr(out, s->cond.is_is ? " ISEMPTYFILE" : " ISNOTEMPTYFILE");
                dstr_append_cstr(out, " THEN\n");
            } else {
                dstr_append_cstr(out, s->cond.is_is ? " IS " : " ISNOT ");
                for (size_t i = 0; i < s->cond.nvalues; i++) {
                    if (i > 0) dstr_append_cstr(out, " OR ");
                    dstr_append_cstr(out, s->cond.values[i]);
                }
                dstr_append_cstr(out, " THEN\n");
            }
            serialize_stmt_list(out, s->cond.then_branch);
            if (s->cond.else_branch) {
                dstr_append_cstr(out, "ELSE\n");
                serialize_stmt_list(out, s->cond.else_branch);
            }
            dstr_append_cstr(out, "ENDIF\n");
            break;
        case K_EXEC:
            dstr_append_cstr(out, s->exec.silent ? "EXECSILENT " : "EXEC ");
            dstr_append_cstr(out, s->exec.is_shell ? "SHELL\n" : "EXECP\n");
            dstr_append_cstr(out, s->exec.code);
            dstr_append_char(out, '\n');
            break;
        case K_SHOW:
            dstr_append_cstr(out, "SHOW\n");
            dstr_append_cstr(out, s->show.code);
            dstr_append_char(out, '\n');
            break;
        case K_DELETE:
            dstr_append_cstr(out, "DELETE ");
            dstr_append_cstr(out, s->delfile.path);
            dstr_append_char(out, '\n');
            break;
        case K_CREATE:
            dstr_append_cstr(out, "CREATE ");
            dstr_append_cstr(out, s->mkfile.path);
            dstr_append_char(out, '\n');
            break;
        case K_WRITE:
        case K_APPEND:
            dstr_append_cstr(out, s->kind == K_WRITE ? "WRITE " : "APPEND ");
            dstr_append_cstr(out, s->writefile.path);
            dstr_append_char(out, '\n');
            dstr_append_cstr(out, s->writefile.code);
            dstr_append_char(out, '\n');
            break;
        case K_CCOMPAT:
            dstr_append_cstr(out, "CCOMPAT\n");
            dstr_append_cstr(out, s->ccompat.code);
            dstr_append_char(out, '\n');
            break;
        case K_FLOATCALC: {
            char widthbuf[16];
            snprintf(widthbuf, sizeof(widthbuf), "%d", s->floatcalc.width);
            dstr_append_cstr(out, "FLOATCALC float");
            dstr_append_cstr(out, widthbuf);
            dstr_append_char(out, ' ');
            dstr_append_cstr(out, s->floatcalc.lhs_raw);
            dstr_append_char(out, ' ');
            dstr_append_char(out, s->floatcalc.op);
            dstr_append_char(out, ' ');
            dstr_append_cstr(out, s->floatcalc.rhs_raw);
            dstr_append_cstr(out, " AS ");
            dstr_append_cstr(out, s->floatcalc.varname);
            dstr_append_char(out, '\n');
            break;
        }
        case K_LIBCALL:
            dstr_appendf(out, "LIBCALL %zu", s->libcall.idx);
            for (int i = 0; i < s->libcall.nargs; i++) {
                dstr_append_char(out, ' ');
                dstr_append_cstr(out, s->libcall.args[i]);
            }
            if (s->libcall.varname) {
                dstr_append_cstr(out, " AS ");
                dstr_append_cstr(out, s->libcall.varname);
            }
            dstr_append_char(out, '\n');
            break;
        case K_RUNFUNC:
            dstr_append_cstr(out, "RUNFUNC ");
            dstr_append_cstr(out, s->runfunc.name);
            dstr_append_char(out, '\n');
            break;
        case K_MEMALLOC:
        case K_MEMFREE:
        case K_MEMWRITE:
        case K_MEMSHOW:
            dstr_appendf(out, "MEM%d %s %s %s\n", (int)s->kind, s->mem.name,
                         s->mem.num ? s->mem.num : "", s->mem.text ? s->mem.text : "");
            break;
    }
}

static char *compute_func_hash(const char *global_hash, Func *fn) {
    dstring buf;
    dstr_init(&buf);
    dstr_append_cstr(&buf, "GH=");
    dstr_append_cstr(&buf, global_hash);
    dstr_append_cstr(&buf, "\nFN=");
    dstr_append_cstr(&buf, fn->name);
    dstr_append_cstr(&buf, "\nBODY:\n");
    serialize_stmt_list(&buf, fn->body);
    char *h = sha256_hex(buf.data, buf.len);
    dstr_free(&buf);
    return h;
}

static char *sha256_hex(const char *data, size_t len) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256((const unsigned char *)data, len, digest);
    char *out = xmalloc(SHA256_DIGEST_LENGTH * 2 + 1);
    for (int i = 0; i < SHA256_DIGEST_LENGTH; i++)
        snprintf(out + i * 2, 3, "%02x", digest[i]);
    return out;
}

static char *strip_comments(const char *src) {
    dstring out;
    dstr_init(&out);
    const char *p = src;
    bool in_fence = false;
    bool line_has_code = false;
    while (*p) {
        if (*p == '`' && p[1] == '`' && p[2] == '`') {
            in_fence = !in_fence;
            dstr_append_cstr(&out, "```");
            p += 3;
            continue;
        }
        if (!in_fence && *p == '#') {
            
            bool whole_line_comment = !line_has_code;
            
            while (*p && *p != '\n') p++;
            if (whole_line_comment) {
                
                if (*p == '\n') p++;
            } else {
                
                while (out.len > 0 && (out.data[out.len-1] == ' ' ||
                                       out.data[out.len-1] == '\t')) {
                    out.len--;
                }
                out.data[out.len] = '\0';
                if (*p == '\n') {
                    dstr_append_char(&out, '\n');
                    p++;
                }
            }
            line_has_code = false;
            continue;
        }
        if (*p == '\n') {
            line_has_code = false;
        } else if (!isspace((unsigned char)*p)) {
            line_has_code = true;
        }
        dstr_append_char(&out, *p);
        p++;
    }
    return out.data;
}

static char *read_stored_hash(const char *hashdir, const char *name) {
    char path[1024];
    snprintf(path, sizeof(path), "%s/%s.sha256", hashdir, name);
    FILE *f = fopen(path, "r");
    if (!f) return NULL;
    char buf[128];
    size_t n = fread(buf, 1, sizeof(buf) - 1, f);
    fclose(f);
    buf[n] = '\0';

    if (n == 0) return xstrdup("");

    char *end = buf + n - 1;
    while (end >= buf && isspace((unsigned char)*end)) *end-- = '\0';
    return xstrdup(buf);
}

static void write_stored_hash(const char *hashdir, const char *name,
                              const char *hash) {
    char path[1024];
    snprintf(path, sizeof(path), "%s/%s.sha256", hashdir, name);
    FILE *f = fopen(path, "w");
    if (!f) {
        zt_error("cannot write hash file %s: %s",
                path, strerror(errno));
        return;
    }
    fprintf(f, "%s\n", hash);
    fclose(f);
}

static const char *const ZTM_RT_SRC[] = {
    "/* ---- ztc libmemchk runtime (built into ztc, enabled with -libmemchk) ----\n",
    " * Every allocation gets its own mapping with a PROT_NONE guard page on each\n",
    " * side. The block ends right at the upper guard page, so an overflow faults\n",
    " * immediately; freed blocks are kept mapped as PROT_NONE, so a use-after-free\n",
    " * or a double free is caught. Leaks are checked at scope end / program end. */\n",
    "typedef struct ztm_blk {\n",
    "    char *base;\n",
    "    size_t maplen;\n",
    "    char *user;\n",
    "    size_t size;\n",
    "    size_t rn;\n",
    "    unsigned long seq;\n",
    "    int freed;\n",
    "    struct ztm_blk *next;\n",
    "} ztm_blk;\n",
    "\n",
    "static ztm_blk *ztm_head;\n",
    "static unsigned long ztm_seq;\n",
    "\n",
    "static size_t ztm_pg(void) {\n",
    "    static size_t pg;\n",
    "    if (!pg) pg = (size_t)sysconf(_SC_PAGESIZE);\n",
    "    return pg;\n",
    "}\n",
    "\n",
    "__attribute__((noreturn)) static void ztm_abort(void) {\n",
    "    volatile long long edge = 2147483648LL; /* INT32_MAX + 1 */\n",
    "    long long r = edge + 1;\n",
    "    char buf[80];\n",
    "    size_t n = 0;\n",
    "    const char *pre = \"E: Value Out of Bounds (\";\n",
    "    char dig[24];\n",
    "    int d = 0;\n",
    "    unsigned long long u = (unsigned long long)r;\n",
    "    ssize_t wr;\n",
    "    while (*pre) buf[n++] = *pre++;\n",
    "    do { dig[d++] = (char)('0' + u % 10); u /= 10; } while (u);\n",
    "    while (d) buf[n++] = dig[--d];\n",
    "    buf[n++] = ')';\n",
    "    buf[n++] = '\\n';\n",
    "    fflush(stdout);\n",
    "    wr = write(2, buf, n);\n",
    "    (void)wr;\n",
    "    signal(SIGSEGV, SIG_DFL);\n",
    "    raise(SIGSEGV);\n",
    "    _exit(139);\n",
    "}\n",
    "\n",
    "static ztm_blk *ztm_find(const void *p) {\n",
    "    for (ztm_blk *b = ztm_head; b; b = b->next)\n",
    "        if (b->user == (const char *)p) return b;\n",
    "    return NULL;\n",
    "}\n",
    "\n",
    "static int ztm_canary_ok(const ztm_blk *b) {\n",
    "    for (size_t i = b->size; i < b->rn; i++)\n",
    "        if ((unsigned char)b->user[i] != 0xA5) return 0;\n",
    "    return 1;\n",
    "}\n",
    "\n",
    "static void *ztm_malloc(size_t n) {\n",
    "    size_t pg = ztm_pg();\n",
    "    if (n > ((size_t)-1) / 4) return NULL;\n",
    "    size_t dat = ((n ? n : 1) + pg - 1) / pg * pg;\n",
    "    size_t total = dat + 2 * pg;\n",
    "    char *base = mmap(NULL, total, PROT_READ | PROT_WRITE,\n",
    "                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);\n",
    "    if (base == (char *)MAP_FAILED) return NULL;\n",
    "    if (mprotect(base, pg, PROT_NONE) != 0 ||\n",
    "        mprotect(base + pg + dat, pg, PROT_NONE) != 0) {\n",
    "        munmap(base, total);\n",
    "        return NULL;\n",
    "    }\n",
    "    size_t rn = (n + 15) & ~(size_t)15;\n",
    "    if (rn == 0) rn = 16;\n",
    "    char *user = base + pg + dat - rn;\n",
    "    for (size_t i = n; i < rn; i++) user[i] = (char)0xA5;\n",
    "    ztm_blk *b = malloc(sizeof *b);\n",
    "    if (!b) { munmap(base, total); return NULL; }\n",
    "    b->base = base;\n",
    "    b->maplen = total;\n",
    "    b->user = user;\n",
    "    b->size = n;\n",
    "    b->rn = rn;\n",
    "    b->seq = ++ztm_seq;\n",
    "    b->freed = 0;\n",
    "    b->next = ztm_head;\n",
    "    ztm_head = b;\n",
    "    return user;\n",
    "}\n",
    "\n",
    "static void ztm_free(void *p) {\n",
    "    if (!p) return;\n",
    "    ztm_blk *b = ztm_find(p);\n",
    "    if (!b) ztm_abort();             /* invalid free */\n",
    "    if (b->freed) ztm_abort();       /* double free */\n",
    "    if (!ztm_canary_ok(b)) ztm_abort(); /* small overflow into the slack */\n",
    "    mprotect(b->base + ztm_pg(), b->maplen - 2 * ztm_pg(), PROT_NONE);\n",
    "    b->freed = 1;\n",
    "}\n",
    "\n",
    "static void *ztm_calloc(size_t nm, size_t sz) {\n",
    "    if (sz && nm > ((size_t)-1) / sz) return NULL;\n",
    "    return ztm_malloc(nm * sz); /* fresh anonymous pages are zeroed */\n",
    "}\n",
    "\n",
    "static void *ztm_realloc(void *p, size_t n) {\n",
    "    if (!p) return ztm_malloc(n);\n",
    "    ztm_blk *b = ztm_find(p);\n",
    "    if (!b || b->freed) ztm_abort();\n",
    "    void *q = ztm_malloc(n);\n",
    "    if (!q) return NULL;\n",
    "    memcpy(q, p, b->size < n ? b->size : n);\n",
    "    ztm_free(p);\n",
    "    return q;\n",
    "}\n",
    "\n",
    "static char *ztm_strdup(const char *s) {\n",
    "    size_t l = strlen(s) + 1;\n",
    "    char *q = ztm_malloc(l);\n",
    "    if (q) memcpy(q, s, l);\n",
    "    return q;\n",
    "}\n",
    "\n",
    "static void ztm_segv(int sig, siginfo_t *si, void *uc) {\n",
    "    (void)sig;\n",
    "    (void)uc;\n",
    "    const char *a = (const char *)si->si_addr;\n",
    "    for (ztm_blk *b = ztm_head; b; b = b->next)\n",
    "        if (a >= b->base && a < b->base + b->maplen) ztm_abort();\n",
    "    /* not ours: the handler was installed with SA_RESETHAND, so returning\n",
    "     * re-runs the fault with the default action */\n",
    "}\n",
    "\n",
    "static void ztm_init(void) {\n",
    "    struct sigaction sa;\n",
    "    memset(&sa, 0, sizeof sa);\n",
    "    sa.sa_sigaction = ztm_segv;\n",
    "    sa.sa_flags = SA_SIGINFO | SA_RESETHAND | SA_NODEFER;\n",
    "    sigemptyset(&sa.sa_mask);\n",
    "    sigaction(SIGSEGV, &sa, NULL);\n",
    "}\n",
    "\n",
    "/* checkpoint (after every run.func): a live block whose slack bytes changed\n",
    " * was overflowed */\n",
    "static void ztm_check(void) {\n",
    "    for (ztm_blk *b = ztm_head; b; b = b->next)\n",
    "        if (!b->freed && !ztm_canary_ok(b)) ztm_abort();\n",
    "}\n",
    "\n",
    "/* end of a successful run: anything still allocated is a leak */\n",
    "static void ztm_leaks(void) {\n",
    "    ztm_check();\n",
    "    for (ztm_blk *b = ztm_head; b; b = b->next)\n",
    "        if (!b->freed) ztm_abort();\n",
    "}\n",
    NULL
};

static const char *const ZT26_RT_SRC[] = {
    "/* ---- ZTSL 26 runtime: program arguments (%a%, %ea%), exec, result ---- */\n",
    "static int zt_argc;\n",
    "static char **zt_argv;\n",
    "static int zt_handled, zt_usage_err, zt_result;\n",
    "\n",
    "typedef struct { char *p; size_t n, cap; } zt_buf;\n",
    "\n",
    "static void zt_bput(zt_buf *b, const char *s, size_t k) {\n",
    "    if (b->n + k + 1 > b->cap) {\n",
    "        size_t nc = b->cap ? b->cap : 64;\n",
    "        while (nc < b->n + k + 1) nc *= 2;\n",
    "        char *np = realloc(b->p, nc);\n",
    "        if (!np) { fputs(\"E: out of memory\\n\", stderr); exit(1); }\n",
    "        b->p = np;\n",
    "        b->cap = nc;\n",
    "    }\n",
    "    memcpy(b->p + b->n, s, k);\n",
    "    b->n += k;\n",
    "    b->p[b->n] = '\\0';\n",
    "}\n",
    "\n",
    "/* ---- runtime variables: results of library statements (\"as variable\") ---- */\n",
    "typedef struct zt_var { char *name; char *val; struct zt_var *next; } zt_var;\n",
    "static zt_var *zt_vars;\n",
    "\n",
    "static void zt_setvar(const char *name, const char *val) {\n",
    "    for (zt_var *v = zt_vars; v; v = v->next) {\n",
    "        if (strcasecmp(v->name, name) == 0) {\n",
    "            char *nv = strdup(val);\n",
    "            if (!nv) { fputs(\"E: out of memory\\n\", stderr); exit(1); }\n",
    "            free(v->val);\n",
    "            v->val = nv;\n",
    "            return;\n",
    "        }\n",
    "    }\n",
    "    zt_var *v = malloc(sizeof *v);\n",
    "    if (!v) { fputs(\"E: out of memory\\n\", stderr); exit(1); }\n",
    "    v->name = strdup(name);\n",
    "    v->val = strdup(val);\n",
    "    if (!v->name || !v->val) { fputs(\"E: out of memory\\n\", stderr); exit(1); }\n",
    "    v->next = zt_vars;\n",
    "    zt_vars = v;\n",
    "}\n",
    "\n",
    "static const char *zt_getvar(const char *name) {\n",
    "    for (zt_var *v = zt_vars; v; v = v->next)\n",
    "        if (strcasecmp(v->name, name) == 0) return v->val;\n",
    "    return NULL;\n",
    "}\n",
    "\n",
    "static int zt_var_eq(const char *name, const char *val) {\n",
    "    const char *v = zt_getvar(name);\n",
    "    return strcmp(v ? v : \"\", val) == 0;\n",
    "}\n",
    "\n",
    "/* ---- ZTSL module ABI (what a def_mod library exports) ---- */\n",
    "typedef int (*ztsl_stmt_fn)(int argc, const char *const *argv, char **out);\n",
    "typedef struct { const char *name; ztsl_stmt_fn fn; } ztsl_stmt;\n",
    "typedef struct { unsigned abi; const char *name; const ztsl_stmt *stmts; } ztsl_module;\n",
    "\n",
    "/* %a% = first program argument, %ea% = the one after it.\n",
    " * quote != 0: values are single-quoted for sh (no shell injection). */\n",
    "static char *zt_expand(const char *t, int quote) {\n",
    "    zt_buf b = {NULL, 0, 0};\n",
    "    zt_bput(&b, \"\", 0);\n",
    "    while (*t) {\n",
    "        const char *val = NULL;\n",
    "        size_t adv = 0;\n",
    "        if (strncmp(t, \"%ea%\", 4) == 0) { val = zt_argc > 2 ? zt_argv[2] : \"\"; adv = 4; }\n",
    "        else if (strncmp(t, \"%a%\", 3) == 0) { val = zt_argc > 1 ? zt_argv[1] : \"\"; adv = 3; }\n",
    "        if (!val && *t == '@' && (isalpha((unsigned char)t[1]) || t[1] == '_')) {\n",
    "            const char *q = t + 1;\n",
    "            while (isalnum((unsigned char)*q) || *q == '_') q++;\n",
    "            char nm[128];\n",
    "            size_t nl = (size_t)(q - t - 1);\n",
    "            if (nl < sizeof nm) {\n",
    "                memcpy(nm, t + 1, nl);\n",
    "                nm[nl] = '\\0';\n",
    "                const char *lv = zt_getvar(nm);\n",
    "                if (lv) { val = lv; adv = (size_t)(q - t); }\n",
    "            }\n",
    "        }\n",
    "        if (!val) { zt_bput(&b, t, 1); t++; continue; }\n",
    "        t += adv;\n",
    "        if (!quote) { zt_bput(&b, val, strlen(val)); continue; }\n",
    "        zt_bput(&b, \"'\", 1);\n",
    "        for (; *val; val++) {\n",
    "            if (*val == '\\'') zt_bput(&b, \"'\\\\''\", 4);\n",
    "            else zt_bput(&b, val, 1);\n",
    "        }\n",
    "        zt_bput(&b, \"'\", 1);\n",
    "    }\n",
    "    return b.p;\n",
    "}\n",
    "\n",
    "static void zt_show(const char *t) {\n",
    "    char *s = zt_expand(t, 0);\n",
    "    fputs(s, stdout);\n",
    "    fflush(stdout);\n",
    "    free(s);\n",
    "}\n",
    "\n",
    "static int zt_status(int st) {\n",
    "    if (WIFEXITED(st)) return WEXITSTATUS(st);\n",
    "    if (WIFSIGNALED(st)) return 128 + WTERMSIG(st);\n",
    "    return 0;\n",
    "}\n",
    "\n",
    "static int zt_run_exec(const char *const *tmpl, int silent) {\n",
    "    size_t n = 0;\n",
    "    while (tmpl[n]) n++;\n",
    "    char **av = calloc(n + 1, sizeof *av);\n",
    "    if (!av) return -1;\n",
    "    for (size_t i = 0; i < n; i++) av[i] = zt_expand(tmpl[i], 0);\n",
    "    fflush(NULL);\n",
    "    pid_t pid = fork();\n",
    "    int st = 0, rc;\n",
    "    if (pid == 0) {\n",
    "        if (silent) {\n",
    "            int fd = open(\"/dev/null\", O_WRONLY);\n",
    "            if (fd >= 0) { dup2(fd, 1); dup2(fd, 2); close(fd); }\n",
    "        }\n",
    "        execvp(av[0], av);\n",
    "        fprintf(stderr, \"E: execvp(%s) failed: %s\\n\", av[0], strerror(errno));\n",
    "        _exit(127);\n",
    "    }\n",
    "    if (pid < 0) {\n",
    "        rc = -1;\n",
    "    } else {\n",
    "        pid_t w;\n",
    "        do { w = waitpid(pid, &st, 0); } while (w < 0 && errno == EINTR);\n",
    "        rc = w < 0 ? -1 : zt_status(st);\n",
    "    }\n",
    "    for (size_t i = 0; i < n; i++) free(av[i]);\n",
    "    free(av);\n",
    "    return rc;\n",
    "}\n",
    "\n",
    "static int zt_run_shell(const char *tmpl, int silent) {\n",
    "    char *cmd = zt_expand(tmpl, 1);\n",
    "    zt_buf full = {NULL, 0, 0};\n",
    "    zt_bput(&full, \"\", 0);\n",
    "    if (silent) {\n",
    "        zt_bput(&full, \"( \", 2);\n",
    "        zt_bput(&full, cmd, strlen(cmd));\n",
    "        zt_bput(&full, \"\\n) >/dev/null 2>&1\", 18);\n",
    "    } else {\n",
    "        zt_bput(&full, cmd, strlen(cmd));\n",
    "    }\n",
    "    fflush(NULL);\n",
    "    int st = system(full.p);\n",
    "    free(full.p);\n",
    "    free(cmd);\n",
    "    return st == -1 ? -1 : zt_status(st);\n",
    "}\n",
    "\n",
    "static int zt_res_eq(const char *v) {\n",
    "    char b[24];\n",
    "    snprintf(b, sizeof b, \"%d\", zt_result);\n",
    "    return strcmp(b, v) == 0;\n",
    "}\n",
    "\n",
    "static int zt_arg_passed(const char *name, int need_ea) {\n",
    "    if (zt_argc < 2 || strcmp(zt_argv[1], name) != 0) return 0;\n",
    "    zt_handled = 1;\n",
    "    if (need_ea && zt_argc < 3) {\n",
    "        fprintf(stderr, \"E: command '%s' requires an argument\\n\", name);\n",
    "        zt_usage_err = 1;\n",
    "        return 0;\n",
    "    }\n",
    "    return 1;\n",
    "}\n",
    "\n",
    "static int zt_arg_undef(void) {\n",
    "    if (zt_handled) return 0;\n",
    "    if (zt_argc >= 2) {\n",
    "        for (size_t i = 0; zt_defined[i]; i++)\n",
    "            if (strcmp(zt_argv[1], zt_defined[i]) == 0) return 0;\n",
    "    }\n",
    "    zt_handled = 1;\n",
    "    return 1;\n",
    "}\n",
    "\n",
    "/* Calls library statement 'name' of module 'm'. Arguments are expanded at run\n",
    " * time (%a%, %ea%, @var). The library's 'out' string is malloc'd by the\n",
    " * library: stored in 'var' when given, otherwise printed. */\n",
    "static int zt_libcall(const ztsl_module *m, const char *name,\n",
    "                      const char *const *tmpl, int n, const char *var) {\n",
    "    ztsl_stmt_fn fn = NULL;\n",
    "    for (const ztsl_stmt *e = m->stmts; e->name; e++)\n",
    "        if (strcmp(e->name, name) == 0) { fn = e->fn; break; }\n",
    "    if (!fn) { fprintf(stderr, \"E: %s: statement not found in module %s\\n\", name, m->name); return 1; }\n",
    "    char **av = calloc((size_t)n + 1, sizeof *av);\n",
    "    if (!av) return 1;\n",
    "    for (int i = 0; i < n; i++) av[i] = zt_expand(tmpl[i], 0);\n",
    "    char *out = NULL;\n",
    "    int rc = fn(n, (const char *const *)av, &out);\n",
    "    for (int i = 0; i < n; i++) free(av[i]);\n",
    "    free(av);\n",
    "    if (rc != 0) {\n",
    "        fprintf(stderr, \"E: %s: %s\\n\", name, out ? out : \"failed\");\n",
    "        free(out);\n",
    "        return 1;\n",
    "    }\n",
    "    if (var) zt_setvar(var, out ? out : \"\");\n",
    "    else if (out) { fputs(out, stdout); fputc('\\n', stdout); fflush(stdout); }\n",
    "    free(out);\n",
    "    return 0;\n",
    "}\n",
    NULL
};

static void append_rt(dstring *d, const char *const *lines) {
    for (; *lines; lines++) dstr_append_cstr(d, *lines);
}

/* keep_c: -e keeps <out>.c next to the executable; -o builds from a temporary
 * file that is removed again. */
static int transpile_to_c(ExecCtx *ctx, const char *out_path, bool keep_c) {
    Func *f = ctx->prog->funcs;
    Func *rev = NULL;
    while (f) {
        Func *next = f->next;
        f->next = rev;
        rev = f;
        f = next;
    }
    ctx->prog->funcs = rev;

    /* def_mod libraries */
    char **libs = NULL;
    size_t nlibs = 0;
    for (size_t i = 0; i < ctx->prog->nmods; i++) {
        const char *m = ctx->prog->mods[i];
        if (strcmp(m, "libztsl") == 0) continue;
        char *path = mod_path(m);
        if (access(path, R_OK) != 0) {
            zt_error("def_mod %s: %s not found", m, path);
            free(path);
            for (size_t k = 0; k < nlibs; k++) free(libs[k]);
            free(libs);
            return -1;
        }
        libs = xrealloc(libs, sizeof(char *) * (nlibs + 1));
        libs[nlibs++] = path;
    }

    if (g_ztv == ZTV_ZTSL26)
        for (Func *fn = ctx->prog->funcs; fn; fn = fn->next)
            stmts_collect_rtvars(fn->body, ctx);

    bool exec_used = false;
    int  gen_rc = 0;
    int  nfuncs = 0;
    dstring body;
    dstr_init(&body);

    if (g_ztv == ZTV_ZTSL26) {
        /* every func becomes zf_N(); run.func is a real C call */
        for (Func *fn = ctx->prog->funcs; fn; fn = fn->next) nfuncs++;
        int idx = 0;
        for (Func *fn = ctx->prog->funcs; fn; fn = fn->next, idx++) {
            dstr_init(&ctx->gen_c);
            int rc = exec_stmt_list(ctx, fn->body);
            if (rc != 0) gen_rc = rc;
            dstr_appendf(&body, "static int zf_%d(void) {\n    /* func \"%s\" */\n", idx, fn->name);
            dstr_append_cstr(&body, ctx->gen_c.data);
            dstr_append_cstr(&body, "    return 0;\n}\n\n");
            dstr_free(&ctx->gen_c);
        }
    } else {
        for (Func *fn = ctx->prog->funcs; fn; fn = fn->next) {
            dstr_init(&ctx->gen_c);
            dstr_appendf(&body, "    /* func \"%s\" */\n", fn->name);
            int rc = exec_stmt_list(ctx, fn->body);
            if (rc != 0) gen_rc = rc;
            if (strstr(ctx->gen_c.data, "do_exec(") != NULL) exec_used = true;
            dstr_append_cstr(&body, ctx->gen_c.data);
            dstr_free(&ctx->gen_c);
        }
    }
    if (gen_rc != 0) {
        dstr_free(&body);
        for (size_t k = 0; k < nlibs; k++) free(libs[k]);
        free(libs);
        return -1;
    }

    dstring src;
    dstr_init(&src);
    dstr_append_cstr(&src,
        "/* Auto-generated by ztc -e. Do not edit. */\n"
        "#define _POSIX_C_SOURCE 200809L\n"
        "#define _DEFAULT_SOURCE\n"
        "#include <stdio.h>\n"
        "#include <stdlib.h>\n"
        "#include <string.h>\n"
        "#include <ctype.h>\n"
        "#include <stdbool.h>\n"
        "#include <unistd.h>\n"
        "#include <sys/wait.h>\n"
        "#include <sys/types.h>\n"
        "#include <sys/mman.h>\n"
        "#include <fcntl.h>\n"
        "#include <signal.h>\n"
        "#include <errno.h>\n"
        "#pragma GCC diagnostic ignored \"-Wunused-function\"\n\n");

    if (g_memchk) {
        dstr_append_cstr(&src, "/* libmemchk is built into ztc (-libmemchk) */\n");
        append_rt(&src, ZTM_RT_SRC);
        dstr_append_cstr(&src, "\n");
    }
    if (g_ztv == ZTV_ZTSL26) {
        char **names = NULL;
        size_t nn = 0;
        for (Func *fn = ctx->prog->funcs; fn; fn = fn->next)
            stmts_collect_args(fn->body, &names, &nn);
        dstr_append_cstr(&src, "static const char *const zt_defined[] = {");
        for (size_t i = 0; i < nn; i++) {
            c_escape_append(&src, names[i]);
            dstr_append_cstr(&src, ", ");
        }
        dstr_append_cstr(&src, "NULL};\n");
        free(names);
        append_rt(&src, ZT26_RT_SRC);
        dstr_append_cstr(&src, "\n");
        for (size_t mi = 0; mi < ctx->prog->nmods; mi++) {
            bool has = false;
            for (size_t li = 0; li < ctx->prog->nlstmts; li++)
                if (ctx->prog->lstmts[li].mod == mi) has = true;
            if (!has) continue;
            char *sym = mod_symbol(ctx->prog->mods[mi]);
            dstr_appendf(&src, "extern const ztsl_module %s;\n", sym);
            free(sym);
        }
    }
    if (exec_used) {
        dstr_append_cstr(&src,
            "/* split_args: respects double-quoted arguments (matches ztc runtime) */\n"
            "static int do_split_args(const char *cmd, char **argv, int max) {\n"
            "    int argc = 0;\n"
            "    const char *p = cmd;\n"
            "    while (*p && argc < max - 1) {\n"
            "        while (*p && (*p == ' ' || *p == '\\t' || *p == '\\n')) p++;\n"
            "        if (!*p) break;\n"
            "        char *tok = NULL;\n"
            "        size_t cap = 16, len = 0;\n"
            "        tok = malloc(cap);\n"
            "        if (!tok) return -1;\n"
            "        bool in_quote = false;\n"
            "        while (*p && (!(*p == ' ' || *p == '\\t' || *p == '\\n') || in_quote)) {\n"
            "            if (*p == '\"') { in_quote = !in_quote; p++; continue; }\n"
            "            if (len + 1 >= cap) { cap *= 2; tok = realloc(tok, cap); if (!tok) return -1; }\n"
            "            tok[len++] = *p++;\n"
            "        }\n"
            "        tok[len] = '\\0';\n"
            "        argv[argc++] = tok;\n"
            "    }\n"
            "    argv[argc] = NULL;\n"
            "    return argc;\n"
            "}\n\n"
            "static void do_free_args(char **argv) {\n"
            "    if (!argv) return;\n"
            "    for (int i = 0; argv[i]; i++) free(argv[i]);\n"
            "}\n\n"
            "static int do_exec(const char *cmd) {\n"
            "    char *argv[256];\n"
            "    int argc = do_split_args(cmd, argv, 256);\n"
            "    if (argc <= 0) return 0;\n"
            "    pid_t pid = fork();\n"
            "    if (pid < 0) { do_free_args(argv); return -1; }\n"
            "    if (pid == 0) {\n"
            "        execvp(argv[0], argv);\n"
            "        fprintf(stderr, \"execvp(%s) failed: %s\\n\",\n"
            "                argv[0], strerror(errno));\n"
            "        _exit(127);\n"
            "    }\n"
            "    int status = 0;\n"
            "    waitpid(pid, &status, 0);\n"
            "    do_free_args(argv);\n"
            "    if (WIFEXITED(status)) return WEXITSTATUS(status);\n"
            "    return 1;\n"
            "}\n\n");
    }

    if (g_memchk) {
        /* from here on, every malloc/free in the program (including raw C in
         * ccompat blocks) is the guarded one */
        dstr_append_cstr(&src,
            "#define malloc(n)     ztm_malloc(n)\n"
            "#define calloc(a, b)  ztm_calloc((a), (b))\n"
            "#define realloc(p, n) ztm_realloc((p), (n))\n"
            "#define free(p)       ztm_free(p)\n"
            "#define strdup(s)     ztm_strdup(s)\n"
            "#define ZTM_INIT()    ztm_init()\n"
            "#define ZTM_CHK()     ztm_check()\n"
            "#define ZTM_LEAKS()   ztm_leaks()\n\n");
    } else {
        dstr_append_cstr(&src,
            "#define ZTM_INIT()    ((void)0)\n"
            "#define ZTM_CHK()     ((void)0)\n"
            "#define ZTM_LEAKS()   ((void)0)\n\n");
    }

    if (ctx->nhnames > 0) {
        dstr_appendf(&src, "static char  *zt_h[%zu];\nstatic size_t zt_hn[%zu];\n\n",
                     ctx->nhnames, ctx->nhnames);
    }

    if (g_ztv == ZTV_ZTSL26) {
        for (int i = 0; i < nfuncs; i++)
            dstr_appendf(&src, "static int zf_%d(void);\n", i);
        dstr_append_cstr(&src, "\n");
        dstr_append_cstr(&src, body.data);
        dstr_append_cstr(&src,
            "int main(int argc, char **argv) {\n"
            "    zt_argc = argc;\n"
            "    zt_argv = argv;\n"
            "    ZTM_INIT();\n"
            "    int zr;\n");
        int idx = 0;
        for (Func *fn = ctx->prog->funcs; fn; fn = fn->next, idx++) {
            if (!func_is_entry(ctx->prog, fn)) continue;
            dstr_appendf(&src, "    zr = zf_%d(); ZTM_CHK(); if (zr != 0) return zr;\n", idx);
        }
        dstr_append_cstr(&src, "    ZTM_LEAKS();\n    return 0;\n}\n");
    } else {
        dstr_append_cstr(&src, "int main(void) {\n    ZTM_INIT();\n");
        dstr_append_cstr(&src, body.data);
        dstr_append_cstr(&src, "    ZTM_LEAKS();\n    return 0;\n}\n");
    }

    char cpath[1024];
    FILE *cf = NULL;
    if (keep_c) {
        snprintf(cpath, sizeof(cpath), "%s.c", out_path);
        cf = fopen(cpath, "w");
    } else {
        const char *tmpd = getenv("TMPDIR");
        snprintf(cpath, sizeof(cpath), "%s/ztc-XXXXXX.c",
                 (tmpd && *tmpd) ? tmpd : "/tmp");
        int tfd = mkstemps(cpath, 2);
        if (tfd >= 0) {
            cf = fdopen(tfd, "w");
            if (!cf) { close(tfd); unlink(cpath); }
        }
    }
    if (!cf) {
        zt_error("cannot open %s: %s", cpath, strerror(errno));
        dstr_free(&src);
        dstr_free(&body);
        for (size_t k = 0; k < nlibs; k++) free(libs[k]);
        free(libs);
        return -1;
    }
    fwrite(src.data, 1, src.len, cf);
    fclose(cf);

    dstr_free(&src);
    dstr_free(&body);

    char **gcc_argv = xmalloc(sizeof(char *) * (12 + nlibs));
    int ga = 0;
    gcc_argv[ga++] = "gcc";
    gcc_argv[ga++] = "-std=c11";
    gcc_argv[ga++] = "-Wall";
    gcc_argv[ga++] = "-Wextra";
    gcc_argv[ga++] = "-Werror";
    gcc_argv[ga++] = "-O2";
    gcc_argv[ga++] = cpath;
    gcc_argv[ga++] = "-o";
    gcc_argv[ga++] = (char *)out_path;
    for (size_t k = 0; k < nlibs; k++) gcc_argv[ga++] = libs[k];
    if (nlibs) gcc_argv[ga++] = "-Wl,-rpath," ZTSL_LIBDIR;
    gcc_argv[ga] = NULL;

    if (ctx->verbose) {
        fprintf(stderr, "ztc: invoking: gcc");
        for (char **a = gcc_argv + 1; *a; a++) fprintf(stderr, " %s", *a);
        fprintf(stderr, "\n");
    }
    pid_t pid = fork();
    if (pid < 0) {
        zt_error("fork() failed: %s", strerror(errno));
        free(gcc_argv);
        for (size_t k = 0; k < nlibs; k++) free(libs[k]);
        free(libs);
        return -1;
    }
    if (pid == 0) {
        execvp("gcc", gcc_argv);
        fprintf(stderr, "E: execvp(gcc) failed: %s\n", strerror(errno));
        _exit(127);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    int rc = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
    free(gcc_argv);
    for (size_t k = 0; k < nlibs; k++) free(libs[k]);
    free(libs);
    if (!keep_c) unlink(cpath);
    if (rc != 0) {
        zt_error("gcc failed (rc=%d)%s", rc,
                 keep_c ? "" : "; re-run with -e to keep the generated C for inspection");
        return rc;
    }
    if (keep_c)
        fprintf(stderr, "Generated C code and ELF in %s and %s%s\n", out_path, cpath,
                g_memchk ? " (libmemchk)" : "");
    else
        fprintf(stderr, "Generated ELF in %s%s\n", out_path,
                g_memchk ? " (libmemchk)" : "");
    return 0;
}

static void usage(const char *argv0) {
    fprintf(stderr,
        "ztc %s (ZTSL %s) - ZTSL build tool\n"
        "Usage: %s [options] [target ...]\n"
        "       %s -o <out> <file.ztsl> [-libmemchk] [-ztv=<version>]\n"
        "  -f <file>      Build file (default: build.ztsl)\n"
        "  -e <out>       Transpile to C and build executable <out>; keeps <out>.c\n"
        "  -o <out>       Build executable <out> from the .ztsl given as a positional\n"
        "                 argument (instead of -f). No .c file is left behind; use -e\n"
        "                 to get it\n"
        "  -ztv=<ver>     Language version:\n"
        "                   p26     ZTSL p26 (ztc 0.1), the original syntax (default)\n"
        "                   ztsl26  ZTSL 26  (ztc 0.26): def_mod, run.func, 'if argument',\n"
        "                           sys.exec.silent, %%a%% / %%ea%%\n"
        "  -libmemchk     Built-in memory checker: use-after-free, double free, leak\n"
        "                 and buffer overflow print 'E: Value Out of Bounds (...)' and\n"
        "                 segfault (guards mem.* and malloc/free inside ccompat)\n"
        "  -l             List available functions and exit\n"
        "  -F             Force (ignore cache)\n"
        "  -v             Verbose\n"
        "  -V             Print version and exit\n"
        "  -h             Help\n"
        "In -ztv=ztsl26 interpreted runs, words after the file are the program's\n"
        "arguments: %s -ztv=ztsl26 prog.ztsl create mysnap\n",
        g_ztv == ZTV_P26 ? ZTC_VERSION_P26 : ZTC_VERSION,
        g_ztv == ZTV_P26 ? "p26" : "ztsl26", argv0, argv0, argv0);
}

int main(int argc, char **argv) {
    /* -ztv=<ver> and -libmemchk are single-dash words getopt would take for
     * clusters of short options, so pull them out first (anywhere on the line,
     * up to a lone "--"). */
    {
        char **fa = xmalloc(sizeof(char *) * ((size_t)argc + 1));
        int fc = 0;
        bool scanning = true;
        for (int i = 0; i < argc; i++) {
            if (scanning && i > 0 && strcmp(argv[i], "--") == 0) {
                scanning = false;
            } else if (scanning && i > 0 && strncmp(argv[i], "-ztv=", 5) == 0) {
                const char *v = argv[i] + 5;
                if (strcmp(v, "p26") == 0) g_ztv = ZTV_P26;
                else if (strcmp(v, "ztsl26") == 0) g_ztv = ZTV_ZTSL26;
                else {
                    zt_error("unknown -ztv version '%s' (expected p26 or ztsl26)", v);
                    return 2;
                }
                continue;
            } else if (scanning && i > 0 && strcmp(argv[i], "-libmemchk") == 0) {
                g_memchk = true;
                continue;
            }
            fa[fc++] = argv[i];
        }
        fa[fc] = NULL;
        argv = fa;
        argc = fc;
    }
    const char *prog_name = argv[0] ? argv[0] : "ztc";
    const char *pn_slash = strrchr(prog_name, '/');
    if (pn_slash) prog_name = pn_slash + 1;
    const char *build_file = "build.ztsl";
    const char *exec_out   = NULL;
    bool list_only = false;
    bool force = false;
    bool verbose = false;
    bool positional_file = false;
    bool f_given = false;
    bool keep_c = false;

    int opt;
    while ((opt = getopt(argc, argv, "+f:e:o:lFvVh")) != -1) {
        switch (opt) {
            case 'f': build_file = optarg; f_given = true; break;
            case 'e': exec_out   = optarg; keep_c = true; break;
            case 'o': exec_out   = optarg; positional_file = true; break;
            case 'l': list_only  = true;   break;
            case 'F': force      = true;   break;
            case 'v': verbose   = true;    break;
            case 'V':
                printf("ztc %s (ZTSL %s)\n",
                       g_ztv == ZTV_P26 ? ZTC_VERSION_P26 : ZTC_VERSION,
                       g_ztv == ZTV_P26 ? "p26" : "ztsl26");
                return 0;
            case 'h': usage(argv[0]); return 0;
            default:  usage(argv[0]); return 2;
        }
    }

    
    char **targets = NULL;
    int ntargets = 0;
    if (optind < argc) {
        targets = &argv[optind];
        ntargets = argc - optind;
    }

    /* a memchk run must always really execute: never short-circuit it through
     * the p26 hash cache */
    if (g_memchk) force = true;

    /* ztsl26 interpreted run: words after the file are the program's arguments */
    char **prog_args = NULL;
    int nprog_args = 0;
    if (g_ztv == ZTV_ZTSL26 && !exec_out) {
        if (!f_given && ntargets > 0) {
            size_t tl = strlen(targets[0]);
            if (tl > 5 && strcmp(targets[0] + tl - 5, ".ztsl") == 0) {
                build_file = targets[0];
                targets++;
                ntargets--;
            }
        }
        prog_args = targets;
        nprog_args = ntargets;
        targets = NULL;
        ntargets = 0;
    }

    if (positional_file) {
        if (ntargets < 1) {
            zt_error("-o requires a .ztsl file: ztc -o <out> <file.ztsl>");
            return 2;
        }
        build_file = targets[0];
        if (ntargets > 1) {
            zt_warn("-o converts the whole file; ignoring extra "
                    "arguments after %s", build_file);
        }
        targets = NULL;
        ntargets = 0;
    }

    
    char *content = read_file(build_file);
    if (!content) {
        zt_error("cannot read %s: %s",
                build_file, strerror(errno));
        return 1;
    }

    
    char *stripped_ztsl = strip_comments(content);

    char extfile[1024];
    snprintf(extfile, sizeof(extfile), "%s", build_file);
    char *dot_ext = strrchr(extfile, '.');
    if (dot_ext) strcpy(dot_ext, ".ztslo");
    else         strcat(extfile, ".ztslo");
    char *ext_content = read_file(extfile);

    dstring combined;
    dstr_init(&combined);
    dstr_append_cstr(&combined, stripped_ztsl);
    dstr_append_cstr(&combined, "\n||ZTSLO||\n");
    if (ext_content) {
        char *stripped_ztslo = strip_comments(ext_content);
        dstr_append_cstr(&combined, stripped_ztslo);
        free(stripped_ztslo);
        free(ext_content);
    }
    char *new_hash = sha256_hex(combined.data, combined.len);
    dstr_free(&combined);
    free(stripped_ztsl);

    
    const char *slash = strrchr(build_file, '/');
    const char *base = slash ? slash + 1 : build_file;
    
    char base_noext[256];
    snprintf(base_noext, sizeof(base_noext), "%s", base);
    char *dot = strrchr(base_noext, '.');
    if (dot) *dot = '\0';

    const char *hashdir = "hash";
    if (g_ztv == ZTV_P26) mkdir(hashdir, 0755);   /* cache is a p26 build-tool feature */
    char *stored = read_stored_hash(hashdir, base_noext);

    bool cache_hit = false;
    if (!force && stored && strcmp(stored, new_hash) == 0) {
        cache_hit = true;
    }

    if (verbose) {
        fprintf(stderr, "ztc: build file    = %s\n", build_file);
        fprintf(stderr, "ztc: ztslo file    = %s%s\n", extfile,
                ext_content ? "" : " (not found)");
        fprintf(stderr, "ztc: current hash  = %s\n", new_hash);
        fprintf(stderr, "ztc: stored hash   = %s\n",
                stored ? stored : "(none)");
        fprintf(stderr, "ztc: cache %s\n",
                cache_hit ? "HIT (skipping)" : "MISS (running)");
    }

    
    LineBuf lb;
    linebuf_init(&lb);
    file_to_lines(content, &lb);
    free(content);

    Parser p = { .lb = &lb, .pos = 0, .error = false, .err_msg = NULL };
    Program prog = { .funcs = NULL, .vars = NULL };
    p.prog = &prog;
    parse_program(&p, &prog);

    if (p.error) {
                zt_error("parse error: %s",
                        p.err_msg ? p.err_msg : "(unknown)");
        free(p.err_msg);
        linebuf_free(&lb);
        var_free(prog.vars);
        func_free(prog.funcs);
        free(new_hash);
        free(stored);
        return 1;
    }

    
    {
        char extfile[1024];
        snprintf(extfile, sizeof(extfile), "%s", build_file);
        char *dot2 = strrchr(extfile, '.');
        if (dot2) strcpy(dot2, ".ztslo");
        else      strcat(extfile, ".ztslo");

        bool ext_exists = (access(extfile, F_OK) == 0);
        if (prog.inline_ztslo_used && ext_exists) {
            zt_warn("inline ztslo block in %s; external %s will be ignored",
                    build_file, extfile);
        }

        if (!prog.inline_ztslo_used && ext_exists) {
            char *ext_content = read_file(extfile);
            if (ext_content) {
                if (verbose) {
                    fprintf(stderr, "ztc: loaded external ztslo: %s\n",
                            extfile);
                }
                LineBuf elb;
                linebuf_init(&elb);
                file_to_lines(ext_content, &elb);
                free(ext_content);

                Parser ep = { .lb = &elb, .pos = 0, .error = false, .err_msg = NULL, .prog = &prog };
                parse_program(&ep, &prog);
                if (ep.error) {
                    zt_error("parse error in %s: %s",
                            extfile, ep.err_msg ? ep.err_msg : "(unknown)");
                    free(ep.err_msg);
                    linebuf_free(&elb);
                    linebuf_free(&lb);
                    var_free(prog.vars);
                    func_free(prog.funcs);
                    free(new_hash);
                    free(stored);
                    return 1;
                }
                linebuf_free(&elb);
            }
        } else if (!prog.inline_ztslo_used && verbose) {
            fprintf(stderr, "ztc: no inline ztslo and no %s; "
                    "continuing with empty variable table\n", extfile);
        }
    }

    
    if (list_only) {
        
        Func *rev = NULL;
        Func *f = prog.funcs;
        while (f) {
            Func *next = f->next;
            f->next = rev;
            rev = f;
            f = next;
        }
        prog.funcs = rev;
        printf("Available functions in %s:\n", build_file);
        for (Func *fn = prog.funcs; fn; fn = fn->next)
            printf("  - %s\n", fn->name);
        linebuf_free(&lb);
        var_free(prog.vars);
        func_free(prog.funcs);
        free(new_hash);
        free(stored);
        return 0;
    }

    
    if (exec_out) {
        ExecCtx ctx;
        memset(&ctx, 0, sizeof(ctx));
        ctx.prog    = &prog;
        ctx.vars    = &prog.vars;
        ctx.verbose = verbose;
        ctx.dry_run = true;
        ctx.force   = force;
        int rc = transpile_to_c(&ctx, exec_out, keep_c);
        linebuf_free(&lb);
        var_free(prog.vars);
        func_free(prog.funcs);
        free(new_hash);
        free(stored);
        return rc == 0 ? 0 : 1;
    }

    
    if (g_ztv == ZTV_ZTSL26) {
        /* ZTSL 26 programs are run, not built: no hash cache. Entry funcs
         * (the 'if argument' guards) run in source order. */
        ExecCtx zctx;
        memset(&zctx, 0, sizeof(zctx));
        zctx.prog    = &prog;
        zctx.vars    = &prog.vars;
        zctx.verbose = verbose;
        zctx.force   = force;
        zctx.args    = prog_args;
        zctx.nargs   = nprog_args;

        Func *zrev = NULL;
        Func *zf = prog.funcs;
        while (zf) {
            Func *next = zf->next;
            zf->next = zrev;
            zrev = zf;
            zf = next;
        }
        prog.funcs = zrev;

        int zrc = 0;
        for (Func *fn = prog.funcs; fn; fn = fn->next) {
            if (!func_is_entry(&prog, fn)) continue;
            if (verbose) fprintf(stderr, "ztc: === func %s ===\n", fn->name);
            zrc = exec_stmt_list(&zctx, fn->body);
            if (zrc != 0) {
                if (zrc != 2) zt_error("function %s failed (rc=%d)", fn->name, zrc);
                break;
            }
        }
        if (zrc == 0 && g_memchk) zrc = mem_leak_since(&zctx, 0);
        mem_free_all(&zctx);
        linebuf_free(&lb);
        var_free(prog.vars);
        func_free(prog.funcs);
        prog_free_mods(&prog);
        free(new_hash);
        free(stored);
        return zrc == 0 ? 0 : (zrc == 2 ? 2 : 1);
    }

    if (cache_hit && ntargets == 0) {
        
        bool all_hit = true;
        for (Func *fn = prog.funcs; fn; fn = fn->next) {
            char *fh = compute_func_hash(new_hash, fn);
            char fkey[512];
            snprintf(fkey, sizeof(fkey), "%s.%s", base_noext, fn->name);
            char *stored_fh = read_stored_hash(hashdir, fkey);
            bool hit = (stored_fh && strcmp(stored_fh, fh) == 0);
            if (!hit) { all_hit = false; }
            if (verbose)
                fprintf(stderr, "ztc: func %-20s %s\n", fn->name,
                        hit ? "(cached)" : "(will run)");
            free(fh);
            free(stored_fh);
        }
        if (all_hit) {
            fprintf(stderr,
                    "E: all functions in %s unchanged since last successful run; skipping.\n"
                    "  - to force re-run:    %s -F [%s]\n"
                    "  - to clear all cache: rm -rf hash/\n"
                    "  - to see what's there: %s -l [%s]\n",
                    build_file,
                    prog_name, build_file,
                    prog_name, build_file);
            linebuf_free(&lb);
            var_free(prog.vars);
            func_free(prog.funcs);
            free(new_hash);
            free(stored);
            return 0;
        }
    } else if (cache_hit && verbose) {
        fprintf(stderr, "ztc: global cache hit but specific targets requested; running.\n");
    }

    
    ExecCtx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.prog    = &prog;
    ctx.vars    = &prog.vars;
    ctx.verbose = verbose;
    ctx.dry_run = false;
    ctx.force   = force;

    
    Func *rev = NULL;
    Func *f = prog.funcs;
    while (f) {
        Func *next = f->next;
        f->next = rev;
        rev = f;
        f = next;
    }
    prog.funcs = rev;

    int rc = 0;
    if (ntargets == 0) {
        
        for (Func *fn = prog.funcs; fn; fn = fn->next) {
            char *fh = compute_func_hash(new_hash, fn);
            char fkey[512];
            snprintf(fkey, sizeof(fkey), "%s.%s", base_noext, fn->name);
            char *stored_fh = read_stored_hash(hashdir, fkey);
            bool hit = (!force && stored_fh && strcmp(stored_fh, fh) == 0);
            free(stored_fh);

            if (hit) {
                if (verbose)
                    fprintf(stderr, "ztc: === func %s === (cached, skipping)\n",
                            fn->name);
                free(fh);
                continue;
            }

            if (verbose) fprintf(stderr, "ztc: === func %s ===\n",
                                 fn->name);
            rc = exec_stmt_list(&ctx, fn->body);
            if (rc != 0) {
                zt_error("function %s failed (rc=%d)", fn->name, rc);
                free(fh);
                break;
            }
            
            write_stored_hash(hashdir, fkey, fh);
            free(fh);
        }
    } else {
        
        for (int i = 0; i < ntargets; i++) {
            Func *fn = NULL;
            for (Func *g = prog.funcs; g; g = g->next) {
                if (strcmp(g->name, targets[i]) == 0) { fn = g; break; }
            }
            if (!fn) {
                zt_error("no such function: %s", targets[i]);
                rc = 1;
                break;
            }
            char *fh = compute_func_hash(new_hash, fn);
            char fkey[512];
            snprintf(fkey, sizeof(fkey), "%s.%s", base_noext, fn->name);
            char *stored_fh = read_stored_hash(hashdir, fkey);
            bool hit = (!force && stored_fh && strcmp(stored_fh, fh) == 0);
            free(stored_fh);

            if (hit) {
                if (verbose)
                    fprintf(stderr, "ztc: === func %s === (cached, skipping)\n",
                            fn->name);
                free(fh);
                continue;
            }

            if (verbose) fprintf(stderr, "ztc: === func %s ===\n",
                                 fn->name);
            rc = exec_stmt_list(&ctx, fn->body);
            if (rc != 0) {
                zt_error("function %s failed (rc=%d)", fn->name, rc);
                free(fh);
                break;
            }
            
            write_stored_hash(hashdir, fkey, fh);
            free(fh);
        }
    }

    
    if (rc == 0 && g_memchk) rc = mem_leak_since(&ctx, 0);
    mem_free_all(&ctx);

    if (rc == 0) {
        
        write_stored_hash(hashdir, base_noext, new_hash);
        if (verbose)
            fprintf(stderr, "ztc: updated global hash for %s\n", base_noext);
    }

    linebuf_free(&lb);
    var_free(prog.vars);
    func_free(prog.funcs);
    free(new_hash);
    free(stored);
    return rc == 0 ? 0 : 1;
}

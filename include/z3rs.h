/* z3rs — C ABI for the pure-Rust Z3 port.
 *
 * Link against the static (libz3rs.a) or shared (libz3rs.so/.dylib/.dll)
 * library built with:
 *   cargo rustc --lib --release --features ffi --crate-type staticlib
 *   cargo rustc --lib --release --features ffi --crate-type cdylib
 */
#ifndef Z3RS_H
#define Z3RS_H

#ifdef __cplusplus
extern "C" {
#endif

/* The z3rs version string (statically owned; do not free). */
const char *z3rs_version(void);

/* Evaluate an SMT-LIB 2 (or 1.2) script. Returns a newly allocated C string
 * with one response line per check-sat (newline-separated), or an
 * (error "...") line on a parse error; NULL if `script` is NULL or not UTF-8.
 * Release the result with z3rs_string_free. */
char *z3rs_eval_smtlib2_string(const char *script);

/* Free a string returned by z3rs_eval_smtlib2_string / z3rs_session_eval
 * (NULL is ignored). */
void z3rs_string_free(char *s);

/* ---- Stateful solver session (incremental) ---- */

/* Opaque persistent session: declarations, assertions and the push/pop stack
 * carry across z3rs_session_eval calls. */
typedef struct Z3rsSession Z3rsSession;

/* Create a new, empty session. */
Z3rsSession *z3rs_mk_session(void);

/* Evaluate more SMT-LIB2 text against the session's accumulated state. Returns
 * a newly allocated C string (newline-separated responses), or NULL on a NULL
 * argument / invalid UTF-8. Free with z3rs_string_free. */
char *z3rs_session_eval(Z3rsSession *s, const char *script);

/* Check the session's current assertions (convenience over (check-sat)).
 * Returns 1 = sat, 0 = unsat, -1 = unknown, -2 on NULL/error. */
int z3rs_session_check(Z3rsSession *s);

/* Scope management (convenience over (push)/(pop)/(reset)).
 * Return 0 on success, -1 on error. */
int z3rs_session_push(Z3rsSession *s);
int z3rs_session_pop(Z3rsSession *s);
int z3rs_session_reset(Z3rsSession *s);

/* Free a session created by z3rs_mk_session (NULL is ignored). */
void z3rs_del_session(Z3rsSession *s);

/* ---- Z3-compatible drop-in slice ----
 * Same symbol names & ABI as Z3's z3_api.h, so a C program written against Z3
 * that uses only this subset links against libz3rs. Handles are opaque pointers
 * (matching Z3's typedef struct _Z3_{config,context}*). */
typedef struct Z3rsZ3Config *Z3_config;
typedef struct Z3rsZ3Context *Z3_context;

Z3_config Z3_mk_config(void);
void Z3_del_config(Z3_config c);
Z3_context Z3_mk_context(Z3_config cfg);
void Z3_del_context(Z3_context c);

/* Evaluate an SMT-LIB2 command sequence; state persists across calls. The
 * returned string is owned by the context (valid until the next call or
 * Z3_del_context) — do NOT free it. */
const char *Z3_eval_smtlib2_string(Z3_context c, const char *str);

/* Version string (statically owned; do not free). */
const char *Z3_get_full_version(void);

/* ---- Z3-compatible object (handle) API ----
 * Build sorts/consts/terms through the context, then assert & check with a
 * solver. All handles are owned by the context and freed at Z3_del_context. */
typedef const char *Z3_symbol;
typedef struct Z3rsSort *Z3_sort;
typedef struct Z3rsAst *Z3_ast;
typedef struct Z3rsSolver *Z3_solver;

Z3_symbol Z3_mk_string_symbol(Z3_context c, const char *s);
Z3_sort Z3_mk_int_sort(Z3_context c);
Z3_sort Z3_mk_bool_sort(Z3_context c);
Z3_sort Z3_mk_real_sort(Z3_context c);
Z3_sort Z3_mk_bv_sort(Z3_context c, unsigned sz);
Z3_ast Z3_mk_const(Z3_context c, Z3_symbol sym, Z3_sort sort);
Z3_ast Z3_mk_numeral(Z3_context c, const char *text, Z3_sort sort);
Z3_ast Z3_mk_add(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_sub(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_mul(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_and(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_or(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_lt(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_le(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_gt(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_ge(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_eq(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_implies(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_not(Z3_context c, Z3_ast a);
Z3_solver Z3_mk_solver(Z3_context c);
void Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a);
/* Returns a Z3_lbool: 1 = sat, -1 = unsat, 0 = unknown. */
int Z3_solver_check(Z3_context c, Z3_solver s);

typedef struct Z3rsModel *Z3_model;
Z3_model Z3_solver_get_model(Z3_context c, Z3_solver s);
/* Context-owned strings; do not free. */
const char *Z3_model_to_string(Z3_context c, Z3_model m);
const char *Z3_ast_to_string(Z3_context c, Z3_ast a);

#ifdef __cplusplus
}
#endif

#endif /* Z3RS_H */

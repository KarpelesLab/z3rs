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

/* Free a session created by z3rs_mk_session (NULL is ignored). */
void z3rs_del_session(Z3rsSession *s);

#ifdef __cplusplus
}
#endif

#endif /* Z3RS_H */

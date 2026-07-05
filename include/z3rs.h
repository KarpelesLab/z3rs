/* z3rs — C ABI for the pure-Rust Z3 port.
 *
 * Link against the static (libz3rs.a) or shared (libz3rs.so/.dylib/.dll)
 * library built with:
 *   cargo rustc --lib --release --features ffi --crate-type staticlib
 *   cargo rustc --lib --release --features ffi --crate-type cdylib
 */
#ifndef Z3RS_H
#define Z3RS_H

#include <stdbool.h>

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
/* Reference-counted context; identical to Z3_mk_context in z3rs (handles live
 * in context arenas freed at Z3_del_context). */
Z3_context Z3_mk_context_rc(Z3_config cfg);
void Z3_del_context(Z3_context c);

/* Emulated Z3 version numbers (4.17.0.0). NULL out-pointers are skipped. */
void Z3_get_version(unsigned *major, unsigned *minor, unsigned *build_number,
                    unsigned *revision_number);

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
typedef struct Z3rsFuncDecl *Z3_func_decl;
typedef struct Z3rsSolver *Z3_solver;
typedef struct Z3rsModel *Z3_model;

/* ---- Reference-counting lifecycle (no-ops in z3rs) ----
 * Handles live in context arenas freed at Z3_del_context, so these do nothing;
 * they exist so RC-style clients link and run. */
void Z3_inc_ref(Z3_context c, Z3_ast a);
void Z3_dec_ref(Z3_context c, Z3_ast a);
void Z3_solver_inc_ref(Z3_context c, Z3_solver s);
void Z3_solver_dec_ref(Z3_context c, Z3_solver s);
void Z3_model_inc_ref(Z3_context c, Z3_model m);
void Z3_model_dec_ref(Z3_context c, Z3_model m);

Z3_symbol Z3_mk_string_symbol(Z3_context c, const char *s);
const char *Z3_get_symbol_string(Z3_context c, Z3_symbol s);

/* ---- Sorts ---- */
Z3_sort Z3_mk_int_sort(Z3_context c);
Z3_sort Z3_mk_bool_sort(Z3_context c);
Z3_sort Z3_mk_real_sort(Z3_context c);
Z3_sort Z3_mk_bv_sort(Z3_context c, unsigned sz);
Z3_sort Z3_mk_array_sort(Z3_context c, Z3_sort domain, Z3_sort range);
Z3_sort Z3_mk_uninterpreted_sort(Z3_context c, Z3_symbol name);

/* Z3_sort_kind: UNINTERPRETED=0, BOOL=1, INT=2, REAL=3, BV=4, ARRAY=5. */
Z3_sort Z3_get_sort(Z3_context c, Z3_ast a);
unsigned Z3_get_sort_kind(Z3_context c, Z3_sort s);
unsigned Z3_get_bv_sort_size(Z3_context c, Z3_sort s);
Z3_sort Z3_get_array_sort_domain(Z3_context c, Z3_sort s);
Z3_sort Z3_get_array_sort_range(Z3_context c, Z3_sort s);
const char *Z3_sort_to_string(Z3_context c, Z3_sort s);

/* ---- Constants, numerals, uninterpreted functions ---- */
Z3_ast Z3_mk_const(Z3_context c, Z3_symbol sym, Z3_sort sort);
Z3_ast Z3_mk_fresh_const(Z3_context c, const char *prefix, Z3_sort sort);
Z3_ast Z3_mk_numeral(Z3_context c, const char *text, Z3_sort sort);
Z3_ast Z3_mk_int(Z3_context c, int v, Z3_sort ty);
Z3_ast Z3_mk_unsigned_int(Z3_context c, unsigned v, Z3_sort ty);
Z3_ast Z3_mk_int64(Z3_context c, long long v, Z3_sort ty);
Z3_ast Z3_mk_unsigned_int64(Z3_context c, unsigned long long v, Z3_sort ty);
Z3_ast Z3_mk_real(Z3_context c, int num, int den);
Z3_func_decl Z3_mk_func_decl(Z3_context c, Z3_symbol s, unsigned domain_size,
                             Z3_sort const domain[], Z3_sort range);
Z3_ast Z3_mk_app(Z3_context c, Z3_func_decl d, unsigned num_args,
                 Z3_ast const args[]);

/* ---- Booleans / core ---- */
Z3_ast Z3_mk_true(Z3_context c);
Z3_ast Z3_mk_false(Z3_context c);
Z3_ast Z3_mk_ite(Z3_context c, Z3_ast cond, Z3_ast then, Z3_ast els);
Z3_ast Z3_mk_distinct(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_iff(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_xor(Z3_context c, Z3_ast l, Z3_ast r);
/* Boolean literal value: 1 = true, -1 = false, 0 = undef. */
int Z3_get_bool_value(Z3_context c, Z3_ast a);

/* ---- Arithmetic ---- */
Z3_ast Z3_mk_add(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_sub(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_mul(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_and(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_or(Z3_context c, unsigned num, Z3_ast const args[]);
Z3_ast Z3_mk_unary_minus(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_div(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_mod(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_rem(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_power(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_int2real(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_real2int(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_is_int(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_divides(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_lt(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_le(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_gt(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_ge(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_eq(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_implies(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_not(Z3_context c, Z3_ast a);

/* ---- Bit-vectors ---- */
Z3_ast Z3_mk_bvadd(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvsub(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvmul(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvudiv(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvsdiv(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvurem(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvsrem(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvsmod(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvand(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvor(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvxor(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvnand(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvnor(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvxnor(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvshl(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvlshr(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvashr(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvnot(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_bvneg(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_bvult(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvslt(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvule(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvsle(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvugt(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvsgt(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvuge(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_bvsge(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_concat(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_extract(Z3_context c, unsigned high, unsigned low, Z3_ast a);
Z3_ast Z3_mk_sign_ext(Z3_context c, unsigned i, Z3_ast a);
Z3_ast Z3_mk_zero_ext(Z3_context c, unsigned i, Z3_ast a);
Z3_ast Z3_mk_repeat(Z3_context c, unsigned i, Z3_ast a);
Z3_ast Z3_mk_rotate_left(Z3_context c, unsigned i, Z3_ast a);
Z3_ast Z3_mk_rotate_right(Z3_context c, unsigned i, Z3_ast a);
Z3_ast Z3_mk_int2bv(Z3_context c, unsigned n, Z3_ast a);
Z3_ast Z3_mk_bv2int(Z3_context c, Z3_ast a, bool is_signed);

/* ---- Arrays ---- */
Z3_ast Z3_mk_select(Z3_context c, Z3_ast a, Z3_ast i);
Z3_ast Z3_mk_store(Z3_context c, Z3_ast a, Z3_ast i, Z3_ast v);
Z3_ast Z3_mk_const_array(Z3_context c, Z3_sort domain, Z3_ast v);

/* ---- Solvers ---- */
Z3_solver Z3_mk_solver(Z3_context c);
Z3_solver Z3_mk_simple_solver(Z3_context c);
void Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a);
void Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p);
/* Returns a Z3_lbool: 1 = sat, -1 = unsat, 0 = unknown. */
int Z3_solver_check(Z3_context c, Z3_solver s);
int Z3_solver_check_assumptions(Z3_context c, Z3_solver s,
                                unsigned num_assumptions,
                                Z3_ast const assumptions[]);
void Z3_solver_push(Z3_context c, Z3_solver s);
void Z3_solver_pop(Z3_context c, Z3_solver s, unsigned n);
void Z3_solver_reset(Z3_context c, Z3_solver s);
unsigned Z3_solver_get_num_scopes(Z3_context c, Z3_solver s);

Z3_model Z3_solver_get_model(Z3_context c, Z3_solver s);
/* Context-owned strings; do not free. */
const char *Z3_model_to_string(Z3_context c, Z3_model m);
const char *Z3_ast_to_string(Z3_context c, Z3_ast a);

/* ---- AST kind & numeral readback ----
 * Z3_ast_kind: NUMERAL=0, APP=1, VAR=2, QUANTIFIER=3, SORT=4, FUNC_DECL=5,
 * UNKNOWN=1000. z3rs terms are text, so only NUMERAL vs APP is distinguished. */
unsigned Z3_get_ast_kind(Z3_context c, Z3_ast a);
bool Z3_is_numeral_ast(Z3_context c, Z3_ast a);
/* Decimal ("6") or rational ("1/2") string of a numeral (context-owned). */
const char *Z3_get_numeral_string(Z3_context c, Z3_ast a);
/* Write the numeral's value; return false if not an integer numeral / no fit. */
bool Z3_get_numeral_int(Z3_context c, Z3_ast v, int *i);
bool Z3_get_numeral_uint(Z3_context c, Z3_ast v, unsigned *u);
bool Z3_get_numeral_int64(Z3_context c, Z3_ast v, long long *i);
bool Z3_get_numeral_uint64(Z3_context c, Z3_ast v, unsigned long long *u);

/* ---- Application accessors (minimum viable) ----
 * Z3_app is an alias of Z3_ast (z3rs has one term representation). */
typedef Z3_ast Z3_app;
Z3_app Z3_to_app(Z3_context c, Z3_ast a);
Z3_func_decl Z3_get_app_decl(Z3_context c, Z3_app a);
unsigned Z3_get_app_num_args(Z3_context c, Z3_app a);
Z3_ast Z3_get_app_arg(Z3_context c, Z3_app a, unsigned i);
Z3_symbol Z3_get_decl_name(Z3_context c, Z3_func_decl d);

/* ---- Model value readback ----
 * Evaluate t under model m; write the value AST to *v; return true on success. */
bool Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, bool model_completion,
                   Z3_ast *v);
/* Value of a 0-ary declaration in the model (NULL if unavailable). */
Z3_ast Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a);
unsigned Z3_model_get_num_consts(Z3_context c, Z3_model m);
Z3_func_decl Z3_model_get_const_decl(Z3_context c, Z3_model m, unsigned i);

/* ---- AST vectors (z3_ast_containers.h) ----
 * Owned by the context arena, freed at Z3_del_context; inc/dec_ref are no-ops. */
typedef struct Z3rsAstVector *Z3_ast_vector;
Z3_ast_vector Z3_mk_ast_vector(Z3_context c);
void Z3_ast_vector_inc_ref(Z3_context c, Z3_ast_vector v);
void Z3_ast_vector_dec_ref(Z3_context c, Z3_ast_vector v);
unsigned Z3_ast_vector_size(Z3_context c, Z3_ast_vector v);
Z3_ast Z3_ast_vector_get(Z3_context c, Z3_ast_vector v, unsigned i);
void Z3_ast_vector_push(Z3_context c, Z3_ast_vector v, Z3_ast a);
const char *Z3_ast_vector_to_string(Z3_context c, Z3_ast_vector v);

/* Unsat core of the last unsatisfiable check as tracking assumption ASTs. */
Z3_ast_vector Z3_solver_get_unsat_core(Z3_context c, Z3_solver s);

/* ---- Quantifiers (the _const forms; no De-Bruijn bookkeeping needed) ----
 * Bound variables are supplied as constant Z3_app handles (name + sort); the
 * text front end binds them by name in the rendered (forall/exists ...). */
typedef struct Z3rsPattern *Z3_pattern;

/* Build a (multi-)pattern trigger (t1 ... tn) from term handles. */
Z3_pattern Z3_mk_pattern(Z3_context c, unsigned num_patterns,
                         Z3_ast const terms[]);
/* forall/exists over the constant bound variables, with optional patterns and
 * weight. Result sort is Bool. */
Z3_ast Z3_mk_forall_const(Z3_context c, unsigned weight, unsigned num_bound,
                          Z3_app const bound[], unsigned num_patterns,
                          Z3_pattern const patterns[], Z3_ast body);
Z3_ast Z3_mk_exists_const(Z3_context c, unsigned weight, unsigned num_bound,
                          Z3_app const bound[], unsigned num_patterns,
                          Z3_pattern const patterns[], Z3_ast body);
Z3_ast Z3_mk_quantifier_const(Z3_context c, bool is_forall, unsigned weight,
                              unsigned num_bound, Z3_app const bound[],
                              unsigned num_patterns,
                              Z3_pattern const patterns[], Z3_ast body);

/* ---- Algebraic datatypes ----
 * Declared to the front end with (declare-datatype ...). A Z3_constructor
 * captures a constructor spec; a NULL field sort (with its sort_refs index)
 * denotes a recursive reference to the datatype being defined. */
typedef Z3_sort Z3_sort_opt;
typedef struct Z3rsConstructor *Z3_constructor;
typedef struct Z3rsConstructorList *Z3_constructor_list;

Z3_constructor Z3_mk_constructor(Z3_context c, Z3_symbol name,
                                 Z3_symbol recognizer, unsigned num_fields,
                                 Z3_symbol const field_names[],
                                 Z3_sort_opt const sorts[],
                                 unsigned sort_refs[]);
Z3_sort Z3_mk_datatype(Z3_context c, Z3_symbol name,
                       unsigned num_constructors,
                       Z3_constructor constructors[]);
/* Hand back the constructor, its (_ is name) tester, and one accessor per
 * field, as Z3_func_decl handles. NULL out-pointers are skipped. */
void Z3_query_constructor(Z3_context c, Z3_constructor constr,
                          unsigned num_fields, Z3_func_decl *constructor,
                          Z3_func_decl *tester, Z3_func_decl accessors[]);
Z3_constructor_list Z3_mk_constructor_list(Z3_context c,
                                           unsigned num_constructors,
                                           Z3_constructor const constructors[]);
void Z3_del_constructor(Z3_context c, Z3_constructor constr);
void Z3_del_constructor_list(Z3_context c, Z3_constructor_list clist);

/* Enumeration sort: a datatype of nullary constructors. Fills enum_consts[i]
 * with each value's constructor decl and enum_testers[i] with its tester. */
Z3_sort Z3_mk_enumeration_sort(Z3_context c, Z3_symbol name, unsigned n,
                               Z3_symbol const enum_names[],
                               Z3_func_decl enum_consts[],
                               Z3_func_decl enum_testers[]);
/* Tuple sort: a single-constructor datatype. Writes the constructor decl to
 * *mk_tuple_decl and the projection (accessor) decls to proj_decl. */
Z3_sort Z3_mk_tuple_sort(Z3_context c, Z3_symbol mk_tuple_name,
                         unsigned num_fields, Z3_symbol const field_names[],
                         Z3_sort const field_sorts[],
                         Z3_func_decl *mk_tuple_decl, Z3_func_decl proj_decl[]);

/* Set sort over `elem`, i.e. (Array elem Bool). */
Z3_sort Z3_mk_set_sort(Z3_context c, Z3_sort elem);

#ifdef __cplusplus
}
#endif

#endif /* Z3RS_H */

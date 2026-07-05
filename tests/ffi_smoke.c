/* Smoke test for the z3rs C ABI: compile against the static library and check a
 * couple of SMT-LIB2 evaluations end-to-end. */
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "z3rs.h"

int main(void) {
    char *v = (char *)z3rs_version();
    printf("z3rs version: %s\n", v);

    char *r1 = z3rs_eval_smtlib2_string(
        "(declare-const x Int)(assert (> x 5))(assert (< x 7))(check-sat)");
    printf("r1 = %s\n", r1);
    assert(strcmp(r1, "sat") == 0);
    z3rs_string_free(r1);

    char *r2 = z3rs_eval_smtlib2_string(
        "(declare-const x Int)(assert (> x 5))(assert (< x 5))(check-sat)");
    printf("r2 = %s\n", r2);
    assert(strcmp(r2, "unsat") == 0);
    z3rs_string_free(r2);

    char *r3 = z3rs_eval_smtlib2_string(
        "(declare-const x (_ BitVec 8))(assert (= (bvadd x #x01) #x10))"
        "(check-sat)(get-value (x))");
    printf("r3 = %s\n", r3);
    assert(strstr(r3, "sat") != NULL && strstr(r3, "#x0f") != NULL);
    z3rs_string_free(r3);

    /* Incremental session: state carries across eval calls, including push/pop. */
    Z3rsSession *s = z3rs_mk_session();
    z3rs_string_free(z3rs_session_eval(s, "(declare-const n Int)(assert (> n 0))"));
    char *s1 = z3rs_session_eval(s, "(push)(assert (< n 0))(check-sat)");
    printf("s1 = %s\n", s1);
    assert(strcmp(s1, "unsat") == 0); /* n>0 and n<0 */
    z3rs_string_free(s1);
    char *s2 = z3rs_session_eval(s, "(pop)(check-sat)");
    printf("s2 = %s\n", s2);
    assert(strcmp(s2, "sat") == 0); /* just n>0 after pop */
    z3rs_string_free(s2);
    z3rs_del_session(s);

    /* Solver-object convenience API (Z3_solver_check-style handle surface). */
    Z3rsSession *t = z3rs_mk_session();
    z3rs_string_free(z3rs_session_eval(t, "(declare-const k Int)(assert (> k 3))"));
    assert(z3rs_session_check(t) == 1); /* sat */
    assert(z3rs_session_push(t) == 0);
    z3rs_string_free(z3rs_session_eval(t, "(assert (< k 3))"));
    assert(z3rs_session_check(t) == 0); /* unsat: k>3 and k<3 */
    assert(z3rs_session_pop(t) == 0);
    assert(z3rs_session_check(t) == 1); /* sat again */
    assert(z3rs_session_reset(t) == 0);
    z3rs_del_session(t);

    /* Z3-compatible drop-in slice: a C program using the real Z3 API names. */
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    printf("Z3_get_full_version: %s\n", Z3_get_full_version());
    /* State persists across Z3_eval_smtlib2_string calls; result owned by ctx. */
    const char *e1 = Z3_eval_smtlib2_string(ctx, "(declare-const z Int)(assert (> z 100))");
    (void)e1;
    const char *e2 = Z3_eval_smtlib2_string(ctx, "(assert (< z 100))(check-sat)");
    printf("Z3_eval = %s\n", e2);
    assert(strcmp(e2, "unsat") == 0); /* z>100 and z<100 */
    Z3_del_context(ctx);
    Z3_del_config(cfg);

    /* Handle-based object API: build terms and solve, the way a Z3 C test
     * program does. Find integer x with 3 < x and x < 4 -> unsat. */
    Z3_config cfg2 = Z3_mk_config();
    Z3_context hc = Z3_mk_context(cfg2);
    Z3_sort is = Z3_mk_int_sort(hc);
    Z3_ast x = Z3_mk_const(hc, Z3_mk_string_symbol(hc, "x"), is);
    Z3_ast three = Z3_mk_numeral(hc, "3", is);
    Z3_ast four = Z3_mk_numeral(hc, "4", is);
    Z3_solver sol = Z3_mk_solver(hc);
    Z3_solver_assert(hc, sol, Z3_mk_lt(hc, three, x)); /* 3 < x */
    Z3_solver_assert(hc, sol, Z3_mk_lt(hc, x, four));  /* x < 4 */
    int r = Z3_solver_check(hc, sol);
    printf("Z3_solver_check (3<x<4 over Int) = %d (expect -1/unsat)\n", r);
    assert(r == -1);

    /* A satisfiable build: x + y = 10 and x = 4 -> sat. */
    Z3_context hc2 = Z3_mk_context(cfg2);
    Z3_sort is2 = Z3_mk_int_sort(hc2);
    Z3_ast xx = Z3_mk_const(hc2, Z3_mk_string_symbol(hc2, "x"), is2);
    Z3_ast yy = Z3_mk_const(hc2, Z3_mk_string_symbol(hc2, "y"), is2);
    Z3_ast sum_args[2] = { xx, yy };
    Z3_ast sum = Z3_mk_add(hc2, 2, sum_args);
    Z3_ast ten = Z3_mk_numeral(hc2, "10", is2);
    Z3_ast four2 = Z3_mk_numeral(hc2, "4", is2);
    Z3_solver sol2 = Z3_mk_solver(hc2);
    Z3_solver_assert(hc2, sol2, Z3_mk_eq(hc2, sum, ten));
    Z3_solver_assert(hc2, sol2, Z3_mk_eq(hc2, xx, four2));
    assert(Z3_solver_check(hc2, sol2) == 1); /* sat: x=4, y=6 */
    /* Retrieve and render the model, like a Z3 find-model test program. */
    Z3_model model = Z3_solver_get_model(hc2, sol2);
    const char *mstr = Z3_model_to_string(hc2, model);
    printf("model =\n%s\n", mstr);
    assert(strstr(mstr, "x") != NULL && strstr(mstr, "4") != NULL);
    printf("ast(x+y) = %s\n", Z3_ast_to_string(hc2, sum));
    Z3_del_context(hc2);
    Z3_del_context(hc);
    Z3_del_config(cfg2);

    puts("ffi_smoke: OK");
    return 0;
}

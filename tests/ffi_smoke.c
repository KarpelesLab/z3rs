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

    /* ---- Extended surface: rc context, refcounting, Int+BV+array build,
     * per-solver push/pop, model read-back, quantified assertion. ---- */
    {
        unsigned maj = 0, minr = 0, bld = 0, rev = 0;
        Z3_get_version(&maj, &minr, &bld, &rev);
        printf("Z3_get_version: %u.%u.%u.%u\n", maj, minr, bld, rev);
        assert(maj == 4 && minr == 17);

        /* Reference-counted context (NULL config is accepted). */
        Z3_context rc = Z3_mk_context_rc(NULL);

        Z3_sort ints = Z3_mk_int_sort(rc);
        Z3_sort bv8 = Z3_mk_bv_sort(rc, 8);
        Z3_sort arr = Z3_mk_array_sort(rc, ints, ints);
        assert(Z3_get_sort_kind(rc, arr) == 5);     /* Z3_ARRAY_SORT */
        assert(Z3_get_sort_kind(rc, bv8) == 4);     /* Z3_BV_SORT */
        assert(Z3_get_bv_sort_size(rc, bv8) == 8);
        assert(Z3_get_sort_kind(rc, Z3_get_array_sort_range(rc, arr)) == 2); /* Int */
        printf("array sort = %s\n", Z3_sort_to_string(rc, arr));

        /* Int:  a > 5  and  a < 7   =>   a = 6 */
        Z3_ast a = Z3_mk_const(rc, Z3_mk_string_symbol(rc, "a"), ints);
        Z3_inc_ref(rc, a);
        Z3_ast a_gt5 = Z3_mk_gt(rc, a, Z3_mk_int(rc, 5, ints));
        Z3_ast a_lt7 = Z3_mk_lt(rc, a, Z3_mk_int(rc, 7, ints));

        /* BV:  v + 1 = 16  =>  v = 15 */
        Z3_ast v = Z3_mk_const(rc, Z3_mk_string_symbol(rc, "v"), bv8);
        Z3_inc_ref(rc, v);
        Z3_ast bvsum = Z3_mk_bvadd(rc, v, Z3_mk_int(rc, 1, bv8));
        Z3_ast bveq = Z3_mk_eq(rc, bvsum, Z3_mk_int(rc, 16, bv8));

        /* Array:  (select m 3) = 7 */
        Z3_ast m = Z3_mk_const(rc, Z3_mk_string_symbol(rc, "m"), arr);
        Z3_inc_ref(rc, m);
        Z3_ast sel = Z3_mk_select(rc, m, Z3_mk_int(rc, 3, ints));
        Z3_ast arreq = Z3_mk_eq(rc, sel, Z3_mk_int(rc, 7, ints));

        /* Int + Array live together in sol3. (The bit-vector constraint is
         * checked in its own solver below: this engine does not yet combine
         * the integer and bit-vector theories in a single check.) */
        Z3_solver sol3 = Z3_mk_solver(rc);
        Z3_solver_inc_ref(rc, sol3);
        Z3_solver_assert(rc, sol3, a_gt5);
        Z3_solver_assert(rc, sol3, a_lt7);
        Z3_solver_assert(rc, sol3, arreq);
        assert(Z3_solver_get_num_scopes(rc, sol3) == 0);
        assert(Z3_solver_check(rc, sol3) == 1); /* sat */

        Z3_model mdl = Z3_solver_get_model(rc, sol3);
        Z3_model_inc_ref(rc, mdl);
        const char *ms = Z3_model_to_string(rc, mdl);
        printf("rc model =\n%s\n", ms);
        assert(strstr(ms, "6") != NULL);  /* a = 6 read back from the model */

        /* Bit-vector constraint in an independent solver: v + 1 = 16 => 15. */
        Z3_solver bvsolver = Z3_mk_solver(rc);
        Z3_solver_assert(rc, bvsolver, bveq);
        assert(Z3_solver_check(rc, bvsolver) == 1); /* sat */
        Z3_model bvm = Z3_solver_get_model(rc, bvsolver);
        const char *bvms = Z3_model_to_string(rc, bvm);
        printf("bv model =\n%s\n", bvms);
        assert(strstr(bvms, "#x0f") != NULL); /* v = 15 */

        /* push a contradiction (a < 5), expect unsat, pop back to sat. */
        Z3_solver_push(rc, sol3);
        assert(Z3_solver_get_num_scopes(rc, sol3) == 1);
        Z3_solver_assert(rc, sol3, Z3_mk_lt(rc, a, Z3_mk_int(rc, 5, ints)));
        assert(Z3_solver_check(rc, sol3) == -1); /* a>5 and a<5 -> unsat */
        Z3_solver_pop(rc, sol3, 1);
        assert(Z3_solver_get_num_scopes(rc, sol3) == 0);
        assert(Z3_solver_check(rc, sol3) == 1); /* sat again */

        /* A second, independent solver in the same context sees none of the
         * assertions above. */
        Z3_solver sol4 = Z3_mk_solver(rc);
        Z3_solver_assert(rc, sol4, Z3_mk_lt(rc, a, Z3_mk_int(rc, 0, ints)));
        assert(Z3_solver_check(rc, sol4) == 1); /* only a<0 -> sat */

        /* Empty n-ary connective / arithmetic identities (divergence fix). */
        Z3_ast empty_and = Z3_mk_and(rc, 0, NULL);
        assert(empty_and != NULL && Z3_get_bool_value(rc, empty_and) == 1);
        Z3_ast empty_or = Z3_mk_or(rc, 0, NULL);
        assert(empty_or != NULL && Z3_get_bool_value(rc, empty_or) == -1);
        printf("empty add = %s, empty mul = %s\n",
               Z3_ast_to_string(rc, Z3_mk_add(rc, 0, NULL)),
               Z3_ast_to_string(rc, Z3_mk_mul(rc, 0, NULL)));

        /* Quantified assertion via the drop-in string entry point (same ABI). */
        const char *q = Z3_eval_smtlib2_string(
            rc, "(assert (forall ((x Int)) (=> (> x 0) (> (+ x 1) 0))))(check-sat)");
        printf("quantified = %s\n", q);
        assert(strcmp(q, "sat") == 0);

        Z3_model_dec_ref(rc, mdl);
        Z3_solver_dec_ref(rc, sol3);
        Z3_dec_ref(rc, a);
        Z3_dec_ref(rc, v);
        Z3_dec_ref(rc, m);
        Z3_del_context(rc);
    }

    puts("ffi_smoke: OK");
    return 0;
}

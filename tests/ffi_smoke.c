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

        /* ---- Structured value readback from the model ---- */
        /* Z3_model_eval: pull the concrete value of `a` back as a numeral AST. */
        Z3_ast a_val = NULL;
        bool ok = Z3_model_eval(rc, mdl, a, true, &a_val);
        assert(ok && a_val != NULL);
        assert(Z3_get_ast_kind(rc, a_val) == 0);   /* Z3_NUMERAL_AST */
        assert(Z3_is_numeral_ast(rc, a_val));
        printf("model_eval(a) numeral string = %s\n",
               Z3_get_numeral_string(rc, a_val));
        assert(strcmp(Z3_get_numeral_string(rc, a_val), "6") == 0);
        int a_int = -1;
        assert(Z3_get_numeral_int(rc, a_val, &a_int) && a_int == 6); /* a == 6 */
        long long a_i64 = 0;
        assert(Z3_get_numeral_int64(rc, a_val, &a_i64) && a_i64 == 6);

        /* Z3_model_get_const_interp over the model's parsed constant decls. */
        unsigned nconsts = Z3_model_get_num_consts(rc, mdl);
        printf("model has %u const(s)\n", nconsts);
        assert(nconsts >= 1);
        bool saw_a = false;
        for (unsigned ci = 0; ci < nconsts; ci++) {
            Z3_func_decl cd = Z3_model_get_const_decl(rc, mdl, ci);
            const char *cn = Z3_get_symbol_string(rc, Z3_get_decl_name(rc, cd));
            Z3_ast civ = Z3_model_get_const_interp(rc, mdl, cd);
            printf("  %s = %s\n", cn, Z3_get_numeral_string(rc, civ));
            if (strcmp(cn, "a") == 0) {
                saw_a = true;
                int cval = 0;
                assert(Z3_get_numeral_int(rc, civ, &cval) && cval == 6);
            }
        }
        assert(saw_a);

        /* Bit-vector value readback: evaluate v (== 15 == 0x0f) under bvm. */
        Z3_ast v_val = NULL;
        assert(Z3_model_eval(rc, bvm, v, true, &v_val) && v_val != NULL);
        assert(Z3_is_numeral_ast(rc, v_val));
        unsigned v_uint = 0;
        assert(Z3_get_numeral_uint(rc, v_val, &v_uint));
        printf("model_eval(v) = %u (0x%02x)\n", v_uint, v_uint);
        assert(v_uint == 0x0f); /* v == 0x0f */
        assert(strcmp(Z3_get_numeral_string(rc, v_val), "15") == 0);

        /* A non-numeral term is not a numeral AST. */
        assert(!Z3_is_numeral_ast(rc, a_gt5));
        assert(Z3_get_ast_kind(rc, a_gt5) == 1); /* Z3_APP_AST */

        Z3_model_dec_ref(rc, mdl);
        Z3_solver_dec_ref(rc, sol3);
        Z3_dec_ref(rc, a);
        Z3_dec_ref(rc, v);
        Z3_dec_ref(rc, m);
        Z3_del_context(rc);
    }

    /* ---- Unsat core via assert_and_track + Z3_solver_get_unsat_core ---- */
    {
        Z3_context uc = Z3_mk_context(NULL);
        Z3_sort ints = Z3_mk_int_sort(uc);
        Z3_sort bools = Z3_mk_bool_sort(uc);
        Z3_ast x = Z3_mk_const(uc, Z3_mk_string_symbol(uc, "x"), ints);
        /* Tracking literals p1, p2 for two contradictory constraints. */
        Z3_ast p1 = Z3_mk_const(uc, Z3_mk_string_symbol(uc, "p1"), bools);
        Z3_ast p2 = Z3_mk_const(uc, Z3_mk_string_symbol(uc, "p2"), bools);
        Z3_solver s = Z3_mk_solver(uc);
        Z3_solver_assert_and_track(uc, s, Z3_mk_gt(uc, x, Z3_mk_int(uc, 0, ints)), p1);
        Z3_solver_assert_and_track(uc, s, Z3_mk_lt(uc, x, Z3_mk_int(uc, 0, ints)), p2);
        assert(Z3_solver_check(uc, s) == -1); /* x>0 and x<0 -> unsat */
        Z3_ast_vector core = Z3_solver_get_unsat_core(uc, s);
        unsigned n = Z3_ast_vector_size(uc, core);
        printf("unsat core size = %u: %s\n", n, Z3_ast_vector_to_string(uc, core));
        assert(n == 2); /* both tracked assumptions are in the core */
        bool saw_p1 = false, saw_p2 = false;
        for (unsigned i = 0; i < n; i++) {
            const char *nm = Z3_ast_to_string(uc, Z3_ast_vector_get(uc, core, i));
            if (strcmp(nm, "p1") == 0) saw_p1 = true;
            if (strcmp(nm, "p2") == 0) saw_p2 = true;
        }
        assert(saw_p1 && saw_p2);
        Z3_del_context(uc);
    }

    /* ---- Representative real-world program: an algebraic List datatype ----
     * List = nil | cons(head: Int, tail: List). Build cons(1, cons(2, nil)),
     * assert head(l) == 1 and l != nil, solve, and read the model back. */
    {
        Z3_context dc = Z3_mk_context(NULL);
        Z3_sort intsort = Z3_mk_int_sort(dc);

        /* cons(head: Int, tail: List): a NULL field sort with sort_ref = 0 means
         * "the datatype being defined" (the recursive tail). */
        Z3_symbol head_name = Z3_mk_string_symbol(dc, "head");
        Z3_symbol tail_name = Z3_mk_string_symbol(dc, "tail");
        Z3_symbol cons_fields[2] = { head_name, tail_name };
        Z3_sort_opt cons_field_sorts[2] = { intsort, NULL }; /* NULL = List */
        unsigned cons_field_refs[2] = { 0, 0 };
        Z3_constructor cons_ctor = Z3_mk_constructor(
            dc, Z3_mk_string_symbol(dc, "cons"), Z3_mk_string_symbol(dc, "is_cons"),
            2, cons_fields, cons_field_sorts, cons_field_refs);
        /* nil: a nullary constructor. */
        Z3_constructor nil_ctor = Z3_mk_constructor(
            dc, Z3_mk_string_symbol(dc, "nil"), Z3_mk_string_symbol(dc, "is_nil"),
            0, NULL, NULL, NULL);

        Z3_constructor ctors[2] = { nil_ctor, cons_ctor };
        Z3_sort list_sort = Z3_mk_datatype(dc, Z3_mk_string_symbol(dc, "List"),
                                           2, ctors);
        assert(Z3_get_sort_kind(dc, list_sort) == 6); /* Z3_DATATYPE_SORT */
        printf("List sort = %s\n", Z3_sort_to_string(dc, list_sort));

        /* Pull back the constructor / tester / accessor decls. */
        Z3_func_decl cons_decl, cons_tester, cons_accessors[2];
        Z3_query_constructor(dc, cons_ctor, 2, &cons_decl, &cons_tester,
                             cons_accessors);
        Z3_func_decl head_decl = cons_accessors[0];
        Z3_func_decl nil_decl, nil_tester;
        Z3_query_constructor(dc, nil_ctor, 0, &nil_decl, &nil_tester, NULL);

        /* nil, cons(2, nil), cons(1, cons(2, nil)). */
        Z3_ast nil = Z3_mk_app(dc, nil_decl, 0, NULL);
        Z3_ast two = Z3_mk_numeral(dc, "2", intsort);
        Z3_ast one = Z3_mk_numeral(dc, "1", intsort);
        Z3_ast inner_args[2] = { two, nil };
        Z3_ast inner = Z3_mk_app(dc, cons_decl, 2, inner_args); /* cons(2,nil) */
        Z3_ast outer_args[2] = { one, inner };
        Z3_ast lst = Z3_mk_app(dc, cons_decl, 2, outer_args); /* cons(1,..) */
        printf("term = %s\n", Z3_ast_to_string(dc, lst));

        /* l is a List constant; assert l = cons(1, cons(2, nil)). */
        Z3_ast l = Z3_mk_const(dc, Z3_mk_string_symbol(dc, "l"), list_sort);
        Z3_solver ds = Z3_mk_solver(dc);
        Z3_solver_assert(dc, ds, Z3_mk_eq(dc, l, lst));
        /* Property: head(l) == 1 and l is a cons (not nil). */
        Z3_ast head_l = Z3_mk_app(dc, head_decl, 1, &l);
        Z3_solver_assert(dc, ds, Z3_mk_eq(dc, head_l, one));
        Z3_ast is_cons_l = Z3_mk_app(dc, cons_tester, 1, &l);
        Z3_solver_assert(dc, ds, is_cons_l);
        assert(Z3_solver_check(dc, ds) == 1); /* sat */

        /* Read head(l) back from the model: it must be 1. */
        Z3_model dm = Z3_solver_get_model(dc, ds);
        Z3_ast hv = NULL;
        assert(Z3_model_eval(dc, dm, head_l, true, &hv) && hv != NULL);
        int hval = -1;
        assert(Z3_get_numeral_int(dc, hv, &hval));
        printf("model: head(l) = %d\n", hval);
        assert(hval == 1);

        /* Contradiction: additionally assert l is nil -> unsat. */
        Z3_solver_push(dc, ds);
        Z3_ast is_nil_l = Z3_mk_app(dc, nil_tester, 1, &l);
        Z3_solver_assert(dc, ds, is_nil_l);
        assert(Z3_solver_check(dc, ds) == -1); /* cons and nil -> unsat */
        Z3_solver_pop(dc, ds, 1);

        Z3_del_constructor(dc, cons_ctor);
        Z3_del_constructor(dc, nil_ctor);
        Z3_del_context(dc);
        puts("datatype program: OK");
    }

    /* ---- Representative real-world program: a quantified assertion ----
     * Assert  forall x:Int. f(x) >= 0  and  f(3) < 0  -> unsat. */
    {
        Z3_context qc = Z3_mk_context(NULL);
        Z3_sort intsort = Z3_mk_int_sort(qc);

        /* f : Int -> Int */
        Z3_sort fdom[1] = { intsort };
        Z3_func_decl f = Z3_mk_func_decl(qc, Z3_mk_string_symbol(qc, "f"), 1,
                                         fdom, intsort);

        /* Bound variable x:Int as a constant Z3_app. */
        Z3_ast x = Z3_mk_const(qc, Z3_mk_string_symbol(qc, "x"), intsort);
        Z3_ast fx = Z3_mk_app(qc, f, 1, &x);
        Z3_ast zero = Z3_mk_numeral(qc, "0", intsort);
        Z3_ast body = Z3_mk_ge(qc, fx, zero); /* f(x) >= 0 */

        /* Pattern { f(x) } to trigger instantiation. */
        Z3_pattern pat = Z3_mk_pattern(qc, 1, &fx);
        Z3_app bound[1] = { x };
        Z3_pattern pats[1] = { pat };
        Z3_ast forall = Z3_mk_forall_const(qc, 0, 1, bound, 1, pats, body);
        printf("quantifier = %s\n", Z3_ast_to_string(qc, forall));

        Z3_ast three = Z3_mk_numeral(qc, "3", intsort);
        Z3_ast f3 = Z3_mk_app(qc, f, 1, &three);
        Z3_ast f3_lt0 = Z3_mk_lt(qc, f3, zero); /* f(3) < 0 */

        Z3_solver qs = Z3_mk_solver(qc);
        Z3_solver_assert(qc, qs, forall);
        Z3_solver_assert(qc, qs, f3_lt0);
        int qr = Z3_solver_check(qc, qs);
        printf("forall f(x)>=0 and f(3)<0 => %d (expect -1/unsat)\n", qr);
        assert(qr == -1);

        /* The existential dual is satisfiable on its own: exists x. f(x) < 0. */
        Z3_context ec = Z3_mk_context(NULL);
        Z3_sort eint = Z3_mk_int_sort(ec);
        Z3_sort efdom[1] = { eint };
        Z3_func_decl ef = Z3_mk_func_decl(ec, Z3_mk_string_symbol(ec, "g"), 1,
                                          efdom, eint);
        Z3_ast ex = Z3_mk_const(ec, Z3_mk_string_symbol(ec, "y"), eint);
        Z3_ast egx = Z3_mk_app(ec, ef, 1, &ex);
        Z3_ast ezero = Z3_mk_numeral(ec, "0", eint);
        Z3_ast ebody = Z3_mk_lt(ec, egx, ezero);
        Z3_app ebound[1] = { ex };
        Z3_ast exists = Z3_mk_exists_const(ec, 0, 1, ebound, 0, NULL, ebody);
        Z3_solver es = Z3_mk_solver(ec);
        Z3_solver_assert(ec, es, exists);
        assert(Z3_solver_check(ec, es) == 1); /* sat */
        Z3_del_context(ec);

        Z3_del_context(qc);
        puts("quantifier program: OK");
    }

    /* ---- Enumeration + tuple sorts ---- */
    {
        Z3_context nc = Z3_mk_context(NULL);
        /* enum Color { Red, Green, Blue } */
        Z3_symbol cnames[3] = { Z3_mk_string_symbol(nc, "Red"),
                                Z3_mk_string_symbol(nc, "Green"),
                                Z3_mk_string_symbol(nc, "Blue") };
        Z3_func_decl cconsts[3], ctesters[3];
        Z3_sort color = Z3_mk_enumeration_sort(
            nc, Z3_mk_string_symbol(nc, "Color"), 3, cnames, cconsts, ctesters);
        assert(Z3_get_sort_kind(nc, color) == 6);
        Z3_ast red = Z3_mk_app(nc, cconsts[0], 0, NULL);
        Z3_ast green = Z3_mk_app(nc, cconsts[1], 0, NULL);
        Z3_ast col = Z3_mk_const(nc, Z3_mk_string_symbol(nc, "col"), color);
        Z3_solver ns = Z3_mk_solver(nc);
        Z3_solver_assert(nc, ns, Z3_mk_eq(nc, col, red));
        Z3_solver_assert(nc, ns, Z3_mk_eq(nc, col, green)); /* Red != Green */
        assert(Z3_solver_check(nc, ns) == -1); /* unsat: distinct enum values */

        /* tuple Pair(first: Int, second: Int) */
        Z3_sort intsort = Z3_mk_int_sort(nc);
        Z3_symbol pfields[2] = { Z3_mk_string_symbol(nc, "first"),
                                 Z3_mk_string_symbol(nc, "second") };
        Z3_sort psorts[2] = { intsort, intsort };
        Z3_func_decl mk_pair, projs[2];
        Z3_sort pair = Z3_mk_tuple_sort(nc, Z3_mk_string_symbol(nc, "Pair"), 2,
                                        pfields, psorts, &mk_pair, projs);
        assert(Z3_get_sort_kind(nc, pair) == 6);
        Z3_ast pa[2] = { Z3_mk_numeral(nc, "3", intsort),
                         Z3_mk_numeral(nc, "4", intsort) };
        Z3_ast p = Z3_mk_app(nc, mk_pair, 2, pa); /* mk-Pair(3,4) */
        Z3_ast first_p = Z3_mk_app(nc, projs[0], 1, &p); /* first(p) == 3 */
        Z3_solver ps = Z3_mk_solver(nc);
        Z3_solver_assert(nc, ps, Z3_mk_eq(nc, first_p, Z3_mk_numeral(nc, "4", intsort)));
        assert(Z3_solver_check(nc, ps) == -1); /* first(mk-Pair(3,4)) != 4 */
        Z3_del_context(nc);
        puts("enum+tuple program: OK");
    }

    puts("ffi_smoke: OK");
    return 0;
}

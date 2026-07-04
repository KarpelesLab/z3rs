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

    puts("ffi_smoke: OK");
    return 0;
}

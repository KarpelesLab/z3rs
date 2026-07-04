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

    puts("ffi_smoke: OK");
    return 0;
}

//! Black-box end-to-end tests exercising z3rs's public API the way the CLI does:
//! SMT-LIB2 scripts through `run_smt2` and DIMACS CNF through `parse_dimacs`.

use z3rs::cmd_context::run_smt2;
use z3rs::sat::{SatResult, parse_dimacs};

#[test]
fn smt2_qf_uf_transitivity_unsat() {
    let script = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U) (declare-const b U) (declare-const c U)
        (assert (= a b)) (assert (= b c)) (assert (not (= a c)))
        (check-sat)
    ";
    assert_eq!(run_smt2(script).unwrap(), vec!["unsat"]);
}

#[test]
fn smt2_qf_uf_congruence_with_let() {
    let script = "
        (declare-sort U 0)
        (declare-fun f (U U) U)
        (declare-const a U) (declare-const b U)
        (assert (let ((e (= a b))) e))
        (assert (not (= (f a a) (f b b))))
        (check-sat)
    ";
    assert_eq!(run_smt2(script).unwrap(), vec!["unsat"]);
}

#[test]
fn smt2_satisfiable_and_push_pop() {
    let script = "
        (declare-const p Bool) (declare-const q Bool)
        (assert (=> p q))
        (check-sat)
        (push 1)
          (assert p) (assert (not q))
          (check-sat)
        (pop 1)
        (check-sat)
    ";
    assert_eq!(run_smt2(script).unwrap(), vec!["sat", "unsat", "sat"]);
}

#[test]
fn dimacs_sat_and_unsat() {
    // (x1 ∨ x2) ∧ ¬x1  → sat
    let mut sat = parse_dimacs("p cnf 2 2\n1 2 0\n-1 0\n").unwrap();
    assert_eq!(sat.solve(), SatResult::Sat);

    // (x1) ∧ (¬x1)  → unsat
    let mut unsat = parse_dimacs("p cnf 1 2\n1 0\n-1 0\n").unwrap();
    assert_eq!(unsat.solve(), SatResult::Unsat);
}

#[test]
fn smt2_reports_errors() {
    assert!(run_smt2("(assert (= a b))").is_err()); // undeclared symbols
    assert!(run_smt2("(check-sat").is_err()); // unbalanced parens
}

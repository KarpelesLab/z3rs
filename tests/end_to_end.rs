//! Black-box end-to-end tests exercising z3rs's public API the way the CLI does:
//! SMT-LIB2 scripts through `run_smt2` and DIMACS CNF through `parse_dimacs`.

use z3rs::cmd_context::run_smt2;
use z3rs::sat::{SatResult, check_drat_text, parse_dimacs};

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
    // Undeclared symbols are reported as `(error …)` and the script continues
    // (z3's behaviour), rather than aborting the whole run.
    let out = run_smt2("(assert (= a b))").unwrap();
    assert!(out.iter().any(|l| l.contains("unknown constant a")));
    assert!(run_smt2("(check-sat").is_err()); // unbalanced parens still abort
}

#[test]
fn datalog_reachability_frontend() {
    // The `-dl` frontend engine: transitive closure over a small graph.
    let prog = z3rs::muz::parse(
        "edge(1,2). edge(2,3). edge(3,4).
         path(X,Y) :- edge(X,Y).
         path(X,Z) :- edge(X,Y), path(Y,Z).",
    )
    .unwrap();
    let model = z3rs::muz::evaluate(&prog);
    let reach = |a: &str, b: &str| {
        model.holds(&z3rs::muz::Atom {
            pred: "path".into(),
            args: vec![
                z3rs::muz::Term::Const(a.into()),
                z3rs::muz::Term::Const(b.into()),
            ],
        })
    };
    assert!(reach("1", "4")); // 1→2→3→4
    assert!(!reach("4", "1")); // no path back
}

#[test]
fn drat_frontend_checks_refutation() {
    // The `-drat` frontend engine: a valid DRUP refutation of an UNSAT CNF.
    let cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
    assert!(check_drat_text(cnf, "2 0\n-2 0\n0\n").is_ok());
    // A bogus proof is rejected.
    assert!(check_drat_text("p cnf 2 1\n1 2 0\n", "1 0\n0\n").is_err());
}

/// Run `script` on a thread with an ordinary 8 MiB stack (the library's callers
/// do not get the CLI's enlarged one).
fn run_on_default_stack(script: String) -> Vec<String> {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || run_smt2(&script).unwrap())
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn smt2_deep_nesting_does_not_exhaust_the_stack() {
    const N: usize = 30_000;
    let decls = "(declare-fun x () Int)(declare-fun p () Bool)";
    // A deep conjunction, sum, and `let` chain, each decided and evaluated.
    let and = format!(
        "{decls}(assert {}(> x 0){})(check-sat)(eval x)",
        "(and p ".repeat(N),
        ")".repeat(N)
    );
    assert_eq!(run_on_default_stack(and), vec!["sat", "1"]);
    let sum = format!(
        "{decls}(assert (= {}x{} {}))(check-sat)(eval x)",
        "(+ 1 ".repeat(N),
        ")".repeat(N),
        N + 7
    );
    assert_eq!(run_on_default_stack(sum), vec!["sat", "7"]);
    let mut chain = format!("{decls}(assert ");
    for i in 0..N {
        let prev = if i == 0 {
            "x".to_string()
        } else {
            format!("a{}", i - 1)
        };
        chain += &format!("(let ((a{i} (+ {prev} 1))) ");
    }
    chain += &format!(
        "(= a{} {}){})(check-sat)(eval x)",
        N - 1,
        N + 3,
        ")".repeat(N)
    );
    assert_eq!(run_on_default_stack(chain), vec!["sat", "3"]);
}

/// A square root equation whose nlsat model has values of degree 24: the
/// exact value of a variable substituted away would be of degree in the
/// thousands, so the goal stays undecided instead of running for minutes.
#[test]
fn smt2_nra_model_completion_is_bounded() {
    let script = "(declare-const x Real)(declare-const y Real)
        (assert (>= x 1.0))
        (assert (>= y (- 1.0)))
        (assert (= (+ (^ x 0.5) (+ 3.0 (^ (+ y y) 0.5))) x))
        (assert (= (+ (* y 1.0) (* y x)) (^ (* 2.0 x) 0.5)))
        (assert (< (+ x y) (+ (+ x y) (^ x 0.5))))
        (check-sat)";
    assert_eq!(run_smt2(script).unwrap(), vec!["unknown"]);
}

/// An equation fixes the real for each integer: with the integer first in
/// nlsat's variable order the sample is a solution, with the real first branch
/// and bound chases the integer root by root.
#[test]
fn smt2_mixed_integer_real_nlsat() {
    let script = "(declare-fun x0 () Int)(declare-fun x1 () Real)
        (assert (distinct (+ (+ (* (- 2.0) x1) 1.0) (* x0 x1))
            (+ (* (+ (* (- 3.0) x0) (- 2.0)) (+ (* 4.0 x1) 5.0))
               (+ (* (- 4.0) x0) (* 0.0 x0) 1.0))))
        (assert (<= (+ (* x0 x0) (* x1 x1 x1) (* x0 x0 x0)) (- 3.0)))
        (assert (<= (+ (+ (* (- 3.0) x0) 4.0) (* x0 x1 x0))
            (+ (+ (* (- 4.0) x0) (* 0.0 x1) (- 5.0)) (+ (* (- 3.0) x1) (- 4.0))
               (+ (* 0.0 x0) 9.0) (- 5.0))))
        (assert (< (+ (* x1 x1 x0) (* (+ (* (- 4.0) x1) (* 1.0 x1) (- 3.0)) (+ (* 3.0 x1) (- 3.0))) 7.0)
            7.0))
        (assert (= (+ (* x0 x1) (* x0 x0 x1)
                      (* (+ (* (- 2.0) x0) (- 9.0)) (+ (* (- 2.0) x0) (* (- 1.0) x1) (- 4.0))))
            4.0))
        (check-sat)";
    assert_eq!(run_smt2(script).unwrap(), vec!["sat"]);
}

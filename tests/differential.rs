//! Differential testing against upstream Z3 (the reference oracle, per
//! `ROADMAP.md` §7). Each script's `(check-sat)` verdicts from z3rs's
//! [`run_smt2`] are compared to those of the `z3` binary. If `z3` is not on
//! `PATH` the whole suite is skipped, so it stays green on machines without it.
//!
//! The corpus is deliberately confined to the fragment z3rs decides today
//! (QF_UF / QF_LRA / QF_LIA with the supported operators); as coverage grows,
//! extend `CORPUS`.

use std::process::Command;

use z3rs::cmd_context::run_smt2;

/// A labelled SMT-LIB2 script.
struct Case {
    name: &'static str,
    script: &'static str,
}

const CORPUS: &[Case] = &[
    Case {
        name: "qf_uf_transitivity",
        script: "(declare-sort U 0)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (= a b))(assert (= b c))(assert (not (= a c)))(check-sat)",
    },
    Case {
        name: "qf_uf_congruence",
        script: "(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)(declare-const b U)
                 (assert (= a b))(assert (not (= (f a) (f b))))(check-sat)",
    },
    Case {
        name: "qf_uf_sat",
        script: "(declare-sort U 0)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (= a b))(assert (not (= a c)))(check-sat)",
    },
    Case {
        name: "bool_contradiction",
        script: "(declare-const p Bool)(assert (and p (not p)))(check-sat)",
    },
    Case {
        name: "bool_tautology_sat",
        script: "(declare-const p Bool)(assert (or p (not p)))(check-sat)",
    },
    Case {
        name: "qf_lra_bounds_unsat",
        script: "(declare-const x Real)(declare-const y Real)
                 (assert (>= x 1))(assert (>= y 1))(assert (<= (+ x y) 1))(check-sat)",
    },
    Case {
        name: "qf_lra_bounds_sat",
        script: "(declare-const x Real)(assert (>= x 3))(assert (<= x 5))(check-sat)",
    },
    Case {
        name: "qf_lra_strict_cycle",
        script: "(declare-const x Real)(declare-const y Real)
                 (assert (< x y))(assert (< y x))(check-sat)",
    },
    Case {
        name: "qf_lia_integrality_unsat",
        script: "(declare-const x Int)(assert (< 3 x))(assert (< x 4))(check-sat)",
    },
    Case {
        name: "qf_lia_divisibility_sat",
        script: "(declare-const x Int)(assert (<= 3 (* 2 x)))(assert (<= (* 2 x) 5))(check-sat)",
    },
    Case {
        name: "qf_lia_bounds_sat",
        script: "(declare-const x Int)(assert (<= 3 x))(assert (<= x 5))(check-sat)",
    },
    Case {
        name: "uf_int_congruence_unsat",
        script: "(declare-fun f (Int) Int)(declare-const x Int)(declare-const y Int)
                 (assert (= x y))(assert (not (= (f x) (f y))))(check-sat)",
    },
    Case {
        name: "disequality_pin_unsat",
        script: "(declare-const x Int)(assert (<= x 5))(assert (>= x 5))(assert (not (= x 5)))(check-sat)",
    },
    Case {
        name: "ite_arith_sat",
        script: "(declare-const x Int)(assert (= x (ite (< x 0) 1 2)))(check-sat)",
    },
    Case {
        name: "let_nested_sat",
        script: "(declare-const p Bool)(declare-const q Bool)
                 (assert (let ((x p)) (let ((x q)) (or x (not x)))))(check-sat)",
    },
    Case {
        name: "define_fun_unsat",
        script: "(declare-const x Int)(define-fun bound () Int 10)(define-fun below ((a Int)(b Int)) Bool (< a b))
                 (assert (below x bound))(assert (>= x 10))(check-sat)",
    },
    Case {
        name: "distinct_uf_unsat",
        script: "(declare-sort U 0)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (distinct a b c))(assert (= a b))(check-sat)",
    },
    Case {
        name: "distinct_bool_pigeonhole",
        script: "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)(assert (distinct a b c))(check-sat)",
    },
    Case {
        name: "distinct_int_sat",
        script: "(declare-const a Int)(declare-const b Int)(declare-const c Int)
                 (assert (distinct a b c))(assert (<= 0 a))(assert (<= a 2))(assert (<= 0 b))(assert (<= b 2))
                 (assert (<= 0 c))(assert (<= c 2))(check-sat)",
    },
    Case {
        name: "real_division_sat",
        script: "(declare-const x Real)(assert (= x (/ 1 3)))(assert (= (* 3 x) 1))(check-sat)",
    },
    Case {
        name: "implies_modus_ponens",
        script: "(declare-const p Bool)(declare-const q Bool)(assert (=> p q))(assert p)(assert (not q))(check-sat)",
    },
    Case {
        name: "xor_unsat",
        script: "(declare-const p Bool)(declare-const q Bool)(assert (xor p q))(assert (= p q))(check-sat)",
    },
    Case {
        name: "chained_lt_unsat",
        script: "(declare-const x Int)(declare-const y Int)(declare-const z Int)
                 (assert (< x y z))(assert (< z x))(check-sat)",
    },
    Case {
        name: "int_div_mod_fold",
        script: "(assert (not (= (div 7 3) 2)))(check-sat)",
    },
    Case {
        name: "mod_negative",
        script: "(assert (not (= (mod (- 7) 3) 2)))(check-sat)",
    },
    Case {
        name: "abs_constant",
        script: "(declare-const x Int)(assert (= x (abs (- 5))))(assert (not (= x 5)))(check-sat)",
    },
    Case {
        name: "to_real_value",
        script: "(declare-const x Int)(declare-const y Real)
                 (assert (= y (to_real x)))(assert (= x 3))(assert (not (= y 3.0)))(check-sat)",
    },
    Case {
        name: "minus_nary_fold",
        script: "(declare-const x Int)(assert (= (- 10 1 2 3) x))(assert (not (= x 4)))(check-sat)",
    },
    Case {
        name: "term_ite_unsat",
        script: "(declare-const b Bool)(declare-const x Int)
                 (assert (= x (ite b 1 2)))(assert b)(assert (not (= x 1)))(check-sat)",
    },
    Case {
        name: "term_ite_selfref_sat",
        script: "(declare-const x Int)(assert (= x (ite (< x 0) 1 2)))(check-sat)",
    },
    Case {
        name: "nested_term_ite_unsat",
        script: "(declare-const x Int)(assert (> (+ (ite (> x 0) x 0) 1) 100))(assert (< x 50))(check-sat)",
    },
    Case {
        name: "parity_equation_unsat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* 2 x) (+ (* 2 y) 1)))(check-sat)",
    },
    Case {
        name: "divisibility_unsat",
        script: "(declare-const x Int)(assert (= (* 3 x) 7))(check-sat)",
    },
    Case {
        name: "nelson_oppen_lia_unsat",
        script: "(declare-sort S 0)(declare-fun f (Int) S)(declare-const a S)
                 (declare-const x Int)(declare-const y Int)
                 (assert (<= x y))(assert (<= y x))(assert (= (f x) a))(assert (not (= (f y) a)))(check-sat)",
    },
    Case {
        name: "nelson_oppen_lra_unsat",
        script: "(declare-fun f (Real) Real)(declare-const x Real)(declare-const y Real)
                 (assert (<= x y))(assert (<= y x))(assert (not (= (f x) (f y))))(check-sat)",
    },
    Case {
        name: "nelson_oppen_sat",
        script: "(declare-sort S 0)(declare-fun f (Int) S)(declare-const a S)
                 (declare-const x Int)(declare-const y Int)
                 (assert (<= x y))(assert (= (f x) a))(assert (not (= (f y) a)))(check-sat)",
    },
    Case {
        name: "nelson_oppen_euf_to_arith_unsat",
        script: "(declare-sort S 0)(declare-fun f (S) Int)(declare-const a S)(declare-const b S)
                 (declare-const x Int)(declare-const y Int)
                 (assert (= a b))(assert (= (f a) x))(assert (= (f b) y))(assert (> x y))(check-sat)",
    },
    Case {
        name: "nary_xor",
        script: "(assert (xor true true true))(check-sat)",
    },
    Case {
        name: "nary_xor_vars",
        script: "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)
                 (assert (xor a b c))(assert (= a b))(assert c)(check-sat)",
    },
    Case {
        name: "congruence_int_fn_to_arith",
        script: "(declare-sort U 0)(declare-fun f (U) Int)(declare-const a U)(declare-const b U)
                 (assert (= a b))(assert (> (f a) (f b)))(check-sat)",
    },
    Case {
        name: "arith_eq_to_uf_compound",
        script: "(declare-fun f (Int) Int)(declare-const x Int)(declare-const y Int)
                 (assert (= (+ x y) 0))(assert (= x 0))(assert (distinct (f x) (f (- y))))(check-sat)",
    },
    Case {
        name: "lia_strict_between_unsat",
        script: "(declare-const x Int)(declare-const y Int)(assert (< x y))(assert (< y (+ x 1)))(check-sat)",
    },
    Case {
        name: "predicate_congruence_unsat",
        script: "(declare-sort U 0)(declare-fun p (U) Bool)(declare-const a U)(declare-const b U)
                 (assert (= a b))(assert (p a))(assert (not (p b)))(check-sat)",
    },
    Case {
        name: "predicate_congruence_2ary_unsat",
        script: "(declare-sort U 0)(declare-fun p (U U) Bool)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (= a b))(assert (p a c))(assert (not (p b c)))(check-sat)",
    },
    Case {
        name: "predicate_no_congruence_sat",
        script: "(declare-sort U 0)(declare-fun p (U) Bool)(declare-const a U)(declare-const b U)
                 (assert (p a))(assert (not (p b)))(check-sat)",
    },
    Case {
        name: "to_int_symbolic_unsat",
        script: "(declare-const x Real)(assert (= x 3.7))(assert (>= (to_int x) 4))(check-sat)",
    },
    Case {
        name: "to_int_floor_unsat",
        script: "(declare-const x Real)(assert (<= 2.0 x))(assert (< x 3.0))(assert (not (= (to_int x) 2)))(check-sat)",
    },
    Case {
        name: "array_row_same_unsat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const v Int)
                 (assert (not (= (select (store a i v) i) v)))(check-sat)",
    },
    Case {
        name: "array_row_other_unsat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const j Int)(declare-const v Int)
                 (assert (not (= i j)))(assert (not (= (select (store a i v) j) (select a j))))(check-sat)",
    },
    Case {
        name: "array_congruence_unsat",
        script: "(declare-const a (Array Int Int))(declare-const b (Array Int Int))(declare-const i Int)
                 (assert (= (select a i) 1))(assert (= (select b i) 2))(assert (= a b))(check-sat)",
    },
    Case {
        name: "array_store_sat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const v Int)
                 (assert (= (select (store a i v) i) v))(check-sat)",
    },
];

/// Run `z3` on a script, returning its `(check-sat)` verdict lines, or `None`
/// if the binary is unavailable or errored.
fn z3_verdicts(script: &str) -> Option<Vec<String>> {
    let out = Command::new("z3")
        .args(["-in"])
        .arg("-smt2")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .ok()
        .and_then(|mut child| {
            use std::io::Write;
            child.stdin.take()?.write_all(script.as_bytes()).ok()?;
            child.wait_with_output().ok()
        })?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&out.stdout);
    let verdicts: Vec<String> = text
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_string)
        .collect();
    Some(verdicts)
}

#[test]
fn matches_z3_on_corpus() {
    // Probe for z3 once; skip the whole suite if missing.
    if z3_verdicts("(check-sat)").is_none() {
        eprintln!("z3 not available — skipping differential suite");
        return;
    }

    let mut mismatches = Vec::new();
    for case in CORPUS {
        let ours = match run_smt2(case.script) {
            Ok(v) => v,
            Err(e) => {
                mismatches.push(format!("{}: z3rs error: {e}", case.name));
                continue;
            }
        };
        let Some(theirs) = z3_verdicts(case.script) else {
            mismatches.push(format!("{}: z3 failed to produce a verdict", case.name));
            continue;
        };
        // "unknown" from z3rs is always sound (an incomplete procedure declined
        // to guess), so it never counts as a mismatch against a definite z3
        // verdict — only sat-vs-unsat disagreements do.
        let disagree = ours.len() != theirs.len()
            || ours.iter().zip(&theirs).any(|(o, t)| o != "unknown" && o != t);
        if disagree {
            mismatches.push(format!(
                "{}: z3rs={ours:?} vs z3={theirs:?}",
                case.name
            ));
        }
    }
    assert!(mismatches.is_empty(), "differential mismatches:\n{}", mismatches.join("\n"));
}

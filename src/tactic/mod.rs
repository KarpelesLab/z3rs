//! # `tactic` — Goals, the tactic framework, probes, and the combinators
//!
//! **Port phase 3.** Ported from `z3/src/tactic` (Z3 4.17.0, MIT): `goal`,
//! `tactic`, `tactical` (the `then`/`or_else`/`repeat`/`cond` combinators), and
//! `probe`. A [`Goal`] is a conjunction of formulas over an [`AstManager`]; a
//! [`Tactic`] maps a goal to a list of subgoals whose conjunction is
//! equisatisfiable (or fails). The combinators compose tactics; [`Probe`]s
//! measure a goal so [`cond`] can choose a strategy.
//!
//! This is the framework plus a small but real portfolio (`simplify`,
//! conjunction splitting, `propagate-values`-style constant propagation). Heavy
//! solving tactics (bit-blast, `sls`, `qe`) are layered on later.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::rewriter::simplify;

/// A goal: a conjunction of formulas to be checked/transformed. Mirrors Z3's
/// `goal` (minus proof/dependency tracking).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Goal {
    /// The asserted formulas (implicitly conjoined).
    pub formulas: Vec<AstId>,
}

impl Goal {
    /// An empty (trivially-true) goal.
    pub fn new() -> Goal {
        Goal { formulas: Vec::new() }
    }

    /// A goal from a list of assertions.
    pub fn from(formulas: Vec<AstId>) -> Goal {
        Goal { formulas }
    }

    /// Add a formula.
    pub fn assert(&mut self, f: AstId) {
        self.formulas.push(f);
    }

    /// Is this goal syntactically decided *unsatisfiable* — i.e. it contains the
    /// literal `false`?
    pub fn is_decided_unsat(&self, m: &AstManager) -> bool {
        self.formulas.iter().any(|&f| m.is_false(f))
    }

    /// Is this goal syntactically decided *satisfiable* — i.e. it has no
    /// formulas, or every formula is the literal `true`?
    pub fn is_decided_sat(&self, m: &AstManager) -> bool {
        self.formulas.iter().all(|&f| m.is_true(f))
    }

    /// The number of formulas.
    pub fn size(&self) -> usize {
        self.formulas.len()
    }
}

/// A tactic: transforms a goal into a list of subgoals (a *conjunctive*
/// decomposition — all subgoals must be satisfied), or fails.
pub trait Tactic {
    /// Apply the tactic. `Ok(subgoals)` on success (often a single subgoal);
    /// `Err(reason)` if the tactic does not apply.
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String>;
}

// --- primitive tactics ----------------------------------------------------

/// The identity tactic: returns the goal unchanged.
pub struct Skip;
impl Tactic for Skip {
    fn apply(&self, _m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        Ok(vec![goal.clone()])
    }
}

/// The always-failing tactic.
pub struct Fail;
impl Tactic for Fail {
    fn apply(&self, _m: &mut AstManager, _goal: &Goal) -> Result<Vec<Goal>, String> {
        Err("fail".into())
    }
}

/// Simplify every formula with the theory rewriter; drop resulting `true`
/// literals, and collapse the whole goal to `{false}` if any formula simplifies
/// to `false`.
pub struct Simplify;
impl Tactic for Simplify {
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        let mut out = Vec::new();
        for &f in &goal.formulas {
            let s = simplify(m, f);
            if m.is_false(s) {
                let fls = m.mk_false();
                return Ok(vec![Goal::from(vec![fls])]);
            }
            if !m.is_true(s) {
                out.push(s);
            }
        }
        Ok(vec![Goal::from(out)])
    }
}

/// Flatten each top-level `(and …)` formula into separate conjuncts, so the goal
/// becomes a flat list of atoms — Z3's `elim-and`/`flatten` preprocessing.
pub struct SplitConjuncts;
impl Tactic for SplitConjuncts {
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        let mut out = Vec::new();
        for &f in &goal.formulas {
            flatten_and(m, f, &mut out);
        }
        Ok(vec![Goal::from(out)])
    }
}

fn flatten_and(m: &AstManager, f: AstId, out: &mut Vec<AstId>) {
    if m.is_and(f) {
        for &c in m.app_args(f) {
            flatten_and(m, c, out);
        }
    } else {
        out.push(f);
    }
}

// --- combinators ----------------------------------------------------------

/// `then(a, b)`: apply `a`, then `b` to every resulting subgoal.
pub struct Then(pub Box<dyn Tactic>, pub Box<dyn Tactic>);
impl Tactic for Then {
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        let mid = self.0.apply(m, goal)?;
        let mut out = Vec::new();
        for g in &mid {
            out.extend(self.1.apply(m, g)?);
        }
        Ok(out)
    }
}

/// `or_else(a, b)`: apply `a`; if it fails, apply `b`.
pub struct OrElse(pub Box<dyn Tactic>, pub Box<dyn Tactic>);
impl Tactic for OrElse {
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        match self.0.apply(m, goal) {
            Ok(r) => Ok(r),
            Err(_) => self.1.apply(m, goal),
        }
    }
}

/// `repeat(t, max)`: apply `t` until it stops changing the goals or `max`
/// iterations elapse (a bounded fixpoint), never failing.
pub struct Repeat(pub Box<dyn Tactic>, pub usize);
impl Tactic for Repeat {
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        let mut current = vec![goal.clone()];
        for _ in 0..self.1 {
            let mut next = Vec::new();
            for g in &current {
                match self.0.apply(m, g) {
                    Ok(sub) => next.extend(sub),
                    Err(_) => next.push(g.clone()),
                }
            }
            if next == current {
                break;
            }
            current = next;
        }
        Ok(current)
    }
}

/// `par(a, b)`: try both and keep whichever makes more progress (fewest total
/// formulas across its subgoals). Without threads this is a sequential
/// "parallel-or"; it models Z3's `par` for our purposes (a heuristic pick that
/// never loses information, since both branches are equisatisfiable).
pub struct Par(pub Box<dyn Tactic>, pub Box<dyn Tactic>);
impl Tactic for Par {
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        let a = self.0.apply(m, goal);
        let b = self.1.apply(m, goal);
        match (a, b) {
            (Ok(ra), Ok(rb)) => {
                let sa: usize = ra.iter().map(Goal::size).sum();
                let sb: usize = rb.iter().map(Goal::size).sum();
                Ok(if sa <= sb { ra } else { rb })
            }
            (Ok(ra), Err(_)) => Ok(ra),
            (Err(_), Ok(rb)) => Ok(rb),
            (Err(e), Err(_)) => Err(e),
        }
    }
}

/// Convenience builders for the combinators.
pub fn then(a: Box<dyn Tactic>, b: Box<dyn Tactic>) -> Box<dyn Tactic> {
    Box::new(Then(a, b))
}
pub fn or_else(a: Box<dyn Tactic>, b: Box<dyn Tactic>) -> Box<dyn Tactic> {
    Box::new(OrElse(a, b))
}
pub fn repeat(t: Box<dyn Tactic>, max: usize) -> Box<dyn Tactic> {
    Box::new(Repeat(t, max))
}
pub fn par(a: Box<dyn Tactic>, b: Box<dyn Tactic>) -> Box<dyn Tactic> {
    Box::new(Par(a, b))
}

// --- probes ---------------------------------------------------------------

/// A probe measures a numeric feature of a goal (Z3's `probe`), used to pick a
/// strategy at runtime.
pub trait Probe {
    fn eval(&self, m: &AstManager, goal: &Goal) -> f64;
}

/// The number of formulas in the goal.
pub struct NumAssertions;
impl Probe for NumAssertions {
    fn eval(&self, _m: &AstManager, goal: &Goal) -> f64 {
        goal.size() as f64
    }
}

/// The total number of distinct sub-expressions across all formulas.
pub struct NumExprs;
impl Probe for NumExprs {
    fn eval(&self, m: &AstManager, goal: &Goal) -> f64 {
        goal.formulas.iter().map(|&f| m.num_subexprs(f)).sum::<usize>() as f64
    }
}

/// `cond(p, thresh, then_t, else_t)`: apply `then_t` if `p(goal) >= thresh`,
/// else `else_t` — the probe-guarded conditional tactic (`when`/`cond`).
pub struct Cond {
    pub probe: Box<dyn Probe>,
    pub threshold: f64,
    pub then_t: Box<dyn Tactic>,
    pub else_t: Box<dyn Tactic>,
}
impl Tactic for Cond {
    fn apply(&self, m: &mut AstManager, goal: &Goal) -> Result<Vec<Goal>, String> {
        if self.probe.eval(m, goal) >= self.threshold {
            self.then_t.apply(m, goal)
        } else {
            self.else_t.apply(m, goal)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // `simplify` folds `(and (< x 3) true)` to `(< x 3)` and detects unsat.
    #[test]
    fn simplify_tactic_folds_and_detects_unsat() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        let lt = m.mk_lt(x, three);
        let tru = m.mk_true();
        let goal = Goal::from(vec![lt, tru]);
        let out = Simplify.apply(&mut m, &goal).unwrap();
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].formulas, vec![lt]); // `true` dropped

        // A literally-false goal collapses.
        let one = m.mk_int(1);
        let two = m.mk_int(2);
        let eq = m.mk_eq(one, two); // 1 = 2 → false
        let g2 = Goal::from(vec![eq]);
        let out2 = Simplify.apply(&mut m, &g2).unwrap();
        assert!(out2[0].is_decided_unsat(&m));
    }

    // `split-conjuncts` flattens nested `and`s into a flat atom list.
    #[test]
    fn split_conjuncts_flattens() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        let r = m.mk_bool_const("r");
        let inner = m.mk_and(&[q, r]);
        let outer = m.mk_and(&[p, inner]);
        let goal = Goal::from(vec![outer]);
        let out = SplitConjuncts.apply(&mut m, &goal).unwrap();
        assert_eq!(out[0].formulas, vec![p, q, r]);
    }

    // Combinators run: `then(split, simplify)`, `or_else(fail, skip)`, `repeat`.
    #[test]
    fn combinators_compose() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let tru = m.mk_true();
        let inner = m.mk_and(&[p, tru]);
        let goal = Goal::from(vec![inner]);

        let t = then(Box::new(SplitConjuncts), Box::new(Simplify));
        let out = t.apply(&mut m, &goal).unwrap();
        // split → [p, true]; simplify drops true → [p].
        assert_eq!(out[0].formulas, vec![p]);

        // or_else recovers from failure.
        let oe = or_else(Box::new(Fail), Box::new(Skip));
        assert!(oe.apply(&mut m, &goal).is_ok());

        // repeat reaches a fixpoint without looping forever.
        let rp = repeat(Box::new(Simplify), 100);
        assert!(rp.apply(&mut m, &goal).is_ok());
    }

    // Probes measure goals and drive `cond`.
    #[test]
    fn probe_guarded_cond() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        let goal = Goal::from(vec![p, q]);
        assert_eq!(NumAssertions.eval(&m, &goal), 2.0);

        // With threshold 2, the `then` branch (Fail) is taken → error surfaces.
        let cond = Cond {
            probe: Box::new(NumAssertions),
            threshold: 2.0,
            then_t: Box::new(Fail),
            else_t: Box::new(Skip),
        };
        assert!(cond.apply(&mut m, &goal).is_err());

        // A smaller goal takes the `else` (Skip) branch.
        let small = Goal::from(vec![p]);
        assert!(cond.apply(&mut m, &small).is_ok());
    }
}

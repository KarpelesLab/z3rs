//! A propositional SAT solver core.
//!
//! This is a correct, self-contained DPLL with unit propagation — the seed of
//! the CDCL engine in `z3/src/sat/sat_solver.{h,cpp}` (Z3 4.17.0, MIT). Watched
//! literals, conflict-driven clause learning, restarts, and in-processing land
//! on top of this in later steps; the public API is chosen to survive that
//! evolution.

use alloc::vec::Vec;

use crate::sat::literal::{Lit, Var};
use crate::util::lbool::LBool;

/// The result of a satisfiability check.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SatResult {
    /// Satisfiable — a model is available via [`Solver::value`].
    Sat,
    /// Unsatisfiable.
    Unsat,
}

/// A DPLL SAT solver.
#[derive(Default)]
pub struct Solver {
    /// Per-variable truth assignment (`Undef` = unassigned).
    assign: Vec<LBool>,
    /// The clause database (each clause a disjunction of literals).
    clauses: Vec<Vec<Lit>>,
    /// Assignment trail, for chronological backtracking.
    trail: Vec<Lit>,
    /// Set once a clause forces unsatisfiability at the top level.
    unsat: bool,
}

impl Solver {
    /// A new, empty solver.
    pub fn new() -> Solver {
        Solver::default()
    }

    /// The number of variables.
    #[inline]
    pub fn num_vars(&self) -> usize {
        self.assign.len()
    }

    /// Allocate a fresh variable.
    pub fn mk_var(&mut self) -> Var {
        let v = self.assign.len() as Var;
        self.assign.push(LBool::Undef);
        v
    }

    /// Ensure variables `0..=max` exist.
    fn ensure_var(&mut self, v: Var) {
        while (self.assign.len() as Var) <= v {
            self.assign.push(LBool::Undef);
        }
    }

    /// Add a clause (a disjunction of literals). An empty clause makes the
    /// problem unsatisfiable.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        for &l in lits {
            self.ensure_var(l.var());
        }
        if lits.is_empty() {
            self.unsat = true;
        }
        self.clauses.push(lits.to_vec());
    }

    /// The value of a literal under the current assignment.
    #[inline]
    fn lit_value(&self, l: Lit) -> LBool {
        match self.assign[l.var() as usize] {
            LBool::Undef => LBool::Undef,
            LBool::True => LBool::from_bool(!l.sign()),
            LBool::False => LBool::from_bool(l.sign()),
        }
    }

    /// Assign `l` to true and record it on the trail.
    #[inline]
    fn assign_lit(&mut self, l: Lit) {
        self.assign[l.var() as usize] = LBool::from_bool(!l.sign());
        self.trail.push(l);
    }

    /// Undo assignments back to trail length `mark`.
    fn backtrack(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let l = self.trail.pop().unwrap();
            self.assign[l.var() as usize] = LBool::Undef;
        }
    }

    /// Boolean-constraint propagation: repeatedly assign forced (unit) literals.
    /// Returns `false` if a clause becomes empty (conflict).
    fn propagate(&mut self) -> bool {
        loop {
            let mut unit: Option<Lit> = None;
            for ci in 0..self.clauses.len() {
                let mut num_undef = 0;
                let mut last_undef = None;
                let mut satisfied = false;
                for k in 0..self.clauses[ci].len() {
                    let lit = self.clauses[ci][k];
                    match self.lit_value(lit) {
                        LBool::True => {
                            satisfied = true;
                            break;
                        }
                        LBool::Undef => {
                            num_undef += 1;
                            last_undef = Some(lit);
                        }
                        LBool::False => {}
                    }
                }
                if satisfied {
                    continue;
                }
                if num_undef == 0 {
                    return false; // conflict: all literals false
                }
                if num_undef == 1 {
                    unit = last_undef;
                    break;
                }
            }
            match unit {
                Some(l) => self.assign_lit(l),
                None => return true, // fixpoint, no conflict
            }
        }
    }

    /// The first unassigned variable, if any.
    fn pick_unassigned(&self) -> Option<Var> {
        self.assign
            .iter()
            .position(|&v| v == LBool::Undef)
            .map(|i| i as Var)
    }

    /// Solve. On [`SatResult::Sat`], the assignment is a model.
    pub fn solve(&mut self) -> SatResult {
        if self.unsat {
            return SatResult::Unsat;
        }
        if self.dpll() {
            SatResult::Sat
        } else {
            SatResult::Unsat
        }
    }

    /// Recursive DPLL: propagate, then branch on an unassigned variable.
    fn dpll(&mut self) -> bool {
        let mark = self.trail.len();
        if !self.propagate() {
            self.backtrack(mark);
            return false;
        }
        match self.pick_unassigned() {
            // Every variable is assigned and no clause conflicts → model found.
            None => true,
            Some(v) => {
                for sign in [false, true] {
                    let branch_mark = self.trail.len();
                    self.assign_lit(Lit::new(v, sign));
                    if self.dpll() {
                        return true;
                    }
                    self.backtrack(branch_mark);
                }
                self.backtrack(mark);
                false
            }
        }
    }

    /// The value assigned to `v` (meaningful after [`SatResult::Sat`]).
    #[inline]
    pub fn value(&self, v: Var) -> LBool {
        self.assign[v as usize]
    }

    /// Whether literal `l` is true in the current model.
    #[inline]
    pub fn model_holds(&self, l: Lit) -> bool {
        self.lit_value(l) == LBool::True
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lits(v: &[i32]) -> Vec<Lit> {
        v.iter()
            .map(|&x| Lit::new(x.unsigned_abs() - 1, x < 0))
            .collect()
    }

    #[test]
    fn empty_problem_is_sat() {
        let mut s = Solver::new();
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn empty_clause_is_unsat() {
        let mut s = Solver::new();
        s.add_clause(&[]);
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn unit_propagation_chain() {
        // p ; (¬p ∨ q) ; (¬q ∨ r) forces p, q, r all true.
        let mut s = Solver::new();
        s.add_clause(&lits(&[1]));
        s.add_clause(&lits(&[-1, 2]));
        s.add_clause(&lits(&[-2, 3]));
        assert_eq!(s.solve(), SatResult::Sat);
        assert_eq!(s.value(0), LBool::True);
        assert_eq!(s.value(1), LBool::True);
        assert_eq!(s.value(2), LBool::True);
    }

    #[test]
    fn contradiction_is_unsat() {
        // (p ∨ q) ∧ ¬p ∧ ¬q
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 2]));
        s.add_clause(&lits(&[-1]));
        s.add_clause(&lits(&[-2]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn finds_a_satisfying_model() {
        // (p ∨ q) ∧ ¬p  →  q must be true.
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 2]));
        s.add_clause(&lits(&[-1]));
        assert_eq!(s.solve(), SatResult::Sat);
        assert_eq!(s.value(0), LBool::False);
        assert_eq!(s.value(1), LBool::True);
        // Every clause is satisfied by the model.
        assert!(s.model_holds(Lit::pos(1)));
    }

    #[test]
    fn pigeonhole_php_2_1_is_unsat() {
        // 2 pigeons, 1 hole: each pigeon in the hole, but not both.
        // vars: x11 (=1), x21 (=2). Clauses: (x11) (x21) (¬x11 ∨ ¬x21)
        let mut s = Solver::new();
        s.add_clause(&lits(&[1]));
        s.add_clause(&lits(&[2]));
        s.add_clause(&lits(&[-1, -2]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn larger_satisfiable_instance() {
        // A small chain that is satisfiable; check the model really satisfies it.
        let mut s = Solver::new();
        let clauses = [
            lits(&[1, 2, 3]),
            lits(&[-1, 2]),
            lits(&[-2, 3]),
            lits(&[-3, 1]),
            lits(&[1, -2, 3]),
        ];
        for c in &clauses {
            s.add_clause(c);
        }
        assert_eq!(s.solve(), SatResult::Sat);
        for c in &clauses {
            assert!(
                c.iter().any(|&l| s.model_holds(l)),
                "clause {c:?} unsatisfied"
            );
        }
    }
}

//! A lazy SMT solver for the quantifier-free theory of equality and
//! uninterpreted functions (QF_UF).
//!
//! This is the offline (lazy) DPLL(T) loop — the conceptual core of
//! `z3/src/smt/smt_context` (Z3 4.17.0, MIT), in its simplest complete form:
//! the SAT engine ([`Solver`]) decides the Boolean skeleton (via
//! [`encode_tracking`]); the theory solver ([`Egraph`]) checks whether the
//! implied equalities/disequalities are consistent under congruence; on a
//! theory conflict a blocking clause rules out that assignment and the loop
//! re-solves. Online theory propagation and minimized explanations are the
//! performance refinements that come next.
//!
//! Atoms that are not equalities (e.g. arithmetic `(<= x y)`) are treated as
//! free Booleans, so this decides the equality fragment exactly; a formula whose
//! satisfiability truly depends on such atoms is handled only abstractly until
//! their theory lands.

use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::sat::literal::Lit;
use crate::sat::solver::{SatResult, Solver};
use crate::sat::tseitin::encode_tracking;
use crate::smt::euf::Egraph;

/// The result of an SMT check.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SmtResult {
    /// Satisfiable.
    Sat,
    /// Unsatisfiable.
    Unsat,
}

/// Decide satisfiability of the quantifier-free formula `formula` in QF_UF.
pub fn check(m: &AstManager, formula: AstId) -> SmtResult {
    let mut sat = Solver::new();
    let (top, atoms) = encode_tracking(m, formula, &mut sat);
    sat.add_clause(&[top]);

    // Equality atoms `(= a b)` (over non-Boolean sorts) are the theory atoms.
    let mut eq_atoms: Vec<(Lit, AstId, AstId)> = Vec::new();
    let mut roots: Vec<AstId> = Vec::new();
    for (&atom, &lit) in &atoms {
        if m.is_eq(atom) {
            let args = m.app_args(atom);
            let (a, b) = (args[0], args[1]);
            eq_atoms.push((lit, a, b));
            roots.push(a);
            roots.push(b);
        }
    }

    loop {
        match sat.solve() {
            SatResult::Unsat => return SmtResult::Unsat,
            SatResult::Sat => {
                if eq_atoms.is_empty() {
                    return SmtResult::Sat; // no theory content
                }
                let mut eqs = Vec::new();
                let mut diseqs = Vec::new();
                for &(lit, a, b) in &eq_atoms {
                    if sat.model_holds(lit) {
                        eqs.push((a, b));
                    } else {
                        diseqs.push((a, b));
                    }
                }
                let mut g = Egraph::new(m, &roots);
                if g.is_consistent(m, &eqs, &diseqs) {
                    return SmtResult::Sat;
                }
                // Theory conflict: block this exact assignment of theory atoms.
                let block: Vec<Lit> = eq_atoms
                    .iter()
                    .map(|&(lit, _, _)| if sat.model_holds(lit) { !lit } else { lit })
                    .collect();
                sat.add_clause(&block);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::symbol::Symbol;

    fn constant(m: &mut AstManager, name: &str, sort: AstId) -> AstId {
        let d = m.mk_func_decl(Symbol::new(name), &[], sort);
        m.mk_const(d)
    }

    #[test]
    fn transitivity_is_unsat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (= a b) (= b c) (not (= a c)))
        let ab = m.mk_eq(a, b);
        let bc = m.mk_eq(b, c);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, bc, nac]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn consistent_equalities_are_sat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (= a b) (not (= a c)))
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, nac]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn congruence_is_unsat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[s], s);
        let fa = m.mk_app(f, &[a]);
        let fb = m.mk_app(f, &[b]);
        // (and (= a b) (not (= (f a) (f b))))
        let ab = m.mk_eq(a, b);
        let fab = m.mk_eq(fa, fb);
        let nfab = m.mk_not(fab);
        let formula = m.mk_and(&[ab, nfab]);
        assert_eq!(check(&m, formula), SmtResult::Unsat);
    }

    #[test]
    fn disjunctive_case_split() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (or (= a b) (= a c)) (not (= a b)) (not (= a c))) — unsat via both
        // branches; exercises the SAT case-split + theory blocking loop.
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let or = m.mk_or(&[ab, ac]);
        let nab = m.mk_not(ab);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[or, nab, nac]);
        assert_eq!(check(&m, f), SmtResult::Unsat);

        // Replace the second disequality's target so a=c becomes possible → sat.
        let g = m.mk_and(&[or, nab]);
        assert_eq!(check(&m, g), SmtResult::Sat);
    }

    #[test]
    fn pure_propositional_still_decided() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let np = m.mk_not(p);
        let f = m.mk_and(&[p, np]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }
}

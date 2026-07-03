//! Tseitin CNF encoding of a Boolean AST formula into the [`Solver`].
//!
//! This is the propositional (Boolean-skeleton) bridge from the AST to the SAT
//! core — a lightweight counterpart of Z3's `goal2sat` (`z3/src/sat`, MIT). Each
//! Boolean connective becomes a fresh variable defined by clauses; non-Boolean
//! atoms (e.g. `(<= x y)`) are abstracted as opaque Boolean variables, so
//! [`check_skeleton`] decides the **propositional abstraction** of a formula:
//! complete for pure propositional logic, sound-but-abstract once theory atoms
//! appear (theory reasoning is the SMT core's job, later).

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::sat::literal::Lit;
use crate::sat::solver::{SatResult, Solver};

/// Encode `root` into `s` and return the literal representing it. Assert that
/// literal to check satisfiability of `root`.
pub fn encode(m: &AstManager, root: AstId, s: &mut Solver) -> Lit {
    let mut enc = Tseitin {
        m,
        s,
        cache: BTreeMap::new(),
        true_lit: None,
    };
    enc.encode(root)
}

/// Decide the propositional abstraction of the Boolean formula `root`.
pub fn check_skeleton(m: &AstManager, root: AstId) -> SatResult {
    let mut s = Solver::new();
    let l = encode(m, root, &mut s);
    s.add_clause(&[l]);
    s.solve()
}

struct Tseitin<'a> {
    m: &'a AstManager,
    s: &'a mut Solver,
    cache: BTreeMap<AstId, Lit>,
    true_lit: Option<Lit>,
}

impl Tseitin<'_> {
    /// A literal that is always true (a fresh unit-clause variable, created once).
    fn true_lit(&mut self) -> Lit {
        if let Some(l) = self.true_lit {
            return l;
        }
        let v = self.s.mk_var();
        let l = Lit::pos(v);
        self.s.add_clause(&[l]);
        self.true_lit = Some(l);
        l
    }

    fn fresh(&mut self) -> Lit {
        Lit::pos(self.s.mk_var())
    }

    fn encode(&mut self, e: AstId) -> Lit {
        // `not` is pure negation — no variable, and don't cache (cheap).
        if self.m.is_not(e) {
            let a = self.m.app_args(e)[0];
            return !self.encode(a);
        }
        if let Some(&l) = self.cache.get(&e) {
            return l;
        }
        let l = self.encode_node(e);
        self.cache.insert(e, l);
        l
    }

    fn encode_node(&mut self, e: AstId) -> Lit {
        if self.m.is_true(e) {
            self.true_lit()
        } else if self.m.is_false(e) {
            let t = self.true_lit();
            !t
        } else if self.m.is_and(e) {
            let lits = self.encode_args(e);
            self.define_and(&lits)
        } else if self.m.is_or(e) {
            let lits = self.encode_args(e);
            self.define_or(&lits)
        } else if is_implies(self.m, e) {
            let args = self.m.app_args(e).to_vec();
            let la = self.encode(args[0]);
            let lb = self.encode(args[1]);
            // a => b  ==  or(¬a, b)
            self.define_or(&[!la, lb])
        } else if is_xor(self.m, e) {
            let args = self.m.app_args(e).to_vec();
            let la = self.encode(args[0]);
            let lb = self.encode(args[1]);
            self.define_xor(la, lb)
        } else if self.m.is_eq(e) && self.eq_is_boolean(e) {
            let args = self.m.app_args(e).to_vec();
            let la = self.encode(args[0]);
            let lb = self.encode(args[1]);
            self.define_iff(la, lb)
        } else if self.m.is_ite(e) && self.m.is_bool(e) {
            let args = self.m.app_args(e).to_vec();
            let lc = self.encode(args[0]);
            let lt = self.encode(args[1]);
            let le = self.encode(args[2]);
            self.define_ite(lc, lt, le)
        } else {
            // Opaque Boolean atom (a propositional variable / theory atom).
            self.fresh()
        }
    }

    fn encode_args(&mut self, e: AstId) -> Vec<Lit> {
        let args = self.m.app_args(e).to_vec();
        args.into_iter().map(|a| self.encode(a)).collect()
    }

    fn eq_is_boolean(&self, e: AstId) -> bool {
        self.m
            .app_args(e)
            .first()
            .is_some_and(|&a| self.m.is_bool(a))
    }

    // --- connective definitions (y ↔ op(...)) ------------------------------

    fn define_and(&mut self, lits: &[Lit]) -> Lit {
        let y = self.fresh();
        // y → each li
        for &li in lits {
            self.s.add_clause(&[!y, li]);
        }
        // (⋀ li) → y  ==  (y ∨ ⋁ ¬li)
        let mut big = Vec::with_capacity(lits.len() + 1);
        big.push(y);
        big.extend(lits.iter().map(|&li| !li));
        self.s.add_clause(&big);
        y
    }

    fn define_or(&mut self, lits: &[Lit]) -> Lit {
        let y = self.fresh();
        // each li → y
        for &li in lits {
            self.s.add_clause(&[!li, y]);
        }
        // y → ⋁ li
        let mut big = Vec::with_capacity(lits.len() + 1);
        big.push(!y);
        big.extend_from_slice(lits);
        self.s.add_clause(&big);
        y
    }

    fn define_xor(&mut self, a: Lit, b: Lit) -> Lit {
        let y = self.fresh();
        self.s.add_clause(&[!y, a, b]);
        self.s.add_clause(&[!y, !a, !b]);
        self.s.add_clause(&[y, !a, b]);
        self.s.add_clause(&[y, a, !b]);
        y
    }

    fn define_iff(&mut self, a: Lit, b: Lit) -> Lit {
        let y = self.fresh();
        self.s.add_clause(&[!y, !a, b]);
        self.s.add_clause(&[!y, a, !b]);
        self.s.add_clause(&[y, a, b]);
        self.s.add_clause(&[y, !a, !b]);
        y
    }

    fn define_ite(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        let y = self.fresh();
        self.s.add_clause(&[!y, !c, t]);
        self.s.add_clause(&[!y, c, e]);
        self.s.add_clause(&[y, !c, !t]);
        self.s.add_clause(&[y, c, !e]);
        y
    }
}

fn is_implies(m: &AstManager, e: AstId) -> bool {
    use crate::ast::{BASIC_FAMILY_ID, BasicOp, DeclKind};
    m.is_app_of(e, BASIC_FAMILY_ID, BasicOp::Implies as DeclKind)
}

fn is_xor(m: &AstManager, e: AstId) -> bool {
    use crate::ast::{BASIC_FAMILY_ID, BasicOp, DeclKind};
    m.is_app_of(e, BASIC_FAMILY_ID, BasicOp::Xor as DeclKind)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contradiction_is_unsat() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let np = m.mk_not(p);
        // (and p (not p))
        let f = m.mk_and(&[p, np]);
        assert_eq!(check_skeleton(&m, f), SatResult::Unsat);
    }

    #[test]
    fn satisfiable_disjunction() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        let f = m.mk_or(&[p, q]);
        assert_eq!(check_skeleton(&m, f), SatResult::Sat);
    }

    #[test]
    fn resolution_refutation() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        // (and (or p q) (not p) (not q)) is unsat
        let or = m.mk_or(&[p, q]);
        let np = m.mk_not(p);
        let nq = m.mk_not(q);
        let f = m.mk_and(&[or, np, nq]);
        assert_eq!(check_skeleton(&m, f), SatResult::Unsat);
    }

    #[test]
    fn excluded_middle_is_a_tautology() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let np = m.mk_not(p);
        // ¬(p ∨ ¬p) is unsat (so p ∨ ¬p is valid)
        let lem = m.mk_or(&[p, np]);
        let neg = m.mk_not(lem);
        assert_eq!(check_skeleton(&m, neg), SatResult::Unsat);
    }

    #[test]
    fn iff_and_implies() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        // (and (= p q) p (not q)) is unsat
        let iff = m.mk_eq(p, q);
        let nq = m.mk_not(q);
        let f = m.mk_and(&[iff, p, nq]);
        assert_eq!(check_skeleton(&m, f), SatResult::Unsat);

        // modus ponens: (and (=> p q) p (not q)) is unsat
        let imp = m.mk_implies(p, q);
        let g = m.mk_and(&[imp, p, nq]);
        assert_eq!(check_skeleton(&m, g), SatResult::Unsat);
    }

    #[test]
    fn theory_atoms_are_abstracted() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        // (and (<= x y) (not (<= x y))) — abstracted as (and a (not a)) => unsat
        let le = m.mk_le(x, y);
        let nle = m.mk_not(le);
        let f = m.mk_and(&[le, nle]);
        assert_eq!(check_skeleton(&m, f), SatResult::Unsat);
        // (and (<= x y) (<= y x)) — two distinct atoms => sat (abstraction).
        let le2 = m.mk_le(y, x);
        let g = m.mk_and(&[le, le2]);
        assert_eq!(check_skeleton(&m, g), SatResult::Sat);
    }
}

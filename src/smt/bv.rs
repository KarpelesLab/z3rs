//! A bit-blasting decision procedure for quantifier-free bit-vectors (QF_BV).
//!
//! Every bit-vector term is expanded into a vector of Boolean literals (LSB
//! first) and every bit-vector / Boolean operation into the corresponding
//! Boolean circuit; the CDCL SAT core ([`Solver`]) then decides the result. This
//! is the eager approach of `z3/src/ast/rewriter/bit_blaster` feeding
//! `z3/src/sat` (Z3 4.17.0, MIT).
//!
//! Supported so far: bit-vector constants and numerals; `bvnot`, `bvand`,
//! `bvor`, `bvxor`; `bvneg`, `bvadd`, `bvsub`; `bvult`/`bvule`; equality; and the
//! Boolean connectives over them. Wider coverage (mul/div, shifts, concat,
//! extract, signed comparisons) builds on the same gates.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::bv::BvOp;
use crate::ast::manager::AstManager;
use crate::sat::literal::Lit;
use crate::sat::solver::{SatResult, Solver};
use crate::smt::solver::SmtResult;

/// Decide a quantifier-free bit-vector formula by bit-blasting to SAT.
pub fn check_bv(m: &AstManager, formula: AstId) -> SmtResult {
    let mut bb = BitBlaster::new(m);
    let top = bb.blast_bool(formula);
    bb.sat.add_clause(&[top]);
    match bb.sat.solve() {
        SatResult::Sat => SmtResult::Sat,
        SatResult::Unsat => SmtResult::Unsat,
    }
}

struct BitBlaster<'a> {
    m: &'a AstManager,
    sat: Solver,
    /// Bit-vector term → its bit literals, least-significant first.
    bits: BTreeMap<AstId, Vec<Lit>>,
    /// Boolean term → its literal.
    bools: BTreeMap<AstId, Lit>,
    /// A literal fixed to true (its negation is false).
    true_lit: Lit,
}

impl<'a> BitBlaster<'a> {
    fn new(m: &'a AstManager) -> BitBlaster<'a> {
        let mut sat = Solver::new();
        let t = Lit::pos(sat.mk_var());
        sat.add_clause(&[t]); // force it true
        BitBlaster {
            m,
            sat,
            bits: BTreeMap::new(),
            bools: BTreeMap::new(),
            true_lit: t,
        }
    }

    fn fresh(&mut self) -> Lit {
        Lit::pos(self.sat.mk_var())
    }

    // --- gates: define a fresh literal equal to a function of its inputs ------

    fn and2(&mut self, a: Lit, b: Lit) -> Lit {
        let c = self.fresh();
        self.sat.add_clause(&[!c, a]);
        self.sat.add_clause(&[!c, b]);
        self.sat.add_clause(&[c, !a, !b]);
        c
    }

    fn or2(&mut self, a: Lit, b: Lit) -> Lit {
        let c = self.fresh();
        self.sat.add_clause(&[c, !a]);
        self.sat.add_clause(&[c, !b]);
        self.sat.add_clause(&[!c, a, b]);
        c
    }

    fn xor2(&mut self, a: Lit, b: Lit) -> Lit {
        let c = self.fresh();
        self.sat.add_clause(&[!c, a, b]);
        self.sat.add_clause(&[!c, !a, !b]);
        self.sat.add_clause(&[c, !a, b]);
        self.sat.add_clause(&[c, a, !b]);
        c
    }

    fn and_all(&mut self, lits: &[Lit]) -> Lit {
        match lits.split_first() {
            None => self.true_lit,
            Some((&first, rest)) => rest.iter().fold(first, |acc, &l| self.and2(acc, l)),
        }
    }

    fn or_all(&mut self, lits: &[Lit]) -> Lit {
        match lits.split_first() {
            None => !self.true_lit,
            Some((&first, rest)) => rest.iter().fold(first, |acc, &l| self.or2(acc, l)),
        }
    }

    /// A full adder: returns `(sum, carry_out)` for `a + b + cin`.
    fn full_adder(&mut self, a: Lit, b: Lit, cin: Lit) -> (Lit, Lit) {
        let axb = self.xor2(a, b);
        let sum = self.xor2(axb, cin);
        // carry = majority(a, b, cin) = (a∧b) ∨ (cin ∧ (a⊕b))
        let ab = self.and2(a, b);
        let cinaxb = self.and2(cin, axb);
        let carry = self.or2(ab, cinaxb);
        (sum, carry)
    }

    /// `a + b` (mod 2^n) via ripple-carry, `cin` the initial carry.
    fn ripple_add(&mut self, a: &[Lit], b: &[Lit], cin: Lit) -> Vec<Lit> {
        let mut carry = cin;
        let mut out = Vec::with_capacity(a.len());
        for i in 0..a.len() {
            let (s, c) = self.full_adder(a[i], b[i], carry);
            out.push(s);
            carry = c;
        }
        out
    }

    // --- blasting -------------------------------------------------------------

    /// The bit literals (LSB first) of a bit-vector term.
    fn blast_bv(&mut self, t: AstId) -> Vec<Lit> {
        if let Some(v) = self.bits.get(&t) {
            return v.clone();
        }
        let width = self
            .m
            .bv_sort_width(self.m.get_sort(t))
            .expect("blast_bv: not a bit-vector") as usize;

        let result = if let Some(val) = self.m.bv_numeral_value(t) {
            (0..width)
                .map(|i| if val.bit(i as u32) { self.true_lit } else { !self.true_lit })
                .collect()
        } else if let Some(op) = self.m.bv_op(t) {
            let args: Vec<AstId> = self.m.app_args(t).to_vec();
            match op {
                BvOp::BNot => {
                    let a = self.blast_bv(args[0]);
                    a.iter().map(|&l| !l).collect()
                }
                BvOp::BAnd => self.zip_gate(args[0], args[1], BitBlaster::and2),
                BvOp::BOr => self.zip_gate(args[0], args[1], BitBlaster::or2),
                BvOp::BXor => self.zip_gate(args[0], args[1], BitBlaster::xor2),
                BvOp::Add => {
                    let a = self.blast_bv(args[0]);
                    let b = self.blast_bv(args[1]);
                    let cin = !self.true_lit; // false
                    self.ripple_add(&a, &b, cin)
                }
                BvOp::Sub => {
                    // a - b = a + (~b) + 1
                    let a = self.blast_bv(args[0]);
                    let b = self.blast_bv(args[1]);
                    let nb: Vec<Lit> = b.iter().map(|&l| !l).collect();
                    self.ripple_add(&a, &nb, self.true_lit)
                }
                BvOp::Neg => {
                    // -a = ~a + 1
                    let a = self.blast_bv(args[0]);
                    let na: Vec<Lit> = a.iter().map(|&l| !l).collect();
                    let zero = alloc::vec![!self.true_lit; width];
                    self.ripple_add(&na, &zero, self.true_lit)
                }
                BvOp::Concat => {
                    // a (high) ++ b (low): low bits are b, high bits are a.
                    let a = self.blast_bv(args[0]);
                    let b = self.blast_bv(args[1]);
                    let mut bits = b;
                    bits.extend(a);
                    bits
                }
                BvOp::Extract => {
                    let (high, low) = self
                        .m
                        .bv_extract_params(t)
                        .expect("extract without indices");
                    let a = self.blast_bv(args[0]);
                    a[low as usize..=high as usize].to_vec()
                }
                // Unsupported bv operators become fresh (unconstrained) bits.
                _ => (0..width).map(|_| self.fresh()).collect(),
            }
        } else {
            // An uninterpreted bit-vector constant: one fresh variable per bit.
            (0..width).map(|_| self.fresh()).collect()
        };
        self.bits.insert(t, result.clone());
        result
    }

    /// Blast `a op b` bitwise, where `op` is a 2-input gate.
    fn zip_gate(
        &mut self,
        a: AstId,
        b: AstId,
        gate: fn(&mut BitBlaster<'a>, Lit, Lit) -> Lit,
    ) -> Vec<Lit> {
        let a = self.blast_bv(a);
        let b = self.blast_bv(b);
        a.iter()
            .zip(&b)
            .map(|(&x, &y)| gate(self, x, y))
            .collect()
    }

    /// The literal for a Boolean term.
    fn blast_bool(&mut self, t: AstId) -> Lit {
        if let Some(&l) = self.bools.get(&t) {
            return l;
        }
        let result = if self.m.is_true(t) {
            self.true_lit
        } else if self.m.is_false(t) {
            !self.true_lit
        } else if self.m.is_not(t) {
            let a = self.blast_bool(self.m.app_args(t)[0]);
            !a
        } else if self.m.is_and(t) {
            let ls: Vec<Lit> = self.m.app_args(t).to_vec().iter().map(|&a| self.blast_bool(a)).collect();
            self.and_all(&ls)
        } else if self.m.is_or(t) {
            let ls: Vec<Lit> = self.m.app_args(t).to_vec().iter().map(|&a| self.blast_bool(a)).collect();
            self.or_all(&ls)
        } else if self.m.is_eq(t) {
            let args = self.m.app_args(t).to_vec();
            if self.m.bv_sort_width(self.m.get_sort(args[0])).is_some() {
                self.bv_eq(args[0], args[1])
            } else {
                // Boolean equality (iff).
                let a = self.blast_bool(args[0]);
                let b = self.blast_bool(args[1]);
                let x = self.xor2(a, b);
                !x
            }
        } else if let Some(op) = self.m.bv_op(t) {
            let args = self.m.app_args(t).to_vec();
            match op {
                BvOp::Ult => self.bv_ult(args[0], args[1]),
                BvOp::Uleq => {
                    let lt = self.bv_ult(args[0], args[1]);
                    let eq = self.bv_eq(args[0], args[1]);
                    self.or2(lt, eq)
                }
                _ => self.fresh(),
            }
        } else {
            // An opaque Boolean atom (e.g. a Boolean constant): a fresh variable.
            self.fresh()
        };
        self.bools.insert(t, result);
        result
    }

    /// `a = b` over bit-vectors: all bits equal.
    fn bv_eq(&mut self, a: AstId, b: AstId) -> Lit {
        let a = self.blast_bv(a);
        let b = self.blast_bv(b);
        let eqs: Vec<Lit> = a
            .iter()
            .zip(&b)
            .map(|(&x, &y)| {
                let d = self.xor2(x, y);
                !d
            })
            .collect();
        self.and_all(&eqs)
    }

    /// `a <u b` (unsigned): subtract and read the borrow, i.e. `a - b` overflows.
    /// Implemented as the carry-out of `a + ~b + 1` being 0.
    fn bv_ult(&mut self, a: AstId, b: AstId) -> Lit {
        let a = self.blast_bv(a);
        let b = self.blast_bv(b);
        // Compute a + ~b + 1 and take the final carry; carry == 0 ⟺ a < b.
        let mut carry = self.true_lit;
        for i in 0..a.len() {
            let nb = !b[i];
            let (_, c) = self.full_adder(a[i], nb, carry);
            carry = c;
        }
        !carry
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bvc(m: &mut AstManager, name: &str, w: u32) -> AstId {
        m.mk_bv_const(name, w)
    }

    #[test]
    fn equality_of_distinct_numerals_unsat() {
        let mut m = AstManager::new();
        let a = m.mk_bv(3, 8);
        let b = m.mk_bv(5, 8);
        let eq = m.mk_eq(a, b);
        assert_eq!(check_bv(&m, eq), SmtResult::Unsat);
        let same = m.mk_eq(a, a);
        assert_eq!(check_bv(&m, same), SmtResult::Sat);
    }

    #[test]
    fn add_overflow_wraps() {
        // x = 255, x + 1 = 0 (8-bit wrap): assert (x+1 != 0) with x=255 → unsat.
        let mut m = AstManager::new();
        let x = bvc(&mut m, "x", 8);
        let c255 = m.mk_bv(255, 8);
        let one = m.mk_bv(1, 8);
        let zero = m.mk_bv(0, 8);
        let sum = m.mk_bvadd(x, one);
        let eq255 = m.mk_eq(x, c255);
        let e0 = m.mk_eq(sum, zero); let ne0 = m.mk_not(e0);
        let f = m.mk_and(&[eq255, ne0]);
        assert_eq!(check_bv(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn bitwise_and_identity() {
        // x & 0 = 0 always: assert (x & 0 != 0) → unsat.
        let mut m = AstManager::new();
        let x = bvc(&mut m, "x", 4);
        let zero = m.mk_bv(0, 4);
        let and = m.mk_bvand(x, zero);
        let e = m.mk_eq(and, zero); let ne = m.mk_not(e);
        assert_eq!(check_bv(&m, ne), SmtResult::Unsat);
    }

    #[test]
    fn ult_is_strict() {
        // x <u x is never true.
        let mut m = AstManager::new();
        let x = bvc(&mut m, "x", 8);
        let lt = m.mk_bvult(x, x);
        assert_eq!(check_bv(&m, lt), SmtResult::Unsat);
        // 3 <u 5 holds.
        let a = m.mk_bv(3, 8);
        let b = m.mk_bv(5, 8);
        let lt2 = m.mk_bvult(a, b);
        assert_eq!(check_bv(&m, lt2), SmtResult::Sat);
        let lt3 = m.mk_bvult(b, a);
        assert_eq!(check_bv(&m, lt3), SmtResult::Unsat);
    }

    #[test]
    fn sub_is_add_inverse() {
        // (x - x) = 0 always.
        let mut m = AstManager::new();
        let x = bvc(&mut m, "x", 8);
        let zero = m.mk_bv(0, 8);
        let sub = m.mk_bvsub(x, x);
        let e = m.mk_eq(sub, zero); let ne = m.mk_not(e);
        assert_eq!(check_bv(&m, ne), SmtResult::Unsat);
    }
}

//! A bounded simplex over the rationals — the feasibility core of Z3's
//! `theory_lra` / `z3/src/math/simplex` (Z3 4.17.0, MIT), after Dutertre & de
//! Moura, *A Fast Linear-Arithmetic Solver for DPLL(T)* (CAV 2006).
//!
//! Every variable carries optional lower/upper bounds; each row defines a basic
//! variable as a linear combination of non-basic ones (`add_row` introduces a
//! slack for a linear form). [`Simplex::check`] restores bound consistency by
//! pivoting under **Bland's rule** (smallest-index leaving and entering
//! variables), which guarantees termination. Strict bounds are handled exactly
//! with an infinitesimal: values and bounds are [`DeltaRat`] `r + k·δ`, and a
//! concrete `δ > 0` small enough for every bound is chosen only when the model is
//! read back.
//!
//! An infeasible row yields its **explanation**: the violated bound of the basic
//! variable plus the blocking bound of every non-basic variable in the row. The
//! row is a Farkas combination of exactly those bounds, so their `tag`s (the
//! caller's constraint indices) form a sound conflict core.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::cmp::Ordering;

use puremp::{Int, Rational};

fn zero() -> Rational {
    Rational::from_integer(Int::from(0))
}

/// `r + k·δ` for a positive infinitesimal `δ` — Z3's `inf_numeral`. Ordered
/// lexicographically, which is the order for every sufficiently small `δ > 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeltaRat {
    pub r: Rational,
    pub k: Rational,
}

impl DeltaRat {
    /// The plain rational `r`.
    pub fn new(r: Rational) -> DeltaRat {
        DeltaRat { r, k: zero() }
    }
    /// `r − δ` (the bound of a strict `< r`).
    pub fn below(r: Rational) -> DeltaRat {
        DeltaRat {
            r,
            k: Rational::from_integer(Int::from(-1)),
        }
    }
    /// `r + δ` (the bound of a strict `> r`).
    pub fn above(r: Rational) -> DeltaRat {
        DeltaRat {
            r,
            k: Rational::from_integer(Int::from(1)),
        }
    }
    fn zero() -> DeltaRat {
        DeltaRat::new(zero())
    }
    fn add(&self, o: &DeltaRat) -> DeltaRat {
        DeltaRat {
            r: self.r.add(&o.r),
            k: self.k.add(&o.k),
        }
    }
    fn sub(&self, o: &DeltaRat) -> DeltaRat {
        DeltaRat {
            r: self.r.sub(&o.r),
            k: self.k.sub(&o.k),
        }
    }
    fn scale(&self, c: &Rational) -> DeltaRat {
        DeltaRat {
            r: self.r.mul(c),
            k: self.k.mul(c),
        }
    }
    fn add_scaled(&mut self, o: &DeltaRat, c: &Rational) {
        self.r.addmul(&o.r, c);
        self.k.addmul(&o.k, c);
    }
    /// The concrete value at `δ = delta`.
    fn at(&self, delta: &Rational) -> Rational {
        self.r.add(&self.k.mul(delta))
    }
}

impl PartialOrd for DeltaRat {
    fn partial_cmp(&self, o: &DeltaRat) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for DeltaRat {
    fn cmp(&self, o: &DeltaRat) -> Ordering {
        self.r.cmp(&o.r).then_with(|| self.k.cmp(&o.k))
    }
}

/// A bound and the caller tag (constraint index) that asserted it.
#[derive(Clone, Debug)]
struct Bound {
    val: DeltaRat,
    tag: usize,
}

/// `basic = Σ coeffs[j]·x_j` over non-basic `x_j`.
#[derive(Clone, Debug)]
struct Row {
    basic: usize,
    coeffs: BTreeMap<usize, Rational>,
}

/// The outcome of [`Simplex::check`].
#[derive(Debug)]
pub enum Check {
    /// All bounds hold at the current assignment.
    Sat,
    /// Infeasible; the tags of a conflicting set of bounds (sorted, deduplicated).
    Unsat(Vec<usize>),
    /// The pivot budget ran out before deciding.
    Exhausted,
}

/// A bounded simplex tableau.
#[derive(Clone, Debug, Default)]
pub struct Simplex {
    lower: Vec<Option<Bound>>,
    upper: Vec<Option<Bound>>,
    value: Vec<DeltaRat>,
    /// `row_of[v]` = the row whose basic variable is `v`, if `v` is basic.
    row_of: Vec<Option<usize>>,
    rows: Vec<Row>,
    /// `col[v]` = the rows in which non-basic `v` occurs.
    col: Vec<BTreeSet<usize>>,
    /// Undo log of bound changes `(var, is_lower, previous bound)`, and the log
    /// length at each open [`push`](Simplex::push).
    undo: Vec<(usize, bool, Option<Bound>)>,
    scopes: Vec<usize>,
}

impl Simplex {
    /// A tableau over `n` structural variables `0..n`, all non-basic and `0`.
    pub fn new(n: usize) -> Simplex {
        let mut s = Simplex::default();
        for _ in 0..n {
            s.mk_var();
        }
        s
    }

    /// Add a fresh unbounded variable at `0` and return it.
    pub fn mk_var(&mut self) -> usize {
        let v = self.value.len();
        self.lower.push(None);
        self.upper.push(None);
        self.value.push(DeltaRat::zero());
        self.row_of.push(None);
        self.col.push(BTreeSet::new());
        v
    }

    /// The number of variables (structural and slack).
    pub fn num_vars(&self) -> usize {
        self.value.len()
    }

    /// Introduce a slack `s = Σ c·x` and return it. Basic variables among the
    /// `x` are replaced by their rows, so the tableau stays in solved form.
    pub fn add_row(&mut self, form: &[(usize, Rational)]) -> usize {
        let s = self.mk_var();
        let mut coeffs: BTreeMap<usize, Rational> = BTreeMap::new();
        for (x, c) in form {
            match self.row_of[*x] {
                Some(r) => {
                    for (y, a) in &self.rows[r].coeffs {
                        add_coeff(&mut coeffs, *y, &a.mul(c));
                    }
                }
                None => add_coeff(&mut coeffs, *x, c),
            }
        }
        let mut val = DeltaRat::zero();
        for (y, a) in &coeffs {
            val.add_scaled(&self.value[*y], a);
        }
        let r = self.rows.len();
        for y in coeffs.keys() {
            self.col[*y].insert(r);
        }
        self.rows.push(Row { basic: s, coeffs });
        self.row_of[s] = Some(r);
        self.value[s] = val;
        s
    }

    /// Assert `v ≥ val`. A conflict with `v`'s upper bound is returned at once.
    pub fn assert_lower(&mut self, v: usize, val: DeltaRat, tag: usize) -> Result<(), Vec<usize>> {
        if self.lower[v].as_ref().is_some_and(|b| b.val >= val) {
            return Ok(()); // not tighter
        }
        if let Some(u) = &self.upper[v]
            && val > u.val
        {
            return Err(core_of([tag, u.tag]));
        }
        if self.row_of[v].is_none() && self.value[v] < val {
            self.update(v, val.clone());
        }
        let old = self.lower[v].replace(Bound { val, tag });
        if !self.scopes.is_empty() {
            self.undo.push((v, true, old));
        }
        Ok(())
    }

    /// Assert `v ≤ val`. A conflict with `v`'s lower bound is returned at once.
    pub fn assert_upper(&mut self, v: usize, val: DeltaRat, tag: usize) -> Result<(), Vec<usize>> {
        if self.upper[v].as_ref().is_some_and(|b| b.val <= val) {
            return Ok(());
        }
        if let Some(l) = &self.lower[v]
            && val < l.val
        {
            return Err(core_of([tag, l.tag]));
        }
        if self.row_of[v].is_none() && self.value[v] > val {
            self.update(v, val.clone());
        }
        let old = self.upper[v].replace(Bound { val, tag });
        if !self.scopes.is_empty() {
            self.undo.push((v, false, old));
        }
        Ok(())
    }

    /// Open a scope: bounds asserted from here on are retracted by the matching
    /// [`pop`](Simplex::pop).
    pub fn push(&mut self) {
        self.scopes.push(self.undo.len());
    }

    /// Retract every bound asserted since the matching [`push`](Simplex::push).
    /// Rows and values are kept: loosening bounds cannot break a bound that held,
    /// and the next [`check`](Simplex::check) repairs any that still fail.
    pub fn pop(&mut self) {
        let mark = self.scopes.pop().expect("pop without push");
        while self.undo.len() > mark {
            let (v, is_lower, old) = self.undo.pop().unwrap();
            if is_lower {
                self.lower[v] = old;
            } else {
                self.upper[v] = old;
            }
        }
    }

    /// Set non-basic `v` to `val`, shifting every basic variable that uses it.
    fn update(&mut self, v: usize, val: DeltaRat) {
        let delta = val.sub(&self.value[v]);
        for &r in &self.col[v] {
            let row = &self.rows[r];
            let a = &row.coeffs[&v];
            let b = row.basic;
            self.value[b].add_scaled(&delta, a);
        }
        self.value[v] = val;
    }

    fn below_lower(&self, v: usize) -> bool {
        self.lower[v]
            .as_ref()
            .is_some_and(|b| self.value[v] < b.val)
    }
    fn above_upper(&self, v: usize) -> bool {
        self.upper[v]
            .as_ref()
            .is_some_and(|b| self.value[v] > b.val)
    }
    fn can_increase(&self, v: usize) -> bool {
        self.upper[v].as_ref().is_none_or(|b| self.value[v] < b.val)
    }
    fn can_decrease(&self, v: usize) -> bool {
        self.lower[v].as_ref().is_none_or(|b| self.value[v] > b.val)
    }

    /// Restore every bound by pivoting (Bland's rule). Each pivot costs the row
    /// count in `budget`; on exhaustion the tableau is left consistent but
    /// undecided.
    pub fn check(&mut self, budget: &mut u64) -> Check {
        loop {
            // Leaving variable: the smallest-index basic variable out of bounds.
            let Some(xi) = self
                .rows
                .iter()
                .map(|r| r.basic)
                .filter(|&b| self.below_lower(b) || self.above_upper(b))
                .min()
            else {
                return Check::Sat;
            };
            let r = self.row_of[xi].unwrap();
            let increase = self.below_lower(xi);
            // Entering variable: the smallest-index non-basic one that can move
            // `xi` toward its violated bound.
            let entering = self.rows[r]
                .coeffs
                .iter()
                .find(|(x, a)| {
                    let up = a.is_positive() == increase;
                    if up {
                        self.can_increase(**x)
                    } else {
                        self.can_decrease(**x)
                    }
                })
                .map(|(x, _)| *x);
            let Some(xj) = entering else {
                // Every variable in the row is pinned at the bound that blocks
                // `xi`: the row is a Farkas combination of those bounds.
                let mut tags = Vec::new();
                let own = if increase {
                    &self.lower[xi]
                } else {
                    &self.upper[xi]
                };
                tags.push(own.as_ref().unwrap().tag);
                for (x, a) in &self.rows[r].coeffs {
                    let blocking = if a.is_positive() == increase {
                        &self.upper[*x]
                    } else {
                        &self.lower[*x]
                    };
                    tags.push(blocking.as_ref().unwrap().tag);
                }
                return Check::Unsat(core_of(tags));
            };
            // A pivot rewrites up to every row: charge accordingly.
            let cost = self.rows.len().max(1) as u64;
            if *budget < cost {
                *budget = 0;
                return Check::Exhausted;
            }
            *budget -= cost;
            let target = if increase {
                self.lower[xi].as_ref().unwrap().val.clone()
            } else {
                self.upper[xi].as_ref().unwrap().val.clone()
            };
            self.pivot_and_update(xi, xj, target);
        }
    }

    /// Move basic `xi` to `target` by changing non-basic `xj`, then swap them.
    fn pivot_and_update(&mut self, xi: usize, xj: usize, target: DeltaRat) {
        let r = self.row_of[xi].unwrap();
        let a = self.rows[r].coeffs[&xj].clone();
        let theta = target.sub(&self.value[xi]).scale(&a.recip());
        let new_xj = self.value[xj].add(&theta);
        self.update(xj, new_xj); // also sets xi = target
        self.pivot(r, xi, xj);
    }

    /// Make `xj` basic in row `r` (replacing `xi`) and eliminate it elsewhere.
    fn pivot(&mut self, r: usize, xi: usize, xj: usize) {
        // xi = a·xj + rest  ⟹  xj = (1/a)·xi − (1/a)·rest
        let mut coeffs = core::mem::take(&mut self.rows[r].coeffs);
        let a = coeffs.remove(&xj).unwrap();
        let inv = a.recip();
        for c in coeffs.values_mut() {
            *c = c.mul(&inv).neg();
        }
        coeffs.insert(xi, inv);
        for y in coeffs.keys() {
            self.col[*y].insert(r);
        }
        self.col[xj].remove(&r);
        // Substitute xj's new definition into every other row that uses it.
        let users: Vec<usize> = self.col[xj].iter().copied().collect();
        for u in users {
            let c = self.rows[u].coeffs.remove(&xj).unwrap();
            for (y, d) in &coeffs {
                let row = &mut self.rows[u].coeffs;
                let had = row.contains_key(y);
                add_coeff(row, *y, &d.mul(&c));
                match (had, row.contains_key(y)) {
                    (false, true) => {
                        self.col[*y].insert(u);
                    }
                    (true, false) => {
                        self.col[*y].remove(&u);
                    }
                    _ => {}
                }
            }
        }
        self.col[xj].clear();
        self.rows[r] = Row { basic: xj, coeffs };
        self.row_of[xi] = None;
        self.row_of[xj] = Some(r);
    }

    /// Concrete rational values for every variable, with `δ` instantiated small
    /// enough that each bound (strict ones included) holds. Only meaningful after
    /// [`Check::Sat`].
    pub fn model(&self) -> Vec<Rational> {
        // Each bound l ≤ x (as DeltaRats, l ≤ x lexicographically) stays true at
        // δ as long as δ ≤ (x.r − l.r)/(l.k − x.k) whenever l.r < x.r, l.k > x.k.
        let one = Rational::from_integer(Int::from(1));
        let mut delta = one;
        let mut tighten = |lo: &DeltaRat, hi: &DeltaRat| {
            if lo.r < hi.r && lo.k > hi.k {
                let d = hi.r.sub(&lo.r).div(&lo.k.sub(&hi.k));
                if d < delta {
                    delta = d;
                }
            }
        };
        for v in 0..self.num_vars() {
            if let Some(l) = &self.lower[v] {
                tighten(&l.val, &self.value[v]);
            }
            if let Some(u) = &self.upper[v] {
                tighten(&self.value[v], &u.val);
            }
        }
        self.value.iter().map(|x| x.at(&delta)).collect()
    }
}

fn add_coeff(m: &mut BTreeMap<usize, Rational>, k: usize, c: &Rational) {
    if c.is_zero() {
        return;
    }
    let e = m.entry(k).or_insert_with(zero);
    *e = e.add(c);
    if e.is_zero() {
        m.remove(&k);
    }
}

fn core_of(tags: impl IntoIterator<Item = usize>) -> Vec<usize> {
    let set: BTreeSet<usize> = tags.into_iter().collect();
    set.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> Rational {
        Rational::from_integer(Int::from(n))
    }

    #[test]
    fn feasible_triangle_and_model() {
        // x ≥ 0, y ≥ 0, x + y ≤ 4, x − y ≥ 1 (strict-free)
        let mut s = Simplex::new(2);
        let sum = s.add_row(&[(0, q(1)), (1, q(1))]);
        let diff = s.add_row(&[(0, q(1)), (1, q(-1))]);
        s.assert_lower(0, DeltaRat::new(q(0)), 0).unwrap();
        s.assert_lower(1, DeltaRat::new(q(0)), 1).unwrap();
        s.assert_upper(sum, DeltaRat::new(q(4)), 2).unwrap();
        s.assert_lower(diff, DeltaRat::new(q(1)), 3).unwrap();
        assert!(matches!(s.check(&mut 100), Check::Sat));
        let m = s.model();
        assert!(m[0] >= q(0) && m[1] >= q(0));
        assert!(m[0].add(&m[1]) <= q(4));
        assert!(m[0].sub(&m[1]) >= q(1));
    }

    #[test]
    fn strict_bounds_pick_a_small_delta() {
        // 0 < x < 1, x + y = 1, y > 0.5  ⟹  x < 0.5
        let mut s = Simplex::new(2);
        let sum = s.add_row(&[(0, q(1)), (1, q(1))]);
        s.assert_lower(0, DeltaRat::above(q(0)), 0).unwrap();
        s.assert_upper(0, DeltaRat::below(q(1)), 1).unwrap();
        s.assert_lower(sum, DeltaRat::new(q(1)), 2).unwrap();
        s.assert_upper(sum, DeltaRat::new(q(1)), 2).unwrap();
        let half = q(1).div(&q(2));
        s.assert_lower(1, DeltaRat::above(half.clone()), 3).unwrap();
        assert!(matches!(s.check(&mut 100), Check::Sat));
        let m = s.model();
        assert!(m[0] > q(0) && m[0] < half);
        assert_eq!(m[0].add(&m[1]), q(1));
        assert!(m[1] > half);
    }

    #[test]
    fn infeasible_row_gives_its_farkas_core() {
        // x + y ≤ 1 (tag 0), x ≥ 1 (tag 1), y > 0 (tag 2), z ≥ 7 (tag 3, irrelevant)
        let mut s = Simplex::new(3);
        let sum = s.add_row(&[(0, q(1)), (1, q(1))]);
        s.assert_upper(sum, DeltaRat::new(q(1)), 0).unwrap();
        s.assert_lower(0, DeltaRat::new(q(1)), 1).unwrap();
        s.assert_lower(1, DeltaRat::above(q(0)), 2).unwrap();
        s.assert_lower(2, DeltaRat::new(q(7)), 3).unwrap();
        match s.check(&mut 100) {
            Check::Unsat(core) => assert_eq!(core, alloc::vec![0, 1, 2]),
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    #[test]
    fn push_pop_retracts_bounds() {
        // x + y ≤ 1 always; scoped x ≥ 1, y ≥ 1 clash, and are retracted by pop.
        let mut s = Simplex::new(2);
        let sum = s.add_row(&[(0, q(1)), (1, q(1))]);
        s.assert_upper(sum, DeltaRat::new(q(1)), 0).unwrap();
        s.push();
        s.assert_lower(0, DeltaRat::new(q(1)), 1).unwrap();
        s.assert_lower(1, DeltaRat::new(q(1)), 2).unwrap();
        assert!(matches!(s.check(&mut 100), Check::Unsat(_)));
        s.pop();
        s.push();
        s.assert_lower(0, DeltaRat::new(q(1)), 1).unwrap();
        assert!(matches!(s.check(&mut 100), Check::Sat));
        assert_eq!(s.model()[0], q(1));
    }

    #[test]
    fn direct_bound_clash() {
        let mut s = Simplex::new(1);
        s.assert_upper(0, DeltaRat::below(q(3)), 4).unwrap();
        assert_eq!(
            s.assert_lower(0, DeltaRat::new(q(3)), 9),
            Err(alloc::vec![4, 9])
        );
    }
}

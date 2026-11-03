//! z3's `lar_solver` feasibility search, reproduced step for step so that a
//! satisfiable system ends at the *same* vertex z3 prints (`z3/src/math/lp`:
//! `lar_solver.cpp`, `static_matrix_def.h`, `lp_core_solver_base*.h`,
//! `lp_primal_core_solver*.h`, `lar_core_solver.h`; `util/util.h` for the
//! random generator; MIT).
//!
//! [`crate::math::simplex`] decides feasibility soundly but picks its own
//! vertex; this module only exists to pick z3's. It follows the default
//! `tableau_rows` strategy exactly:
//!
//! * columns are created in z3's order; a term column is basic, its row
//!   built by `fill_last_row_with_pivoting` (term coefficients in the
//!   iteration order of the term's `u_map`, see [`umap_order`]);
//! * bounds are recorded and the columns whose bounds changed are fixed up
//!   at the next [`Lar::solve`] in insertion order (a non-basic column moves
//!   onto its violated bound, a basic one enters the infeasibility heap);
//! * each iteration repairs the smallest infeasible basic column, entering
//!   the row column with the fewest non-free dependent basics, then the
//!   shortest column, ties broken by z3's `random_gen` (seed 0); the pivot
//!   keeps z3's cell order (`remove_element` swaps with the last cell);
//! * [`Lar::values`] picks `δ` as `init_model` does: the largest `δ ≤ 1`
//!   keeping every strict bound, halved until distinct values stay distinct.
//!
//! Only real columns are modelled (no integer patching or branching).

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use puremp::{Int, Rational};

fn rat(n: i64) -> Rational {
    Rational::from_integer(Int::from(n))
}

/// `x + y·δ` — z3's `numeric_pair<mpq>` (`impq`), ordered lexicographically.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Impq {
    pub x: Rational,
    pub y: Rational,
}

impl Impq {
    fn new(x: Rational, y: Rational) -> Impq {
        Impq { x, y }
    }
    fn zero() -> Impq {
        Impq::new(rat(0), rat(0))
    }
    fn add(&self, o: &Impq) -> Impq {
        Impq::new(self.x.add(&o.x), self.y.add(&o.y))
    }
    fn sub(&self, o: &Impq) -> Impq {
        Impq::new(self.x.sub(&o.x), self.y.sub(&o.y))
    }
    fn scale(&self, c: &Rational) -> Impq {
        Impq::new(self.x.mul(c), self.y.mul(c))
    }
    fn is_zero(&self) -> bool {
        self.x.is_zero() && self.y.is_zero()
    }
}

/// z3's `random_gen` (`util/util.h`): a 15-bit linear congruential generator.
#[derive(Clone, Debug)]
pub struct Rng(u32);

impl Rng {
    /// A generator seeded with `seed` (z3's `smt.random_seed`, 0 by default).
    pub fn new(seed: u32) -> Rng {
        Rng(seed)
    }
    /// The next 15-bit draw.
    pub fn draw(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(214013).wrapping_add(2531011);
        (self.0 >> 16) & 0x7fff
    }
    /// The next draw modulo `u` (`operator()(unsigned)`).
    pub fn below(&mut self, u: u32) -> u32 {
        self.draw() % u
    }
}

/// The iteration order of z3's `u_map<T>` (a `core_hashtable` keyed by the
/// identity hash, initial capacity 8, linear probing, doubled when the load
/// would exceed 3/4) after inserting the distinct `keys` in order.
pub fn umap_order(keys: &[usize]) -> Vec<usize> {
    let mut cap = 8usize;
    let mut slots: Vec<Option<usize>> = alloc::vec![None; cap];
    let place = |slots: &mut Vec<Option<usize>>, cap: usize, k: usize| {
        let mut i = k & (cap - 1);
        while slots[i].is_some() {
            i = (i + 1) & (cap - 1);
        }
        slots[i] = Some(k);
    };
    for (size, &k) in keys.iter().enumerate() {
        if size * 4 > cap * 3 {
            let old = core::mem::replace(&mut slots, alloc::vec![None; cap * 2]);
            cap *= 2;
            for k in old.into_iter().flatten() {
                place(&mut slots, cap, k);
            }
        }
        place(&mut slots, cap, k);
    }
    slots.into_iter().flatten().collect()
}

/// A bound kind, as z3's `lconstraint_kind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Le,
    Lt,
    Ge,
    Gt,
}

/// A row cell: column, offset of the matching column cell, coefficient.
#[derive(Clone, Debug)]
struct RowCell {
    var: usize,
    off: usize,
    coeff: Rational,
}

/// A column cell: row, offset of the matching row cell.
#[derive(Clone, Copy, Debug)]
struct ColCell {
    row: usize,
    off: usize,
}

/// z3's `lar_solver` over real columns (see the module documentation).
#[derive(Clone, Debug)]
pub struct Lar {
    rng: Rng,
    rows: Vec<Vec<RowCell>>,
    cols: Vec<Vec<ColCell>>,
    x: Vec<Impq>,
    lo: Vec<Option<Impq>>,
    hi: Vec<Option<Impq>>,
    /// Row → its basic column.
    basis: Vec<usize>,
    /// Non-basic positions (`m_nbasis`).
    nbasis: Vec<usize>,
    /// `≥ 0`: the row of a basic column; `< 0`: `-1 -` its non-basic position.
    heading: Vec<isize>,
    /// The infeasible basic columns (z3's `m_inf_heap`, a min-heap by index).
    inf: BTreeSet<usize>,
    /// Columns whose bounds changed since the last solve, in insertion order.
    changed: Vec<usize>,
}

impl Lar {
    /// An empty solver whose tie-breaks draw from `random_gen(seed)`.
    pub fn new(seed: u32) -> Lar {
        Lar {
            rng: Rng::new(seed),
            rows: Vec::new(),
            cols: Vec::new(),
            x: Vec::new(),
            lo: Vec::new(),
            hi: Vec::new(),
            basis: Vec::new(),
            nbasis: Vec::new(),
            heading: Vec::new(),
            inf: BTreeSet::new(),
            changed: Vec::new(),
        }
    }

    fn push_column(&mut self) -> usize {
        let j = self.x.len();
        self.cols.push(Vec::new());
        self.x.push(Impq::zero());
        self.lo.push(None);
        self.hi.push(None);
        j
    }

    /// A new free non-basic column at value 0 (`add_var`).
    pub fn add_var(&mut self) -> usize {
        let j = self.push_column();
        self.heading.push(-(self.nbasis.len() as isize) - 1);
        self.nbasis.push(j);
        j
    }

    /// A new basic column for the term `Σ c·x_j` (`add_term`), given with its
    /// coefficients in the term's `u_map` order (see [`umap_order`]).
    pub fn add_term(&mut self, coeffs: &[(usize, Rational)]) -> usize {
        let j = self.push_column();
        self.rows.push(Vec::new());
        let last = self.rows.len() - 1;
        self.heading.push(last as isize);
        self.basis.push(j);
        // `fill_last_row_with_pivoting`, in the form `-term + j = 0`.
        let mut wv: Vec<Rational> = alloc::vec![rat(0); self.x.len()];
        let mut index: Vec<usize> = Vec::new();
        wv[j] = rat(1);
        index.push(j);
        for (cj, c) in coeffs {
            wv[*cj] = c.neg();
            index.push(*cj);
        }
        let block = |lar: &Lar, bj: usize, wv: &mut Vec<Rational>, index: &mut Vec<usize>| {
            let Ok(ri) = usize::try_from(lar.heading[bj]) else {
                return;
            };
            let alpha = wv[bj].clone();
            if alpha.is_zero() {
                return;
            }
            for rc in &lar.rows[ri] {
                if rc.var == bj {
                    continue;
                }
                let was_zero = wv[rc.var].is_zero();
                wv[rc.var].submul(&alpha, &rc.coeff);
                if was_zero {
                    index.push(rc.var);
                } else if wv[rc.var].is_zero() {
                    index.retain(|&v| v != rc.var);
                }
            }
            wv[bj] = rat(0);
            index.retain(|&v| v != bj);
        };
        block(self, j, &mut wv, &mut index);
        for (cj, _) in coeffs {
            block(self, *cj, &mut wv, &mut index);
        }
        for &v in &index {
            if !wv[v].is_zero() {
                let c = wv[v].clone();
                self.add_new_element(last, v, c);
            }
        }
        self.add_new_element(last, j, rat(1));
        // `get_basic_var_value_from_row`.
        let mut r = Impq::zero();
        for rc in &self.rows[last] {
            if rc.var != j && !self.x[rc.var].is_zero() {
                r = r.sub(&self.x[rc.var].scale(&rc.coeff));
            }
        }
        self.x[j] = r;
        j
    }

    fn add_new_element(&mut self, row: usize, col: usize, coeff: Rational) {
        let roff = self.rows[row].len();
        let coff = self.cols[col].len();
        self.rows[row].push(RowCell {
            var: col,
            off: coff,
            coeff,
        });
        self.cols[col].push(ColCell { row, off: roff });
    }

    /// `static_matrix::remove_element`: drop the cell at `row_off` of row
    /// `row`, moving the last cells of its row and column into the holes.
    fn remove_element(&mut self, row: usize, row_off: usize) {
        let col = self.rows[row][row_off].var;
        let col_off = self.rows[row][row_off].off;
        let col_last = self.cols[col].len() - 1;
        if col_off != col_last {
            let cc = self.cols[col][col_last];
            self.cols[col][col_off] = cc;
            self.rows[cc.row][cc.off].off = col_off;
        }
        let row_last = self.rows[row].len() - 1;
        if row_off != row_last {
            let tail = self.rows[row][row_last].clone();
            self.cols[tail.var][tail.off].off = row_off;
            self.rows[row][row_off] = tail;
        }
        self.cols[col].pop();
        self.rows[row].pop();
    }

    /// `pivot_row_to_row_given_cell`: eliminate `pivot_col` from row `ii` (the
    /// row of column cell `c`) with the pivot row `i`.
    fn pivot_row_to_row(&mut self, i: usize, c: ColCell, pivot_col: usize) {
        let ii = c.row;
        let alpha = self.rows[ii][c.off].coeff.neg();
        self.remove_element(ii, c.off);
        let prev = self.rows[ii].len();
        let mut offs: alloc::collections::BTreeMap<usize, usize> = self.rows[ii]
            .iter()
            .enumerate()
            .map(|(k, rc)| (rc.var, k))
            .collect();
        let mut cancelled = 0usize;
        let pivot_row: Vec<(usize, Rational)> = self.rows[i]
            .iter()
            .map(|rc| (rc.var, rc.coeff.clone()))
            .collect();
        for (j, cv) in pivot_row {
            if j == pivot_col {
                continue;
            }
            match offs.get(&j) {
                None => {
                    let k = self.rows[ii].len();
                    self.add_new_element(ii, j, alpha.mul(&cv));
                    offs.insert(j, k);
                }
                Some(&k) => {
                    self.rows[ii][k].coeff.addmul(&cv, &alpha);
                    if self.rows[ii][k].coeff.is_zero() {
                        cancelled += 1;
                    }
                }
            }
        }
        let mut k = prev;
        while k > 0 && cancelled > 0 {
            k -= 1;
            if self.rows[ii][k].coeff.is_zero() {
                self.remove_element(ii, k);
                cancelled -= 1;
            }
        }
    }

    /// `pivot_column_tableau`: make column `j` the unit column of `row`.
    fn pivot_column(&mut self, j: usize, row: usize) {
        let Some(p) = self.rows[row].iter().position(|rc| rc.var == j) else {
            return;
        };
        let a = self.rows[row][p].coeff.clone();
        for rc in self.rows[row].iter_mut() {
            if rc.var != j {
                rc.coeff = rc.coeff.div(&a);
            }
        }
        self.rows[row][p].coeff = rat(1);
        let Some(pci) = self.cols[j].iter().position(|cc| cc.row == row) else {
            return;
        };
        if pci != 0 {
            let c0 = self.cols[j][0];
            self.cols[j].swap(0, pci);
            let head = self.cols[j][0];
            self.rows[head.row][head.off].off = 0;
            self.rows[c0.row][c0.off].off = pci;
        }
        while self.cols[j].len() > 1 {
            let c = *self.cols[j].last().unwrap();
            self.pivot_row_to_row(row, c, j);
        }
    }

    /// Record a bound `x_j kind rhs` (`update_column_type_and_bound`). A
    /// bound no tighter than the current one changes nothing; `false` when
    /// it crosses the opposite bound.
    pub fn add_bound(&mut self, j: usize, kind: Kind, rhs: &Rational) -> bool {
        let (upper, y) = match kind {
            Kind::Le => (true, 0),
            Kind::Lt => (true, -1),
            Kind::Ge => (false, 0),
            Kind::Gt => (false, 1),
        };
        let b = Impq::new(rhs.clone(), rat(y));
        if upper {
            if self.lo[j].as_ref().is_some_and(|l| b < *l) {
                return false;
            }
            if self.hi[j].as_ref().is_none_or(|h| b < *h) {
                self.hi[j] = Some(b);
                self.mark_changed(j);
            }
        } else {
            if self.hi[j].as_ref().is_some_and(|h| b > *h) {
                return false;
            }
            if self.lo[j].as_ref().is_none_or(|l| b > *l) {
                self.lo[j] = Some(b);
                self.mark_changed(j);
            }
        }
        true
    }

    fn mark_changed(&mut self, j: usize) {
        if !self.changed.contains(&j) {
            self.changed.push(j);
        }
    }

    fn is_free(&self, j: usize) -> bool {
        self.lo[j].is_none() && self.hi[j].is_none()
    }

    fn is_fixed(&self, j: usize) -> bool {
        matches!((&self.lo[j], &self.hi[j]), (Some(l), Some(h)) if l == h)
    }

    fn feasible(&self, j: usize) -> bool {
        self.lo[j].as_ref().is_none_or(|l| self.x[j] >= *l)
            && self.hi[j].as_ref().is_none_or(|h| self.x[j] <= *h)
    }

    fn track(&mut self, j: usize) {
        if self.feasible(j) {
            self.inf.remove(&j);
        } else {
            self.inf.insert(j);
        }
    }

    /// Move the non-basic `x_j` onto the bound it violates
    /// (`make_column_feasible`); the change, if any.
    fn make_column_feasible(&mut self, j: usize) -> Option<Impq> {
        let x = &self.x[j];
        let target = match (&self.lo[j], &self.hi[j]) {
            (Some(l), _) if x < l => l.clone(),
            (_, Some(h)) if x > h => h.clone(),
            _ => return None,
        };
        let d = target.sub(x);
        self.x[j] = target;
        Some(d)
    }

    /// Restore feasibility (`find_feasible_solution`). `None` when `budget`
    /// pivots do not suffice, `Some(false)` when infeasible.
    pub fn solve(&mut self, budget: usize) -> Option<bool> {
        for j in core::mem::take(&mut self.changed) {
            if self.heading[j] >= 0 {
                self.track(j);
            } else if let Some(d) = self.make_column_feasible(j) {
                for k in 0..self.cols[j].len() {
                    let cc = self.cols[j][k];
                    let bj = self.basis[cc.row];
                    let a = self.rows[cc.row][cc.off].coeff.clone();
                    self.x[bj] = self.x[bj].sub(&d.scale(&a));
                    self.track(bj);
                }
            }
        }
        let mut bland = false;
        let mut left: BTreeSet<usize> = BTreeSet::new();
        let mut repeated = 0usize;
        for _ in 0..budget {
            let Some(&leaving) = self.inf.iter().next() else {
                return Some(true);
            };
            if !bland {
                if left.contains(&leaving) {
                    repeated += 1;
                    if repeated > 1000 {
                        bland = true;
                    }
                } else {
                    left.insert(leaving);
                }
            }
            let row = self.heading[leaving] as usize;
            let Some((entering, a_ent)) = self.find_entering(row, bland) else {
                return Some(false);
            };
            let x = self.x[leaving].clone();
            let new_val = match (&self.lo[leaving], &self.hi[leaving]) {
                (Some(l), _) if x < *l => l.clone(),
                (_, Some(h)) => h.clone(),
                _ => return Some(false),
            };
            let theta = x.sub(&new_val).scale(&a_ent.recip());
            self.x[leaving] = new_val;
            self.inf.remove(&leaving);
            // `update_x_tableau_rows`.
            self.x[entering] = self.x[entering].add(&theta);
            for k in 0..self.cols[entering].len() {
                let cc = self.cols[entering][k];
                let b = self.basis[cc.row];
                if b != leaving {
                    let a = self.rows[cc.row][cc.off].coeff.clone();
                    self.x[b] = self.x[b].sub(&theta.scale(&a));
                    self.track(b);
                }
            }
            self.pivot_column(entering, row);
            // `change_basis`.
            let pnb = (-self.heading[entering] - 1) as usize;
            self.heading[entering] = row as isize;
            self.basis[row] = entering;
            self.heading[leaving] = -(pnb as isize) - 1;
            self.nbasis[pnb] = leaving;
            self.track(entering);
        }
        if self.inf.is_empty() {
            Some(true)
        } else {
            None
        }
    }

    /// Can the non-basic cell's column move the way that makes the row's
    /// basic column grow (`grow`, z3's `monoid_can_decrease`) or shrink
    /// (`monoid_can_increase`)? The row reads `basic + Σ c·x = 0`.
    fn can_move(&self, rc: &RowCell, grow: bool) -> bool {
        let j = rc.var;
        if self.is_fixed(j) {
            return false;
        }
        if rc.coeff.is_positive() != grow {
            self.hi[j].as_ref().is_none_or(|h| self.x[j] < *h)
        } else {
            self.lo[j].as_ref().is_none_or(|l| self.x[j] > *l)
        }
    }

    /// The number of non-free basic columns depending on `j` other than `bj`,
    /// capped past `bound` (`get_num_of_not_free_basic_dependent_vars`).
    fn not_free_count(&self, j: usize, bound: usize, bj: usize) -> usize {
        let mut r = 0usize;
        for cc in &self.cols[j] {
            let b = self.basis[cc.row];
            if b == bj {
                continue;
            }
            if !self.is_free(b) {
                let old = r;
                r += 1;
                if old > bound {
                    return r;
                }
            }
        }
        r
    }

    /// `find_beneficial_entering_tableau_rows`.
    fn find_entering(&mut self, i: usize, bland: bool) -> Option<(usize, Rational)> {
        let bj = self.basis[i];
        let grow = self.lo[bj].as_ref().is_some_and(|l| self.x[bj] < *l);
        if bland {
            let mut best: Option<(usize, Rational)> = None;
            for rc in &self.rows[i] {
                if rc.var == bj || !self.can_move(rc, grow) {
                    continue;
                }
                if best.as_ref().is_none_or(|(b, _)| rc.var < *b) {
                    best = Some((rc.var, rc.coeff.clone()));
                }
            }
            return best;
        }
        let mut choice: Option<usize> = None;
        let mut nchoices = 0u32;
        let mut min_nf = usize::MAX;
        let mut best_sz = usize::MAX;
        for k in 0..self.rows[i].len() {
            let rc = &self.rows[i][k];
            let j = rc.var;
            if j == bj || !self.can_move(rc, grow) {
                continue;
            }
            let nf = self.not_free_count(j, min_nf, bj);
            let sz = self.cols[j].len();
            if nf < min_nf || (nf == min_nf && sz < best_sz) {
                min_nf = nf;
                best_sz = sz;
                choice = Some(k);
                nchoices = 1;
            } else if nf == min_nf && sz == best_sz {
                nchoices += 1;
                if self.rng.below(nchoices) == 0 {
                    choice = Some(k);
                }
            }
        }
        choice.map(|k| (self.rows[i][k].var, self.rows[i][k].coeff.clone()))
    }

    /// The columns' values at z3's `δ` (`init_model` / `get_value`).
    pub fn values(&self) -> Vec<Rational> {
        let mut delta = rat(1);
        let mut update = |l: &Impq, u: &Impq| {
            if l.x < u.x && l.y > u.y {
                let d = u.x.sub(&l.x).div(&l.y.sub(&u.y));
                if d < delta {
                    delta = d;
                }
            }
        };
        for j in 0..self.x.len() {
            if let Some(l) = &self.lo[j] {
                update(l, &self.x[j]);
            }
            if let Some(h) = &self.hi[j] {
                update(&self.x[j], h);
            }
        }
        let pairs: BTreeSet<&Impq> = self.x.iter().collect();
        loop {
            let singles: BTreeSet<Rational> =
                pairs.iter().map(|p| p.x.add(&p.y.mul(&delta))).collect();
            if singles.len() == pairs.len() {
                break;
            }
            delta = delta.div(&rat(2));
        }
        self.x.iter().map(|p| p.x.add(&p.y.mul(&delta))).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rng_matches_z3() {
        let mut r = Rng::new(0);
        let v: Vec<u32> = (0..4).map(|_| r.draw()).collect();
        assert_eq!(v, alloc::vec![38, 7719, 21238, 2437]);
    }

    #[test]
    fn umap_wraps_by_capacity() {
        assert_eq!(umap_order(&[9, 4, 5]), alloc::vec![9, 4, 5]);
        assert_eq!(umap_order(&[12, 4]), alloc::vec![12, 4]);
        assert_eq!(umap_order(&[6, 5, 4]), alloc::vec![4, 5, 6]);
    }

    /// `-2c + d + 2 < 0`: z3 makes `c` basic (the random tie-break) and
    /// takes `δ = 1`, printing `c = 3/2`, `d = 0`.
    #[test]
    fn strict_term_bound_like_z3() {
        let mut l = Lar::new(0);
        for v in [1, 1, 0, 0] {
            let j = l.add_var();
            l.add_bound(j, Kind::Ge, &rat(v));
            l.add_bound(j, Kind::Le, &rat(v));
        }
        let d = l.add_var();
        let c = l.add_var();
        let t = l.add_term(&[(d, rat(-1)), (c, rat(2))]);
        assert!(l.add_bound(t, Kind::Gt, &rat(2)));
        assert_eq!(l.solve(100), Some(true));
        let v = l.values();
        assert_eq!(v[c], Rational::new(Int::from(3), Int::from(2)));
        assert_eq!(v[d], rat(0));
    }
}

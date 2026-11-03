//! Levelwise single-cell construction (z3's default conflict explanation).
//!
//! Ported from `z3/src/nlsat/levelwise.cpp` (MIT), after Nalbach et al.,
//! "Levelwise construction of a single cylindrical algebraic cell" and
//! "Projective Delineability for Single Cell Construction" (SC² 2025). From the
//! polynomials of a conflict, it builds, level by level from the conflict
//! variable down, a cell around the sample bounded on each level by the
//! closest root functions, and projects only what keeps that cell sign- and
//! order-invariant: on the top level, resultants of polynomials with adjacent
//! roots; below, the "biggest cell" relation (every root function paired
//! with the cell bound on its side), discriminants, leading coefficients
//! (omitted where projective delineability allows), and non-nullification
//! witnesses. The cell becomes the lemma's root literals.
//!
//! Not ported: the spanning-tree relation (an optimization; the biggest-cell
//! relation is always valid) and linear cell approximations. Two
//! factors from the partial factorization that share a factor (an
//! identically zero resultant) abort to the classic projection.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::cmp::Ordering;

use crate::math::polynomial::{Polynomial, Var};
use crate::nlsat::realclosure::Alg;

use super::{ExplainErr, Kind, Solver, max_var, normalize};

/// A root function on the current level: the `i`-th root of `p`, valued `val`
/// at the sample, from the `ps_idx`-th level polynomial.
struct RootFn {
    val: Alg,
    p: Polynomial,
    i: u32,
    ps_idx: usize,
}

/// The cell's interval on one level: a section `p = root_i`, or a sector
/// between two root functions (`None`: infinite).
#[derive(Default)]
struct CellInterval {
    section: bool,
    l: Option<(Polynomial, u32)>,
    u: Option<(Polynomial, u32)>,
}

/// Per-explanation levelwise state.
struct Lws {
    todo: Vec<Polynomial>,
    level: Var,
    level_ps: Vec<Polynomial>,
    witnesses: Vec<Option<Polynomial>>,
    poly_has_roots: Vec<bool>,
    rfunc: Vec<RootFn>,
    pairs: BTreeSet<(usize, usize)>,
    l_rf: Option<usize>,
    u_rf: Option<usize>,
    side_mask: Vec<u8>,
    omit_lc: Vec<bool>,
    cell: Vec<CellInterval>,
}

impl Lws {
    fn add_pair(&mut self, j: usize, k: usize) {
        let (a, b) = (self.rfunc[j].ps_idx, self.rfunc[k].ps_idx);
        if a != b {
            self.pairs.insert((a.min(b), a.max(b)));
        }
    }
}

/// z3's `lws_witness_subs_lc` / `lws_witness_subs_disc` defaults.
const WITNESS_SUBS_LC: bool = true;
const WITNESS_SUBS_DISC: bool = true;

impl Solver {
    /// The levelwise single cell of `ps` (factors with maximal variable at
    /// most `max_x`), added to the lemma as root literals.
    pub(super) fn levelwise(&mut self, ps: &[Polynomial], max_x: Var) -> Result<(), ExplainErr> {
        let mut st = Lws {
            todo: Vec::new(),
            level: 0,
            level_ps: Vec::new(),
            witnesses: Vec::new(),
            poly_has_roots: Vec::new(),
            rfunc: Vec::new(),
            pairs: BTreeSet::new(),
            l_rf: None,
            u_rf: None,
            side_mask: Vec::new(),
            omit_lc: Vec::new(),
            cell: (0..max_x).map(|_| CellInterval::default()).collect(),
        };
        if max_x == 0 {
            return Ok(());
        }
        for p in ps {
            self.request_factorized(&mut st, p)?;
        }
        if st.todo.is_empty() {
            return Ok(());
        }
        if self.lws_extract(&mut st) == Some(max_x) {
            self.lws_top_level(&mut st, max_x)?;
        } else {
            st.todo.append(&mut st.level_ps);
        }
        while !st.todo.is_empty() {
            let Some(x) = self.lws_extract(&mut st) else {
                break;
            };
            if x >= max_x {
                return Err(ExplainErr::Restart);
            }
            self.lws_process_level(&mut st)?;
        }
        // The cell, as literals false at the sample.
        for (y, iv) in st.cell.iter().enumerate() {
            let y = y as Var;
            if iv.section {
                let (p, i) = iv.l.clone().expect("section bound");
                self.add_root_literal(Kind::RootEq, y, i, &p)?;
                continue;
            }
            if let Some((p, i)) = &iv.l {
                let k = if self.full_dimensional {
                    Kind::RootGe
                } else {
                    Kind::RootGt
                };
                self.add_root_literal(k, y, *i, p)?;
            }
            if let Some((p, i)) = &iv.u {
                let k = if self.full_dimensional {
                    Kind::RootLe
                } else {
                    Kind::RootLt
                };
                self.add_root_literal(k, y, *i, p)?;
            }
        }
        Ok(())
    }

    /// Move the todo polynomials of greatest maximal variable to the level
    /// set; that variable becomes the level.
    fn lws_extract(&mut self, st: &mut Lws) -> Option<Var> {
        let x = st.todo.iter().filter_map(max_var).max()?;
        let (mine, rest): (Vec<Polynomial>, Vec<Polynomial>) = core::mem::take(&mut st.todo)
            .into_iter()
            .partition(|p| max_var(p) == Some(x));
        st.todo = rest;
        st.level = x;
        st.level_ps = mine;
        Some(x)
    }

    /// Add the distinct non-constant factors of `p` to the todo set.
    fn request_factorized(&mut self, st: &mut Lws, p: &Polynomial) -> Result<(), ExplainErr> {
        if p.is_constant() {
            return Ok(());
        }
        self.spend(4)?;
        for f in crate::math::factor::factors(p) {
            let (f, _) = normalize(&f);
            if f.is_constant() || st.todo.contains(&f) || st.level_ps.contains(&f) {
                continue;
            }
            st.todo.push(f);
        }
        Ok(())
    }

    /// The first nonzero, non-constant principal subresultant coefficient of
    /// `a` and `b` in `x` (`None`: a nonzero constant); an identically zero
    /// chain (a common factor) aborts levelwise.
    fn lws_psc(
        &mut self,
        a: &Polynomial,
        b: &Polynomial,
        x: Var,
    ) -> Result<Option<Polynomial>, ExplainErr> {
        let chain = self.psc_chain_cached(a, b, x)?;
        let s = &chain[0];
        if s.is_zero() {
            return Err(ExplainErr::Restart);
        }
        Ok((!s.is_constant()).then(|| s.clone()))
    }

    fn lws_discriminant(
        &mut self,
        p: &Polynomial,
        x: Var,
    ) -> Result<Option<Polynomial>, ExplainErr> {
        if p.degree_of(x) < 2 {
            return Ok(None);
        }
        let d = p.deriv_var(x);
        self.lws_psc(p, &d, x)
    }

    /// A coefficient of `p` in `x` nonzero at the sample, preferring a
    /// constant, then the simplest (`choose_nonzero_coeff`); `None` when `p`
    /// is nullified.
    fn choose_nonzero_coeff(
        &mut self,
        p: &Polynomial,
        x: Var,
    ) -> Result<Option<Polynomial>, ExplainErr> {
        let d = p.degree_of(x);
        for j in 0..=d {
            let c = p.coeff_of_var(x, j);
            if !c.is_zero() && c.is_constant() {
                return Ok(Some(c));
            }
        }
        let mut best: Option<(u32, usize, Option<Var>, Polynomial)> = None;
        for j in 0..=d {
            let c = p.coeff_of_var(x, j);
            if c.is_zero() || self.sign(&c)? == 0 {
                continue;
            }
            let key = (c.total_degree(), c.num_terms(), max_var(&c));
            let better = match &best {
                None => true,
                Some((td, sz, mv, _)) => {
                    key.0 < *td
                        || (key.0 == *td
                            && (key.1 < *sz || (key.1 == *sz && (mv.is_none() || key.2 < *mv))))
                }
            };
            if better {
                best = Some((key.0, key.1, key.2, c));
            }
        }
        Ok(best.map(|b| b.3))
    }

    /// A polynomial whose coefficients all vanish at the sample: project its
    /// coefficients and the first partial derivatives (by increasing order)
    /// that do not vanish (`handle_nullified_poly`).
    fn handle_nullified_poly(&mut self, st: &mut Lws, p: &Polynomial) -> Result<(), ExplainErr> {
        let x = st.level;
        for j in 0..=p.degree_of(x) {
            let c = p.coeff_of_var(x, j);
            self.request_factorized(st, &c)?;
        }
        let mut cur: Vec<(Polynomial, Var)> = alloc::vec![(p.clone(), 0)];
        while !cur.is_empty() {
            let mut next: Vec<(Polynomial, Var)> = Vec::new();
            for (q, min_v) in &cur {
                let Some(mv) = max_var(q) else {
                    continue;
                };
                for y in *min_v..=mv {
                    if q.degree_of(y) == 0 {
                        continue;
                    }
                    let dq = q.deriv_var(y);
                    if dq.is_constant() {
                        continue;
                    }
                    if self.sign(&dq)? != 0 {
                        self.request_factorized(st, &dq)?;
                        return Ok(());
                    }
                    next.push((dq, y));
                }
            }
            for (dq, _) in &next {
                self.request_factorized(st, dq)?;
            }
            self.spend(4)?;
            cur = next;
        }
        Ok(())
    }

    /// A non-nullification witness per level polynomial; nullified ones are
    /// handled, and the same-level polynomials that adds are absorbed.
    fn collect_non_null_witnesses(&mut self, st: &mut Lws) -> Result<(), ExplainErr> {
        st.witnesses.clear();
        let x = st.level;
        let mut i = 0;
        while i < st.level_ps.len() {
            let p = st.level_ps[i].clone();
            let w = self.choose_nonzero_coeff(&p, x)?;
            if w.is_none() {
                if x == self.xk_var() {
                    // Nullified on the conflict level: not expected.
                    return Err(ExplainErr::Restart);
                }
                self.handle_nullified_poly(st, &p)?;
            }
            st.witnesses.push(w);
            if i + 1 == st.level_ps.len() {
                let (mine, rest): (Vec<Polynomial>, Vec<Polynomial>) =
                    core::mem::take(&mut st.todo)
                        .into_iter()
                        .partition(|q| max_var(q) == Some(x));
                st.todo = rest;
                st.level_ps.extend(mine);
            }
            i += 1;
        }
        Ok(())
    }

    /// The variable of the current stage (the conflict level), or a value
    /// above all variables.
    fn xk_var(&self) -> Var {
        self.xk.map_or(Var::MAX, |x| x as Var)
    }

    /// Projection of `p`: its leading coefficient, discriminant and witness
    /// as requested (`add_projection_for_poly`).
    fn add_projection_for_poly(
        &mut self,
        st: &mut Lws,
        p: &Polynomial,
        witness: Option<Polynomial>,
        add_lc: bool,
        add_disc: bool,
    ) -> Result<(), ExplainErr> {
        let x = st.level;
        let mut add_nz = witness.as_ref().is_some_and(|w| !w.is_constant());
        if add_lc {
            let lc = p.coeff_of_var(x, p.degree_of(x));
            self.request_factorized(st, &lc)?;
            if add_nz && WITNESS_SUBS_DISC && !lc.is_zero() && self.sign(&lc)? != 0 {
                add_nz = false;
            }
        }
        if add_disc && let Some(disc) = self.lws_discriminant(p, x)? {
            self.request_factorized(st, &disc)?;
            if add_nz && WITNESS_SUBS_DISC && self.sign(&disc)? != 0 {
                add_nz = false;
            }
        }
        if add_nz && let Some(w) = witness {
            self.request_factorized(st, &w)?;
        }
        Ok(())
    }

    /// The conflict level: resultants of polynomials with adjacent roots,
    /// then each polynomial's projection (`process_top_level`).
    fn lws_top_level(&mut self, st: &mut Lws, x: Var) -> Result<(), ExplainErr> {
        self.collect_non_null_witnesses(st)?;
        // add_adjacent_root_resultants
        st.poly_has_roots = alloc::vec![false; st.level_ps.len()];
        let mut root_vals: Vec<(Alg, usize)> = Vec::new();
        for i in 0..st.level_ps.len() {
            let p = st.level_ps[i].clone();
            let roots = self.roots(&p, x)?;
            st.poly_has_roots[i] = !roots.is_empty();
            for r in roots {
                root_vals.push((r, i));
            }
        }
        if root_vals.len() >= 2 {
            root_vals.sort_by(|a, b| a.0.compare(&b.0));
            let mut added: BTreeSet<(usize, usize)> = BTreeSet::new();
            for j in 0..root_vals.len() - 1 {
                let (a, b) = (root_vals[j].1, root_vals[j + 1].1);
                if a == b || !added.insert((a.min(b), a.max(b))) {
                    continue;
                }
                let (p1, p2) = (st.level_ps[a].clone(), st.level_ps[b].clone());
                if let Some(r) = self.lws_psc(&p1, &p2, x)? {
                    self.request_factorized(st, &r)?;
                }
            }
        }
        for i in 0..st.level_ps.len() {
            let p = st.level_ps[i].clone();
            let lc = p.coeff_of_var(x, p.degree_of(x));
            let mut add_lc = true;
            // Lemma 3.2 of "Projective Delineability for Single Cell
            // Construction": a root-free polynomial with a nonvanishing
            // leading coefficient needs only its discriminant.
            if !st.poly_has_roots[i] && !lc.is_zero() && self.sign(&lc)? != 0 {
                add_lc = false;
                st.witnesses[i] = None;
            }
            let w = st.witnesses[i].clone();
            self.add_projection_for_poly(st, &p, w, add_lc, true)?;
        }
        Ok(())
    }

    /// Order of root functions: by value, ties by degree (`desc`: higher
    /// first), then by polynomial (`root_function_lt`).
    fn root_fn_cmp(a: &RootFn, b: &RootFn, x: Var, desc: bool) -> Ordering {
        if a.p == b.p {
            return a.i.cmp(&b.i);
        }
        let c = a.val.compare(&b.val);
        if c != Ordering::Equal {
            return c;
        }
        let (da, db) = (a.p.degree_of(x), b.p.degree_of(x));
        if da != db {
            return if desc { db.cmp(&da) } else { da.cmp(&db) };
        }
        a.p.cmp(&b.p)
    }

    /// The root functions around the sample and the level's interval
    /// (`build_interval`); `false` when no polynomial has a root.
    fn lws_build_interval(&mut self, st: &mut Lws) -> Result<bool, ExplainErr> {
        let x = st.level;
        st.rfunc.clear();
        st.pairs.clear();
        st.l_rf = None;
        st.u_rf = None;
        st.cell[x as usize] = CellInterval::default();
        let v = self.assignment[x as usize].clone().expect("assigned");
        st.poly_has_roots = alloc::vec![false; st.level_ps.len()];
        let mut lhalf: Vec<RootFn> = Vec::new();
        let mut uhalf: Vec<RootFn> = Vec::new();
        for i in 0..st.level_ps.len() {
            let p = st.level_ps[i].clone();
            let roots = self.roots(&p, x)?;
            st.poly_has_roots[i] = !roots.is_empty();
            let mut lower = None;
            let mut upper = None;
            let mut section = false;
            for (k, r) in roots.iter().enumerate() {
                match r.compare(&v) {
                    Ordering::Greater => {
                        upper = Some(k);
                        break;
                    }
                    Ordering::Equal => {
                        lower = Some(k);
                        section = true;
                        break;
                    }
                    Ordering::Less => lower = Some(k),
                }
            }
            if let Some(k) = lower {
                lhalf.push(RootFn {
                    val: roots[k].clone(),
                    p: p.clone(),
                    i: k as u32 + 1,
                    ps_idx: i,
                });
                if section {
                    continue;
                }
            }
            if let Some(k) = upper {
                uhalf.push(RootFn {
                    val: roots[k].clone(),
                    p,
                    i: k as u32 + 1,
                    ps_idx: i,
                });
            }
        }
        if lhalf.is_empty() && uhalf.is_empty() {
            return Ok(false);
        }
        // Ties: the lower bound (last of the lower half) and the upper bound
        // (first of the upper half) come from the lowest-degree polynomials.
        lhalf.sort_by(|a, b| Self::root_fn_cmp(a, b, x, true));
        uhalf.sort_by(|a, b| Self::root_fn_cmp(a, b, x, false));
        let mid = lhalf.len();
        st.rfunc = lhalf;
        st.rfunc.extend(uhalf);
        let iv = &mut st.cell[x as usize];
        if mid > 0 {
            let l = mid - 1;
            st.l_rf = Some(l);
            let r = &st.rfunc[l];
            if r.val.compare(&v) == Ordering::Equal {
                iv.section = true;
                iv.l = Some((r.p.clone(), r.i));
                st.u_rf = Some(l);
            } else {
                iv.l = Some((r.p.clone(), r.i));
                if mid < st.rfunc.len() {
                    st.u_rf = Some(mid);
                    let u = &st.rfunc[mid];
                    iv.u = Some((u.p.clone(), u.i));
                }
            }
        } else {
            st.u_rf = Some(0);
            let u = &st.rfunc[0];
            iv.u = Some((u.p.clone(), u.i));
        }
        // compute_side_mask
        st.side_mask = alloc::vec![0u8; st.level_ps.len()];
        if let Some(l) = st.l_rf {
            for (i, rf) in st.rfunc.iter().enumerate() {
                st.side_mask[rf.ps_idx] |= if i <= l { 1 } else { 2 };
            }
        }
        Ok(true)
    }

    /// One level below the conflict level (`process_level`, biggest-cell
    /// relation in both the section and the sector case).
    fn lws_process_level(&mut self, st: &mut Lws) -> Result<(), ExplainErr> {
        let x = st.level;
        st.omit_lc.clear();
        st.side_mask.clear();
        self.collect_non_null_witnesses(st)?;
        let have_interval = self.lws_build_interval(st)?;
        let section = st.cell[x as usize].section;
        if have_interval {
            let n = st.rfunc.len();
            if section {
                let l = st.l_rf.expect("section bound");
                for j in 0..l {
                    st.add_pair(j, l);
                }
                for j in l + 1..n {
                    st.add_pair(l, j);
                }
            } else {
                if let Some(l) = st.l_rf {
                    for j in 0..l {
                        st.add_pair(j, l);
                    }
                }
                if let Some(u) = st.u_rf {
                    for j in u + 1..n {
                        st.add_pair(u, j);
                    }
                }
                if let (Some(l), Some(u)) = (st.l_rf, st.u_rf) {
                    st.add_pair(l, u);
                }
                // noLdcf: a non-bound polynomial with roots on both sides.
                st.omit_lc = alloc::vec![false; st.level_ps.len()];
                if !st.pairs.is_empty() && !st.side_mask.is_empty() {
                    let lb = st.l_rf.map(|l| st.rfunc[l].ps_idx);
                    let ub = st.u_rf.map(|u| st.rfunc[u].ps_idx);
                    for i in 0..st.level_ps.len() {
                        if st.side_mask[i] == 3 && Some(i) != lb && Some(i) != ub {
                            st.omit_lc[i] = true;
                        }
                    }
                }
            }
        }
        if section {
            let section_poly = st.cell[x as usize].l.clone().expect("section").0;
            let with_roots: BTreeSet<usize> = st.rfunc.iter().map(|r| r.ps_idx).collect();
            for i in 0..st.level_ps.len() {
                let p = st.level_ps[i].clone();
                let w = st.witnesses[i].clone();
                if p == section_poly || !with_roots.contains(&i) {
                    self.add_projection_for_poly(st, &p, w, true, true)?;
                } else {
                    self.add_projection_for_poly(st, &p, w, false, true)?;
                }
            }
        } else {
            for i in 0..st.level_ps.len() {
                let p = st.level_ps[i].clone();
                let add_lc = !st.omit_lc.get(i).copied().unwrap_or(false);
                let mut w = st.witnesses[i].clone();
                if add_lc && w.as_ref().is_some_and(|w| !w.is_constant()) {
                    let lc = p.coeff_of_var(x, p.degree_of(x));
                    if !lc.is_zero() && WITNESS_SUBS_LC && self.sign(&lc)? != 0 {
                        w = None;
                    }
                }
                self.add_projection_for_poly(st, &p, w, add_lc, true)?;
            }
        }
        // add_relation_resultants
        let pairs: Vec<(usize, usize)> = st.pairs.iter().copied().collect();
        for (a, b) in pairs {
            let (p1, p2) = (st.level_ps[a].clone(), st.level_ps[b].clone());
            if let Some(r) = self.lws_psc(&p1, &p2, x)? {
                self.request_factorized(st, &r)?;
            }
        }
        Ok(())
    }
}

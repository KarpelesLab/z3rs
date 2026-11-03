//! Core normalization and simplification before a conflict is explained.
//!
//! Ported from `z3/src/nlsat/nlsat_explain.cpp` (`normalize`, `simplify`,
//! `select_eq`, `select_lower_stage_eq`; MIT), with z3's
//! `simplify_conflicts` default. An inequality atom is viewed as z3 stores
//! it, a product of factors (`atom_factors`). Normalization drops the
//! factors of lower stages (their current signs become assumptions of the
//! lemma) and the vanishing leading coefficients; simplification rewrites the
//! core's literals by pseudo-division with an equation of the core, then with
//! the equations recorded for lower stages (`var2eq`).

use alloc::vec::Vec;

use puremp::{Int, Rational};

use crate::math::polynomial::{Monomial, Polynomial, Var};

use super::{ExplainErr, FALSE_LIT, Just, Kind, LBool, Lit, Res, Solver, TRUE_LIT, max_var};

/// The equation used to rewrite the core (`eq_info`).
struct EqInfo {
    eq: Polynomial,
    x: Var,
    k: u32,
    lc: Polynomial,
    lc_sign: i32,
    lc_const: bool,
    lc_add: bool,
    lc_add_ineq: bool,
}

impl EqInfo {
    fn add_lc_ineq(&mut self) {
        self.lc_add = true;
        self.lc_add_ineq = true;
    }
    fn add_lc_diseq(&mut self) {
        if !self.lc_add {
            self.lc_add = true;
            self.lc_add_ineq = false;
        }
    }
}

/// The pseudo-remainder of `a` by `b` in `x` and the number of
/// multiplications by `lc(b)` performed (z3's `pseudo_remainder`).
fn pseudo_remainder(a: &Polynomial, b: &Polynomial, x: Var) -> (u32, Polynomial) {
    let db = b.degree_of(x);
    let lb = b.coeff_of_var(x, db);
    let xpow = |j: u32| {
        Polynomial::from_terms(alloc::vec![(
            Rational::from_integer(Int::from(1)),
            Monomial::from_powers(&[(x, j)])
        )])
    };
    let rb = b.sub(&lb.mul(&xpow(db)));
    let mut r = a.clone();
    let mut d = 0;
    loop {
        let dr = r.degree_of(x);
        if r.is_zero() || db > dr {
            return (d, r);
        }
        let lr = r.coeff_of_var(x, dr);
        let red = r.sub(&lr.mul(&xpow(dr)));
        r = lb.mul(&red).sub(&lr.mul(&xpow(dr - db)).mul(&rb));
        d += 1;
    }
}

impl Solver {
    /// The factors of an inequality atom with their parity (`true`: even
    /// multiplicity), and the sign of the constant left over, so that the
    /// atom's polynomial is `c · Π fᵢ^mᵢ` (memoized per atom).
    pub(super) fn atom_factors(&mut self, ai: usize) -> Res<super::AtomFactors> {
        if let Some(Some(r)) = self.atom_factor_cache.get(ai) {
            return Ok(r.clone());
        }
        let p = self.atoms[ai].p.clone();
        let fs = self.factors_cached(&p)?;
        let mut rest = p.clone();
        let mut out = Vec::with_capacity(fs.len());
        for f in fs {
            let mut m = 0u32;
            while let Some(q) = rest.div_exact(&f) {
                rest = q;
                m += 1;
            }
            if m == 0 {
                out.clear();
                break;
            }
            out.push((f, m.is_multiple_of(2)));
        }
        let r = match rest.as_constant() {
            Some(c) if !c.is_zero() && !out.is_empty() => (out, c.signum()),
            _ => (alloc::vec![(p, false)], 1),
        };
        if self.atom_factor_cache.len() <= ai {
            self.atom_factor_cache.resize(ai + 1, None);
        }
        self.atom_factor_cache[ai] = Some(r.clone());
        Ok(r)
    }

    /// The literal `Π fᵢ^(2 if even else 1) ⋈ 0` (`mk_ineq_literal` over
    /// factors).
    fn mk_factored_literal(&mut self, kind: Kind, fs: &[(Polynomial, bool)]) -> Lit {
        let mut p = Polynomial::constant(Rational::from_integer(Int::from(1)));
        for (f, even) in fs {
            p = p.mul(f);
            if *even {
                p = p.mul(f);
            }
        }
        self.mk_ineq_literal(kind, &p)
    }

    /// The truth value of literal `l` of atom kind `kind` whose polynomial
    /// has sign `s`.
    fn lit_of_sign(kind: Kind, neg: bool, s: i32) -> Lit {
        let atom_val = Self::satisfied(s, kind);
        if atom_val != neg { TRUE_LIT } else { FALSE_LIT }
    }

    /// Normalize a core literal with respect to the conflict variable `max`
    /// (`normalize(literal, var)`): lower-stage factors become assumptions,
    /// vanishing coefficients of `max` are eliminated.
    pub(super) fn normalize_lit(&mut self, l: Lit, max: Var) -> Result<Lit, ExplainErr> {
        if l == TRUE_LIT || l == FALSE_LIT {
            return Ok(l);
        }
        let Some(ai) = self.bool2atom[l.var() as usize] else {
            return Ok(l);
        };
        let kind = self.atoms[ai].kind;
        if kind.is_root() {
            return Ok(l);
        }
        let (fs, csign) = self.atom_factors(ai)?;
        let mut atom_sign = csign;
        let mut normalized = false;
        let mut kept: Vec<(Polynomial, bool)> = Vec::new();
        for (f, even) in fs {
            let mut p = f.clone();
            if max_var(&p) == Some(max) {
                p = self.elim_vanishing(p)?;
            }
            if p.is_constant() || max_var(&p).is_some_and(|v| v < max) {
                let s = self.sign(&p)?;
                if !p.is_constant() {
                    self.lower_stage_polys.push(p.clone());
                    if s == 0 {
                        self.add_assumption(Kind::Eq, &p, false);
                    } else if even {
                        self.add_assumption(Kind::Eq, &p, true);
                    } else if s < 0 {
                        self.add_assumption(Kind::Lt, &p, false);
                    } else {
                        self.add_assumption(Kind::Gt, &p, false);
                    }
                }
                if s == 0 {
                    return Ok(Self::lit_of_sign(kind, l.sign(), 0));
                } else if s < 0 && !even {
                    atom_sign = -atom_sign;
                }
                normalized = true;
            } else {
                if p != f {
                    normalized = true;
                }
                kept.push((p, even));
            }
        }
        if kept.is_empty() {
            return Ok(Self::lit_of_sign(kind, l.sign(), atom_sign));
        }
        if normalized {
            let k = if atom_sign < 0 { kind.flip() } else { kind };
            let nl = self.mk_factored_literal(k, &kept);
            return Ok(if l.sign() { nl.complement() } else { nl });
        }
        Ok(l)
    }

    /// Normalize the core; `false` when a literal became false (the
    /// assumptions alone imply the conflict and the core is emptied).
    pub(super) fn normalize_core(&mut self, c: &mut Vec<Lit>, max: Var) -> Result<(), ExplainErr> {
        let mut out = Vec::with_capacity(c.len());
        for &l in c.iter() {
            let nl = self.normalize_lit(l, max)?;
            if nl == TRUE_LIT {
                continue;
            }
            if nl == FALSE_LIT {
                c.clear();
                return Ok(());
            }
            out.push(nl);
        }
        *c = out;
        Ok(())
    }

    /// Rewrite literal `l` with the equation of `info`
    /// (`simplify(literal, eq_info, ...)`).
    fn simplify_lit(&mut self, l: Lit, info: &mut EqInfo, max: Var) -> Result<Lit, ExplainErr> {
        let Some(ai) = self.bool2atom[l.var() as usize] else {
            return Ok(l);
        };
        let kind = self.atoms[ai].kind;
        if kind.is_root() {
            return Ok(l);
        }
        let (fs, csign) = self.atom_factors(ai)?;
        if fs.len() == 1 && fs[0].0 == info.eq {
            return Ok(l);
        }
        let mut atom_sign = csign;
        let mut modified = false;
        let mut new_fs: Vec<(Polynomial, bool)> = Vec::new();
        for (f, even) in fs {
            if f.degree_of(info.x) < info.k {
                new_fs.push((f, even));
                continue;
            }
            modified = true;
            self.spend(4)?;
            let (d, r) = pseudo_remainder(&f, &info.eq, info.x);
            if d % 2 == 1 && !even && info.lc_sign < 0 {
                atom_sign = -atom_sign;
            }
            if r.is_constant() {
                let s = r.as_constant().expect("constant").signum();
                if s == 0 {
                    if !info.lc_const {
                        info.add_lc_diseq();
                    }
                    return Ok(Self::lit_of_sign(kind, l.sign(), 0));
                }
                if !info.lc_const {
                    if d % 2 == 0 || even || kind == Kind::Eq {
                        info.add_lc_diseq();
                    } else {
                        info.add_lc_ineq();
                    }
                }
                if s < 0 && !even {
                    atom_sign = -atom_sign;
                }
            } else {
                new_fs.push((r, even));
                if !info.lc_const {
                    if d % 2 == 0 || even || kind == Kind::Eq {
                        info.add_lc_diseq();
                    } else {
                        info.add_lc_ineq();
                    }
                }
            }
        }
        if !modified {
            return Ok(l);
        }
        let k = if atom_sign < 0 { kind.flip() } else { kind };
        let nl = self.mk_factored_literal(k, &new_fs);
        let nl = if l.sign() { nl.complement() } else { nl };
        if nl == TRUE_LIT || nl == FALSE_LIT {
            return Ok(nl);
        }
        if self.lit_max_var(nl).is_some_and(|v| v < max) {
            if self.value(nl)? == LBool::True {
                return Ok(l);
            }
            self.add_literal(nl);
            return Ok(TRUE_LIT);
        }
        self.normalize_lit(nl, max)
    }

    /// Rewrite the core with equation `eq`; whether it changed
    /// (`simplify(C, eq, max)`).
    fn simplify_core_with(
        &mut self,
        c: &mut Vec<Lit>,
        eq: &Polynomial,
        max: Var,
    ) -> Result<bool, ExplainErr> {
        let x = max_var(eq).expect("non-constant equation");
        let k = eq.degree_of(x);
        let lc = eq.coeff_of_var(x, k);
        let lc_sign = self.sign(&lc)?;
        let mut info = EqInfo {
            eq: eq.clone(),
            x,
            k,
            lc_const: lc.is_constant(),
            lc,
            lc_sign,
            lc_add: false,
            lc_add_ineq: false,
        };
        let mut modified = false;
        let mut out = Vec::with_capacity(c.len());
        let mut falsified = false;
        for &l in c.iter() {
            let nl = self.simplify_lit(l, &mut info, max)?;
            if nl == l {
                out.push(l);
                continue;
            }
            modified = true;
            if nl == TRUE_LIT {
                continue;
            }
            if nl == FALSE_LIT {
                falsified = true;
                break;
            }
            out.push(nl);
        }
        *c = if falsified { Vec::new() } else { out };
        if info.lc_add {
            if info.lc_add_ineq {
                let k = if info.lc_sign < 0 { Kind::Lt } else { Kind::Gt };
                self.add_assumption(k, &info.lc, false);
            } else {
                self.add_assumption(Kind::Eq, &info.lc, true);
            }
        }
        Ok(modified)
    }

    /// An equation of the core (single odd factor) of least degree in `max`
    /// (`select_eq`).
    fn select_eq(&mut self, c: &[Lit], max: Var) -> Res<Option<Polynomial>> {
        let mut best: Option<(u32, Polynomial)> = None;
        for &l in c {
            if l.sign() {
                continue;
            }
            let Some(ai) = self.bool2atom[l.var() as usize] else {
                continue;
            };
            if self.atoms[ai].kind != Kind::Eq {
                continue;
            }
            let (fs, _) = self.atom_factors(ai)?;
            if fs.len() > 1 || fs[0].1 {
                continue;
            }
            let d = fs[0].0.degree_of(max);
            if d > 0 && best.as_ref().is_none_or(|(bd, _)| d < *bd) {
                let stop = d == 1;
                best = Some((d, fs[0].0.clone()));
                if stop {
                    break;
                }
            }
        }
        Ok(best.map(|b| b.1))
    }

    /// An equation recorded for a lower stage `y` (with a constant leading
    /// coefficient) able to rewrite a factor of the core
    /// (`select_lower_stage_eq`): its atom.
    fn select_lower_stage_eq(&mut self, c: &[Lit], max: Var) -> Res<Option<usize>> {
        for &l in c {
            let Some(ai) = self.bool2atom[l.var() as usize] else {
                continue;
            };
            if self.atoms[ai].kind.is_root() {
                continue;
            }
            let (fs, _) = self.atom_factors(ai)?;
            for (p, _) in &fs {
                for y in p.vars() {
                    if y >= max {
                        continue;
                    }
                    let Some(eqa) = self.var2eq[y as usize] else {
                        continue;
                    };
                    let eq_p = self.atoms[eqa].p.clone();
                    let d = eq_p.degree_of(y);
                    if eq_p.coeff_of_var(y, d).as_constant().is_none() {
                        continue;
                    }
                    if p.degree_of(y) >= d {
                        return Ok(Some(eqa));
                    }
                }
            }
        }
        Ok(None)
    }

    /// Simplify the core with its equations, then with the lower stages'
    /// (`simplify(C, max)`).
    pub(super) fn simplify_core(&mut self, c: &mut Vec<Lit>, max: Var) -> Result<(), ExplainErr> {
        let mut rounds = 0;
        while !c.is_empty() && rounds < 64 {
            rounds += 1;
            let Some(eq) = self.select_eq(c, max)? else {
                break;
            };
            if !self.simplify_core_with(c, &eq, max)? {
                break;
            }
        }
        while !c.is_empty() && rounds < 128 {
            rounds += 1;
            let Some(eqa) = self.select_lower_stage_eq(c, max)? else {
                break;
            };
            let eq_p = self.atoms[eqa].p.clone();
            self.simplify_core_with(c, &eq_p, max)?;
            // The equation is an assumption of the lemma.
            let b = self.atom_bool[eqa];
            self.add_literal(Lit::new(b, true));
        }
        Ok(())
    }

    /// Record an equation literal set true for the current stage
    /// (`updt_eq`): positive, a single odd factor, justified by a clause, a
    /// decision or an empty lazy core; kept if of least degree.
    pub(super) fn updt_eq(&mut self, l: Lit) {
        if l.sign() {
            return;
        }
        let Some(ai) = self.bool2atom[l.var() as usize] else {
            return;
        };
        if self.atoms[ai].kind != Kind::Eq {
            return;
        }
        match &self.justs[l.var() as usize] {
            Just::Lazy(core) if !core.is_empty() => return,
            _ => {}
        }
        let Ok((fs, _)) = self.atom_factors(ai) else {
            return;
        };
        if fs.len() > 1 || fs[0].1 {
            return;
        }
        let Some(x) = self.xk else {
            return;
        };
        if self.atoms[ai].x as usize != x {
            return;
        }
        if let Some(old) = self.var2eq[x]
            && self.atoms[old].deg <= self.atoms[ai].deg
        {
            return;
        }
        self.trail.push(super::Trail::UpdtEq(self.var2eq[x]));
        self.var2eq[x] = Some(ai);
    }
}

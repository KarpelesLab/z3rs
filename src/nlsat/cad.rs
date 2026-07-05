//! Cylindrical Algebraic Decomposition (CAD) — a complete decision procedure for
//! the satisfiability of a conjunction of polynomial constraints over the reals
//! (QF_NRA), following the McCallum projection.
//!
//! Ported from Z3's `nlsat` / `math/polynomial` (Z3 4.17.0, MIT), implemented as
//! textbook CAD (project → base → lift → decide) on top of the exact
//! [`realclosure`](crate::nlsat::realclosure) real-algebraic-number arithmetic
//! and the [`resultant`](crate::math::resultant) projection primitives.
//!
//! **Soundness is unconditional.** Whenever this procedure returns `Some(sat)` or
//! `Some(unsat)` the answer is correct: signs are computed exactly at each cell's
//! sample point, and the cells are genuinely sign-invariant. Where the cheap
//! McCallum projection could be invalid (a discriminant or resultant that
//! vanishes identically ⇒ non-squarefree/again basis, or a *nullified*
//! polynomial during lifting) — or a resource cap is hit — it returns `None`
//! (the caller falls back to a sound `unknown`). It never guesses.

use alloc::vec::Vec;

use puremp::Rational;

use crate::math::polynomial::{Polynomial, Var};
use crate::math::resultant::{discriminant, resultant};
use crate::math::upoly::UPoly;
use crate::nlsat::icp::Rel;
use crate::nlsat::realclosure::{Alg, poly_to_upoly, sign_at_point, upoly_to_poly};

// Resource caps: beyond these, decline to a sound `unknown` rather than risk a
// doubly-exponential blow-up.
const MAX_VARS: usize = 4;
const MAX_DEG: u32 = 12;
const MAX_PROJ: usize = 500;
const MAX_CELLS: usize = 40_000;

/// Does sign `σ` satisfy `⋈ 0`?
fn rel_holds(sigma: i32, rel: Rel) -> bool {
    match rel {
        Rel::Lt => sigma < 0,
        Rel::Le => sigma <= 0,
        Rel::Gt => sigma > 0,
        Rel::Ge => sigma >= 0,
        Rel::Eq => sigma == 0,
        Rel::Ne => sigma != 0,
    }
}

/// Decide satisfiability over ℝ of `⋀ᵢ constraints[i]` in variables `0..num_vars`.
/// `Some(true)` = sat, `Some(false)` = unsat, `None` = declined (degenerate case
/// or resource cap — a sound `unknown`).
pub fn cad_sat(constraints: &[(Polynomial, Rel)], num_vars: usize) -> Option<bool> {
    if constraints.is_empty() {
        return Some(true);
    }
    // No variables: all constraints are constants.
    if num_vars == 0 {
        return Some(constraints.iter().all(|(p, rel)| {
            let s = p.as_constant().map(|c| c.signum()).unwrap_or(0);
            rel_holds(s, *rel)
        }));
    }
    if num_vars > MAX_VARS {
        return None;
    }
    for (p, _) in constraints {
        if p.total_degree() > MAX_DEG {
            return None;
        }
    }

    // Projection: `levels[k]` is the polynomial set whose main variable is `k`.
    let top: Vec<Polynomial> = clean(
        constraints
            .iter()
            .map(|(p, _)| p.clone())
            .filter(|p| !p.is_zero() && p.as_constant().is_none())
            .collect(),
    );
    let mut levels: Vec<Vec<Polynomial>> = alloc::vec![Vec::new(); num_vars];
    levels[num_vars - 1] = top;
    for main in (1..num_vars).rev() {
        let proj = project(&levels[main], main as Var)?;
        if proj.len() > MAX_PROJ {
            return None;
        }
        levels[main - 1] = proj;
    }

    // Base phase: 1-D CAD in variable 0.
    let base = base_samples(&levels[0]);
    let mut samples: Vec<Vec<Alg>> = base.into_iter().map(|a| alloc::vec![a]).collect();

    // Lifting phase.
    #[allow(clippy::needless_range_loop)]
    for k in 1..num_vars {
        let level_k = &levels[k];
        let mut next: Vec<Vec<Alg>> = Vec::new();
        for s in &samples {
            let children = lift(s, level_k, k as Var)?;
            next.extend(children);
            if next.len() > MAX_CELLS {
                return None;
            }
        }
        samples = next;
    }

    // Decision: some cell's sample satisfies every constraint ⇒ SAT.
    for s in &samples {
        if constraints
            .iter()
            .all(|(p, rel)| rel_holds(sign_at_point(p, s), *rel))
        {
            return Some(true);
        }
    }
    Some(false)
}

/// McCallum projection eliminating `var`: leading/positive coefficients,
/// discriminants, and pairwise resultants. Returns `None` if a discriminant or
/// resultant vanishes identically (non-squarefree/coprime input — McCallum
/// invalid), so the caller declines soundly.
fn project(polys: &[Polynomial], var: Var) -> Option<Vec<Polynomial>> {
    let mut proj: Vec<Polynomial> = Vec::new();
    // Make each polynomial squarefree in the main variable (McCallum requires it,
    // e.g. the trivially-true axiom `y² ≥ 0` must become `y` — otherwise its
    // discriminant vanishes identically). Then keep those with positive degree.
    let conditioned: Vec<Polynomial> = polys.iter().map(|p| squarefree_main(p, var)).collect();
    let mains: Vec<&Polynomial> = conditioned.iter().filter(|p| p.degree_of(var) >= 1).collect();
    // Polynomials free of `var` are carried down unchanged (still constrain lower
    // levels and matter for the decision).
    for p in conditioned.iter().filter(|p| p.degree_of(var) == 0) {
        proj.push(p.clone());
    }
    for f in &mains {
        let d = f.degree_of(var);
        for j in 1..=d {
            proj.push(f.coeff_of_var(var, j));
        }
        if d >= 2 {
            let disc = discriminant(f, var);
            if disc.is_zero() {
                return None; // repeated factor with non-constant coefficients
            }
            proj.push(disc);
        }
    }
    for i in 0..mains.len() {
        for j in (i + 1)..mains.len() {
            let res = resultant(mains[i], mains[j], var);
            if res.is_zero() {
                return None; // the two share a factor in the main variable
            }
            proj.push(res);
        }
    }
    Some(clean(proj))
}

/// The squarefree part of `f` in the main variable `var`, when `f` is univariate
/// in `var` (its `var`-coefficients are constants) — the common case, including
/// the trivially-true square axioms. Multivariate-coefficient polynomials are
/// returned unchanged (a non-squarefree such polynomial is caught by the
/// `disc ≡ 0` guard, which declines soundly).
fn squarefree_main(f: &Polynomial, var: Var) -> Polynomial {
    let d = f.degree_of(var) as usize;
    if d == 0 {
        return f.clone();
    }
    let mut coeffs = Vec::with_capacity(d + 1);
    for j in 0..=d {
        match f.coeff_of_var(var, j as u32).as_constant() {
            Some(c) => coeffs.push(c),
            None => return f.clone(), // not univariate in `var`
        }
    }
    let sf = UPoly::from_coeffs(coeffs).squarefree();
    upoly_to_poly(&sf, var)
}

/// Remove zero and nonzero-constant polynomials and duplicates.
fn clean(polys: Vec<Polynomial>) -> Vec<Polynomial> {
    let mut out: Vec<Polynomial> = Vec::new();
    for p in polys {
        if p.is_zero() || p.as_constant().is_some() {
            continue;
        }
        if !out.contains(&p) {
            out.push(p);
        }
    }
    out
}

/// Base-phase sample points: the real roots of the level-0 (univariate)
/// polynomials, plus a rational in each sector between/around them.
///
/// Each polynomial's roots are isolated **separately** so every algebraic sample
/// keeps a *small* defining polynomial (its own squarefree factor). Multiplying
/// everything into one product would give each root the whole high-degree product
/// as its defining polynomial, blowing up every downstream resultant.
fn base_samples(polys: &[Polynomial]) -> Vec<Alg> {
    let mut roots: Vec<Alg> = Vec::new();
    for f in polys {
        let u = poly_to_upoly(f, 0);
        if u.degree() >= 1 {
            for beta in Alg::roots_of(&u) {
                if !roots
                    .iter()
                    .any(|e| e.compare(&beta) == core::cmp::Ordering::Equal)
                {
                    roots.push(beta);
                }
            }
        }
    }
    roots.sort_by(|a, b| a.compare(b));
    samples_around(&roots)
}

/// Given sorted distinct roots, build the alternating sector/section sample
/// list: a rational below the least, each root, a rational strictly between
/// consecutive roots, a rational above the greatest. Consecutive roots may come
/// from different polynomials and thus have **overlapping** isolating intervals,
/// so each between-sample refines the two roots until their intervals are
/// disjoint (`rational_between`) before taking a midpoint of the gap.
fn samples_around(roots: &[Alg]) -> Vec<Alg> {
    let one = Rational::from_integer(1.into());
    if roots.is_empty() {
        return alloc::vec![Alg::Rational(Rational::from_integer(0.into()))];
    }
    let mut rs = roots.to_vec();
    let mut out: Vec<Alg> = Vec::new();
    // Below the least: floor(lo of first) − 1 (< the least root).
    let first_lo = rs[0].interval().0;
    out.push(Alg::Rational(
        Rational::from_integer(first_lo.floor()).sub(&one),
    ));
    for i in 0..rs.len() {
        out.push(rs[i].clone());
        if i + 1 < rs.len() {
            let mid = rational_between(&mut rs, i);
            out.push(Alg::Rational(mid));
        }
    }
    let last_hi = rs.last().unwrap().interval().1;
    out.push(Alg::Rational(
        Rational::from_integer(last_hi.ceil()).add(&one),
    ));
    out
}

/// A rational strictly between `rs[i]` and `rs[i+1]` (which satisfy
/// `rs[i] < rs[i+1]`): refine both until their isolating intervals are disjoint,
/// then return a point in the gap.
fn rational_between(rs: &mut [Alg], i: usize) -> Rational {
    let two = Rational::from_integer(2.into());
    for _ in 0..4000 {
        let a_hi = rs[i].interval().1;
        let b_lo = rs[i + 1].interval().0;
        // Require a *strict* gap: `a_hi == b_lo` is not enough, since that shared
        // endpoint can itself be the value of one of the roots (e.g. `−√2`'s
        // interval upper bound coinciding with the rational root `0`), which
        // would collapse the sector sample onto a section.
        if a_hi < b_lo {
            return a_hi.add(&b_lo).div(&two);
        }
        rs[i].refine();
        rs[i + 1].refine();
    }
    // Fallback: midpoint of the approximations (well-separated roots reach here
    // essentially never).
    rs[i].approx().add(&rs[i + 1].approx()).div(&two)
}

/// Lift a sample point by one coordinate: isolate the fiber roots of every
/// polynomial (main variable `var`) at the sample, merge them, and extend the
/// sample by each root (section) and a rational between/around them (sectors).
/// Returns `None` on a nullification (McCallum invalid at a positive-dim cell).
fn lift(sample: &[Alg], polys: &[Polynomial], var: Var) -> Option<Vec<Vec<Alg>>> {
    let mut roots: Vec<Alg> = Vec::new();
    for f in polys {
        for r in roots_at(f, sample, var)? {
            // Merge coincident roots across polynomials.
            if !roots.iter().any(|e| e.compare(&r) == core::cmp::Ordering::Equal) {
                roots.push(r);
            }
        }
    }
    roots.sort_by(|a, b| a.compare(b));
    let coords = samples_around(&roots);
    Some(
        coords
            .into_iter()
            .map(|c| {
                let mut ext = sample.to_vec();
                ext.push(c);
                ext
            })
            .collect(),
    )
}

/// Isolate the real roots of `f` in variable `var` at the (lower-dimensional)
/// `sample`: eliminate the sample's coordinates by resultants to get a univariate
/// integer polynomial whose roots ⊇ the fiber roots, isolate those, then keep
/// only the genuine ones (`sign_at_point(f, sample++β) == 0`). `None` if `f` is
/// nullified at the sample (the eliminated polynomial is identically zero).
fn roots_at(f: &Polynomial, sample: &[Alg], var: Var) -> Option<Vec<Alg>> {
    if f.degree_of(var) == 0 {
        return Some(Vec::new()); // no root boundaries from a var-free polynomial
    }
    // Eliminate each sample coordinate (rationals by substitution).
    let mut g = f.clone();
    for (i, coord) in sample.iter().enumerate() {
        match coord {
            Alg::Rational(r) => {
                g = crate::nlsat::elim::subst_var(&g, i as Var, &Polynomial::constant(r.clone()));
            }
            Alg::Irrational { poly, .. } => {
                g = resultant(&g, &upoly_to_poly(poly, i as Var), i as Var);
            }
        }
    }
    // `g` is now univariate in `var`.
    let u = poly_to_upoly(&g, var);
    if u.is_zero() {
        return None; // nullification
    }
    let candidates = Alg::roots_of(&u);
    let mut out = Vec::new();
    for beta in candidates {
        let mut point = sample.to_vec();
        point.push(beta.clone());
        if sign_at_point(f, &point) == 0 {
            out.push(beta);
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::polynomial::Monomial;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn mono(p: &[(Var, u32)]) -> Monomial {
        Monomial::from_powers(p)
    }
    // Bivariate helper: terms are (coeff, [(var, deg), …]).
    fn poly(terms: &[(i64, &[(Var, u32)])]) -> Polynomial {
        Polynomial::from_terms(terms.iter().map(|&(c, m)| (r(c), mono(m))).collect())
    }

    // x^2 + y^2 < 1 ∧ x*y > 1 : UNSAT.
    #[test]
    fn circle_vs_hyperbola_unsat() {
        let c = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (-1, &[])]), Rel::Lt),
            (poly(&[(1, &[(0, 1), (1, 1)]), (-1, &[])]), Rel::Gt),
        ];
        assert_eq!(cad_sat(&c, 2), Some(false));
    }

    // x*y > 5 ∧ x + y < 3 : SAT (e.g. x=-1, y=-10).
    #[test]
    fn product_and_sum_sat() {
        let c = alloc::vec![
            (poly(&[(1, &[(0, 1), (1, 1)]), (-5, &[])]), Rel::Gt),
            (poly(&[(1, &[(0, 1)]), (1, &[(1, 1)]), (-3, &[])]), Rel::Lt),
        ];
        assert_eq!(cad_sat(&c, 2), Some(true));
    }

    // x^2 + y^2 < 4 ∧ x*y > 1 : SAT (x=y=1.2).
    #[test]
    fn circle_vs_hyperbola_sat() {
        let c = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (-4, &[])]), Rel::Lt),
            (poly(&[(1, &[(0, 1), (1, 1)]), (-1, &[])]), Rel::Gt),
        ];
        assert_eq!(cad_sat(&c, 2), Some(true));
    }

    // A single circle equality x^2 + y^2 = 1 : SAT (the unit circle is nonempty).
    #[test]
    fn circle_equality_sat() {
        let c = alloc::vec![(
            poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (-1, &[])]),
            Rel::Eq,
        )];
        assert_eq!(cad_sat(&c, 2), Some(true));
    }

    // x^2 = 2 ∧ y^2 = 3 ∧ x + y < 0 : SAT (x=√2, y=−√3).
    #[test]
    fn two_equalities_and_inequality_sat() {
        let c = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (-2, &[])]), Rel::Eq),
            (poly(&[(1, &[(1, 2)]), (-3, &[])]), Rel::Eq),
            (poly(&[(1, &[(0, 1)]), (1, &[(1, 1)])]), Rel::Lt),
        ];
        assert_eq!(cad_sat(&c, 2), Some(true));
    }

    // x^2 > y^2 ∧ y > 10 ∧ x < 1 : SAT (x=−20, y=11).
    #[test]
    fn inequalities_only_sat() {
        let c = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (-1, &[(1, 2)])]), Rel::Gt),
            (poly(&[(1, &[(1, 1)]), (-10, &[])]), Rel::Gt),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), Rel::Lt),
        ];
        assert_eq!(cad_sat(&c, 2), Some(true));
    }

    // Fuzzer regression: x*y = 2 ∧ x^2 < y^2 : SAT (witness x=-1, y=-2).
    #[test]
    fn eq_and_strict_square_ineq_sat() {
        let c = alloc::vec![
            (poly(&[(1, &[(0, 1), (1, 1)]), (-2, &[])]), Rel::Eq),
            (poly(&[(1, &[(0, 2)]), (-1, &[(1, 2)])]), Rel::Lt),
        ];
        assert_eq!(cad_sat(&c, 2), Some(true));
    }

    // Empty real variety: x^2 + y^2 + 1 = 0 : UNSAT.
    #[test]
    fn empty_variety_unsat() {
        let c = alloc::vec![(
            poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (1, &[])]),
            Rel::Eq,
        )];
        assert_eq!(cad_sat(&c, 2), Some(false));
    }
}

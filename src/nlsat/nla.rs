//! Nonlinear arithmetic **saturation**: derive logical consequences of a
//! polynomial constraint system that are strong enough for a *linear* solver to
//! refute it, once every nonlinear monomial is abstracted as a fresh variable.
//!
//! This is the refutation half of z3's `nla_solver` (`smt/theory_lra` +
//! `math/lp/nla_*`): rather than deciding nonlinear arithmetic outright (CAD,
//! which only applies to the reals and blows up), add *valid* nonlinear lemmas
//! until linear arithmetic alone sees the contradiction. It is what lets the
//! unbounded **integer** systems that CAD and bounded interval propagation both
//! decline get refuted, e.g.
//!
//! - `0 ≤ x ∧ −1 ≤ y ∧ xy + x < 0` — the product `x·(y+1)` of two nonnegatives
//!   is nonnegative, contradicting `xy + x < 0`.
//! - `ab > 0 ∧ cd > 0 ∧ ac > 0 ∧ ¬(bd > 0)` — `(ab)(cd) = abcd > 0` while
//!   `(ac)(−bd) = −abcd ≥ 0`.
//! - `x₁²x₂ = 1 ∧ x₁x₂ = x₂ ∧ x₂ ≠ 1` — multiplying `x₁x₂ − x₂ = 0` by `x₁`
//!   yields `x₁²x₂ − x₁x₂ = 0`, so `x₂ = x₁x₂ = x₁²x₂ = 1`.
//!
//! **Soundness.** Every fact produced here is a logical consequence of the
//! input, and abstracting each monomial as an unconstrained fresh variable only
//! *weakens* the system (any model of the original induces one of the
//! abstraction). So `UNSAT` of the abstracted system implies `UNSAT` of the
//! original; a `SAT` of the abstraction means nothing and must not be trusted.

use alloc::vec::Vec;
use puremp::Rational;

use crate::math::polynomial::{Monomial, Polynomial};
use crate::nlsat::icp::{Constraint, Rel};

/// Highest total degree of a derived fact we keep. Degree 4 covers the pairwise
/// product of two quadratic hypotheses (`(ab)·(cd)`), which is what the
/// sign-propagation refutations need.
const MAX_DEGREE: u32 = 4;
/// Cap on the derived-fact count, so saturation stays linear-ish in practice.
const MAX_FACTS: usize = 512;

/// Is every exponent of `m` even (so `m` is a perfect square, hence `≥ 0`)?
fn is_even_monomial(m: &Monomial) -> bool {
    m.total_degree() >= 2 && m.vars().all(|v| m.degree_of(v).is_multiple_of(2))
}

fn one() -> Rational {
    Rational::from_integer(1.into())
}

/// The exact square root of a nonnegative rational, if it is a perfect square.
fn rational_sqrt(c: &Rational) -> Option<Rational> {
    if c.is_negative() {
        return None;
    }
    let n = c.numerator().sqrt_exact()?;
    let d = c.denominator().sqrt_exact()?;
    Some(Rational::new(n, d))
}

/// Halve every exponent of `m`; `None` unless all of them are even.
fn half_monomial(m: &Monomial) -> Option<Monomial> {
    let vs: Vec<_> = m.vars().collect();
    let mut pairs = Vec::with_capacity(vs.len());
    for v in vs {
        let e = m.degree_of(v);
        if !e.is_multiple_of(2) {
            return None;
        }
        pairs.push((v, e / 2));
    }
    Some(Monomial::from_powers(&pairs))
}

/// The exact square root of `p` as a polynomial, if `p` is a perfect square.
///
/// Builds `q` term-by-term from the leading term downwards (`q₀ = √lead(p)`, then
/// each next term is `lead(p − q²) / (2·lead(q))`, the classic long-division
/// square root) and then **verifies** `q² = p`. The verification is what makes
/// the answer trustworthy — the construction is only a search.
///
/// This is what recognises `x₁²x₃⁴ − 2x₁x₂x₃²x₄ + x₂²x₄² = (x₁x₃² − x₂x₄)²`, hence
/// nonnegative, refuting `that < x₅ < 0`.
pub fn poly_sqrt(p: &Polynomial) -> Option<Polynomial> {
    if p.is_zero() {
        return Some(Polynomial::zero());
    }
    let (c0, m0) = p.terms().first()?.clone();
    let r0 = rational_sqrt(&c0)?;
    let h0 = half_monomial(&m0)?;
    let mut q = Polynomial::from_terms(alloc::vec![(r0, h0)]);
    let two = Rational::from_integer(2.into());
    for _ in 0..64 {
        let rem = p.sub(&q.mul(&q));
        if rem.is_zero() {
            break;
        }
        let (rc, rm) = rem.terms().first()?.clone();
        let (qc, qm) = q.terms().first()?.clone();
        let tc = rc.div(&qc.mul(&two));
        let tm = rm.checked_div(&qm)?;
        let t = Polynomial::from_terms(alloc::vec![(tc, tm)]);
        if t.is_zero() {
            return None;
        }
        q = q.add(&t);
    }
    (q.mul(&q) == *p).then_some(q)
}

/// The degree-≥2 part of `p` (its nonlinear terms).
fn nonlinear_part(p: &Polynomial) -> Polynomial {
    Polynomial::from_terms(
        p.terms()
            .iter()
            .filter(|(_, m)| m.total_degree() >= 2)
            .cloned()
            .collect(),
    )
}

/// The input constraints plus derived consequences (see the module docs).
/// `nvars` is the number of polynomial variables (indices `0..nvars`).
pub fn saturate(cons: &[Constraint], nvars: u32) -> Vec<Constraint> {
    let mut out: Vec<Constraint> = cons.to_vec();

    // Normalise every inequality to "nonnegative form" `q ≥ 0` (or `q > 0` when
    // strict), and collect the equalities. Disequalities carry no sign info but
    // are kept in `out` — they are what many of these systems contradict.
    let mut nonneg: Vec<(Polynomial, bool)> = Vec::new();
    let mut eqs: Vec<Polynomial> = Vec::new();
    for c in cons {
        match c.rel {
            Rel::Ge => nonneg.push((c.poly.clone(), false)),
            Rel::Gt => nonneg.push((c.poly.clone(), true)),
            Rel::Le => nonneg.push((c.poly.neg(), false)),
            Rel::Lt => nonneg.push((c.poly.neg(), true)),
            Rel::Eq => eqs.push(c.poly.clone()),
            Rel::Ne => {}
        }
    }

    // The degree-≥2 monomials the *original* problem actually talks about. A
    // derived equality that mentions none of them cannot help refute it, and
    // multiplying every equality by every variable produces a great many such
    // dead ends — each adding a fresh abstraction variable that only makes the
    // linear system harder. Filtering on this keeps the abstraction small.
    let mut orig_monos: Vec<Monomial> = Vec::new();
    for c in cons {
        for (_, mono) in c.poly.terms() {
            if mono.total_degree() >= 2 && !orig_monos.contains(mono) {
                orig_monos.push(mono.clone());
            }
        }
    }
    let touches_orig = |p: &Polynomial| {
        p.terms()
            .iter()
            .any(|(_, m)| m.total_degree() >= 2 && orig_monos.contains(m))
    };

    // (1) Mutual bounds are an equality: `q ≥ 0 ∧ −q ≥ 0 ⇒ q = 0`. This is what
    // turns `x₄ ≤ x₅ ∧ x₅ ≤ x₄` into `x₄ = x₅`, which (3) can then multiply
    // through a nonlinear term. Once a pair is recognised, drop both halves from
    // `nonneg`: their pairwise products are the degenerate `±q² ≥ 0`, which teach
    // the linear solver nothing but do introduce fresh monomials.
    let mut paired: Vec<bool> = alloc::vec![false; nonneg.len()];
    for i in 0..nonneg.len() {
        for j in (i + 1)..nonneg.len() {
            if !nonneg[i].1
                && !nonneg[j].1
                && !nonneg[i].0.is_zero()
                && nonneg[i].0.add(&nonneg[j].0).is_zero()
            {
                let p = nonneg[i].0.clone();
                if !eqs.iter().any(|e| e.sub(&p).is_zero()) {
                    eqs.push(p.clone());
                    out.push(Constraint::new(p, Rel::Eq));
                }
                paired[i] = true;
                paired[j] = true;
            }
        }
    }
    let mut idx = 0;
    nonneg.retain(|_| {
        let keep = !paired[idx];
        idx += 1;
        keep
    });

    // (2) A monomial with all-even exponents is a square, hence nonnegative.
    // Feeding these into `nonneg` lets (4) multiply them by other hypotheses
    // (`x ≥ 1 ∧ z² ≥ 0 ⇒ (x−1)·z² ≥ 0`).
    let mut squares: Vec<Polynomial> = Vec::new();
    for c in cons {
        for (_, mono) in c.poly.terms() {
            if is_even_monomial(mono) {
                let p = Polynomial::from_terms(alloc::vec![(one(), mono.clone())]);
                if !squares.iter().any(|s| s.sub(&p).is_zero()) {
                    squares.push(p);
                }
            }
        }
    }
    for p in squares {
        nonneg.push((p.clone(), false));
        out.push(Constraint::new(p, Rel::Ge));
    }

    // (2b) A *perfect-square polynomial* is nonnegative. The interesting case is a
    // constraint whose nonlinear part is a square while its linear part is not,
    // e.g. `(x₁x₃² − x₂x₄)² < x₅ ∧ x₅ < 0`: recognising `SOS ≥ 0` makes the
    // abstracted system linearly contradictory. Monomial-wise squares (2) cannot
    // see this — the cross term `−2x₁x₂x₃²x₄` is unbounded on its own.
    let mut sos: Vec<Polynomial> = Vec::new();
    for c in cons {
        for cand in [c.poly.clone(), nonlinear_part(&c.poly)] {
            if cand.total_degree() >= 2
                && poly_sqrt(&cand).is_some()
                && !sos.iter().any(|s| s.sub(&cand).is_zero())
            {
                sos.push(cand);
            }
        }
    }
    for p in sos {
        nonneg.push((p.clone(), false));
        out.push(Constraint::new(p, Rel::Ge));
    }

    // (3) Multiply each equality by each variable: `p = 0 ⇒ p·v = 0`. This is the
    // Gröbner-flavoured step; it relates monomials the abstraction would
    // otherwise treat as independent (`y = 2z² ⇒ xy = 2xz²`).
    let base_eqs = eqs.clone();
    'eqs: for p in &base_eqs {
        for v in 0..nvars {
            let q = p.mul(&Polynomial::var(v));
            if !q.is_zero() && q.total_degree() <= MAX_DEGREE && touches_orig(&q) {
                out.push(Constraint::new(q, Rel::Eq));
            }
            if out.len() >= MAX_FACTS {
                break 'eqs;
            }
        }
    }

    // (4) Products of sign facts: `q₁ ≥ 0 ∧ q₂ ≥ 0 ⇒ q₁·q₂ ≥ 0` (strict when both
    // are). Includes `i == j`, i.e. squares of hypotheses.
    for i in 0..nonneg.len() {
        for j in i..nonneg.len() {
            let q = nonneg[i].0.mul(&nonneg[j].0);
            if !q.is_zero() && q.total_degree() <= MAX_DEGREE {
                let strict = nonneg[i].1 && nonneg[j].1;
                out.push(Constraint::new(q, if strict { Rel::Gt } else { Rel::Ge }));
            }
            if out.len() >= MAX_FACTS {
                return out;
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::polynomial::Polynomial as P;

    fn v(i: u32) -> P {
        P::var(i)
    }
    fn c(i: i64) -> P {
        P::constant(Rational::from_integer(i.into()))
    }

    /// `0 ≤ x ∧ −1 ≤ y ⇒ x·(y+1) = xy + x ≥ 0` must appear among the derived facts.
    #[test]
    fn derives_product_of_nonnegatives() {
        // x ≥ 0 ; y + 1 ≥ 0
        let cons = [
            Constraint::new(v(0), Rel::Ge),
            Constraint::new(v(1).add(&c(1)), Rel::Ge),
        ];
        let sat = saturate(&cons, 2);
        // xy + x ≥ 0
        let want = v(0).mul(&v(1)).add(&v(0));
        assert!(
            sat.iter()
                .any(|c| c.rel == Rel::Ge && c.poly.sub(&want).is_zero()),
            "expected xy + x >= 0 among {} facts",
            sat.len()
        );
    }

    /// `x₄ ≤ x₅ ∧ x₅ ≤ x₄` must yield the equality `x₄ − x₅ = 0`.
    #[test]
    fn mutual_bounds_give_equality() {
        // x0 - x1 <= 0 ; x1 - x0 <= 0
        let cons = [
            Constraint::new(v(0).sub(&v(1)), Rel::Le),
            Constraint::new(v(1).sub(&v(0)), Rel::Le),
        ];
        let sat = saturate(&cons, 2);
        let d = v(0).sub(&v(1));
        assert!(
            sat.iter()
                .any(|c| c.rel == Rel::Eq && (c.poly.sub(&d).is_zero() || c.poly.add(&d).is_zero()))
        );
    }

    /// `p = 0 ⇒ p·v = 0`: from `x₁x₂ − x₂ = 0`, multiplying by `x₁` gives
    /// `x₁²x₂ − x₁x₂ = 0`.
    #[test]
    fn multiplies_equality_by_variable() {
        let p = v(0).mul(&v(1)).sub(&v(1)); // x0*x1 - x1 = 0
        let sat = saturate(&[Constraint::new(p, Rel::Eq)], 2);
        let want = v(0).mul(&v(0)).mul(&v(1)).sub(&v(0).mul(&v(1))); // x0^2 x1 - x0 x1
        assert!(
            sat.iter()
                .any(|c| c.rel == Rel::Eq && c.poly.sub(&want).is_zero())
        );
    }

    /// `(x₁x₃² − x₂x₄)²` is recognised as a perfect square, and a non-square is not.
    #[test]
    fn perfect_square_is_detected() {
        // q = x0*x2^2 - x1*x3
        let q = v(0).mul(&v(2)).mul(&v(2)).sub(&v(1).mul(&v(3)));
        let p = q.mul(&q);
        let root = poly_sqrt(&p).expect("should be a perfect square");
        assert!(root.mul(&root).sub(&p).is_zero());
        // not a square: q^2 + 1
        assert!(poly_sqrt(&p.add(&c(1))).is_none());
        // not a square: an odd-degree leading term
        assert!(poly_sqrt(&v(0).mul(&v(0)).mul(&v(1))).is_none());
    }

    /// The nonlinear part of `SOS − x₅` is a square, so `SOS ≥ 0` is derived.
    #[test]
    fn derives_sum_of_squares_nonneg() {
        let q = v(0).mul(&v(2)).mul(&v(2)).sub(&v(1).mul(&v(3)));
        let sos = q.mul(&q);
        // SOS - x4 < 0
        let cons = [Constraint::new(sos.sub(&v(4)), Rel::Lt)];
        let sat = saturate(&cons, 5);
        assert!(
            sat.iter()
                .any(|c| c.rel == Rel::Ge && c.poly.sub(&sos).is_zero()),
            "expected SOS >= 0"
        );
    }

    /// An even-exponent monomial is recognised as nonnegative (`z² ≥ 0`).
    #[test]
    fn square_monomial_is_nonnegative() {
        let p = v(0).mul(&v(0)).sub(&v(1)); // z^2 - y = 0
        let sat = saturate(&[Constraint::new(p, Rel::Eq)], 2);
        let sq = v(0).mul(&v(0));
        assert!(
            sat.iter()
                .any(|c| c.rel == Rel::Ge && c.poly.sub(&sq).is_zero())
        );
    }
}

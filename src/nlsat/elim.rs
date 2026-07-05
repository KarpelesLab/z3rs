//! Linear-variable elimination — the equality-projection preprocessing step of
//! Z3's `nlsat` (`z3/src/nlsat`, Z3 4.17.0, MIT).
//!
//! When an equality constraint contains a variable that occurs *linearly* with a
//! constant coefficient (`c·v + q = 0`, `q` free of `v`), that variable is
//! determined — `v = −q/c` — and can be substituted into every other constraint,
//! removing it from the system. Iterating this reduces many multivariate
//! nonlinear problems to a single variable (then decided exactly by the
//! univariate procedure) or to a small integer box, all while staying
//! equisatisfiable (each elimination is an exact, sound rewrite).
//!
//! This is *Gaussian elimination generalised to nonlinear systems*: the
//! eliminated variable may appear nonlinearly elsewhere (e.g. `x·v`), and the
//! substitution composes polynomials, so `x·y = 6 ∧ x + y = 5` becomes
//! `x·(5 − x) = 6`.

use alloc::vec::Vec;

use puremp::Rational;

use crate::math::polynomial::{Monomial, Polynomial, Var};
use crate::nlsat::icp::Rel;

/// Substitute the polynomial `repl` for variable `v` throughout `poly`
/// (polynomial composition): each `v^k` factor becomes `repl^k`.
pub fn subst_var(poly: &Polynomial, v: Var, repl: &Polynomial) -> Polynomial {
    let mut result = Polynomial::zero();
    for (coeff, mono) in poly.terms() {
        let k = mono.degree_of(v);
        // The monomial with `v` removed.
        let rest_powers: Vec<(Var, u32)> = mono
            .vars()
            .filter(|&x| x != v)
            .map(|x| (x, mono.degree_of(x)))
            .collect();
        let rest = Polynomial::from_terms(alloc::vec![(
            coeff.clone(),
            Monomial::from_powers(&rest_powers)
        )]);
        let term = if k == 0 { rest } else { rest.mul(&repl.pow(k)) };
        result = result.add(&term);
    }
    result
}

/// If `p = c·v + q` with `c` a nonzero **constant** and `q` free of `v`, return
/// the solved value `v = −q/c` and the coefficient `c`; otherwise `None` (v is
/// nonlinear in `p`, or its coefficient is not constant).
fn solve_linear_for(p: &Polynomial, v: Var) -> Option<(Polynomial, Rational)> {
    if p.degree_of(v) != 1 {
        return None;
    }
    let mut coeff_v = Rational::from_integer(0.into());
    let mut rest = Polynomial::zero();
    for (coeff, mono) in p.terms() {
        match mono.degree_of(v) {
            0 => {
                rest = rest.add(&Polynomial::from_terms(alloc::vec![(
                    coeff.clone(),
                    mono.clone()
                )]));
            }
            1 if mono.total_degree() == 1 => {
                // The term is exactly `coeff · v`.
                coeff_v = coeff_v.add(coeff);
            }
            // `v` multiplied by another variable / higher power ⇒ not constant coeff.
            _ => return None,
        }
    }
    if coeff_v.is_zero() {
        return None;
    }
    // v = -rest / coeff_v.
    Some((rest.neg().scale(&coeff_v.recip()), coeff_v))
}

/// Repeatedly eliminate linearly-occurring variables from equalities. Returns the
/// reduced (equisatisfiable) constraint set. Eliminated equalities are dropped
/// (they become `0 = 0`).
///
/// `can_eliminate(v, c)` decides whether variable `v` (with the solved
/// coefficient `c`) may be eliminated. The caller encodes the soundness rule:
/// a **real** variable is always safe (`v = −q/c` is real); an **integer**
/// variable is safe only in a pure-integer system with a unit coefficient, so
/// `v = ∓q` stays integer-valued.
pub fn eliminate_linear(
    mut constraints: Vec<(Polynomial, Rel)>,
    can_eliminate: impl Fn(Var, &Rational) -> bool,
) -> Vec<(Polynomial, Rel)> {
    let mut guard = 0;
    loop {
        guard += 1;
        if guard > 64 {
            break;
        }
        let mut chosen: Option<(usize, Var, Polynomial)> = None;
        'outer: for (i, (p, rel)) in constraints.iter().enumerate() {
            if *rel != Rel::Eq {
                continue;
            }
            for v in p.vars() {
                if let Some((repl, c)) = solve_linear_for(p, v) {
                    if !can_eliminate(v, &c) {
                        continue;
                    }
                    chosen = Some((i, v, repl));
                    break 'outer;
                }
            }
        }
        let Some((i, v, repl)) = chosen else { break };
        constraints.remove(i);
        for (p, _) in constraints.iter_mut() {
            if p.degree_of(v) > 0 {
                *p = subst_var(p, v, &repl);
            }
        }
    }
    constraints
}

/// Remap the variables actually used in `constraints` to a contiguous
/// `0..k` range. Returns the rewritten constraints and, for each new index, the
/// original variable it corresponds to (so callers can recover per-variable
/// metadata such as its sort).
pub fn remap_vars(constraints: &[(Polynomial, Rel)]) -> (Vec<(Polynomial, Rel)>, Vec<Var>) {
    let mut used: Vec<Var> = constraints.iter().flat_map(|(p, _)| p.vars()).collect();
    used.sort_unstable();
    used.dedup();
    let index_of = |v: Var| used.iter().position(|&u| u == v).unwrap() as Var;
    let rewritten = constraints
        .iter()
        .map(|(p, rel)| {
            let terms = p
                .terms()
                .iter()
                .map(|(c, m)| {
                    let powers: Vec<(Var, u32)> =
                        m.vars().map(|v| (index_of(v), m.degree_of(v))).collect();
                    (c.clone(), Monomial::from_powers(&powers))
                })
                .collect();
            (Polynomial::from_terms(terms), *rel)
        })
        .collect();
    (rewritten, used)
}

/// Try to prove a multivariate system **satisfiable** by fixing all but one
/// variable to candidate rational (for reals) / integer (for ints) values and
/// deciding the last variable univariately. A success is a *verified* witness
/// (the fixed values plus the univariate solution satisfy every constraint), so
/// this is sound; it is incomplete (only a finite candidate grid is tried), so a
/// `false` means "not proven sat here", never "unsat".
///
/// `is_int[i]` gives the sort of variable `i` (indices `0..k`). Only small
/// systems (`k ≤ 4`) with a bounded candidate product are attempted.
pub fn sat_by_fixing(constraints: &[(Polynomial, Rel)], is_int: &[bool]) -> bool {
    let k = is_int.len();
    if !(2..=4).contains(&k) {
        return false;
    }
    let free = (k - 1) as Var;
    let fixed: Vec<Var> = (0..free).collect();

    let candidates = |int: bool| -> Vec<Rational> {
        let mut v: Vec<Rational> = (-8..=8).map(|n| Rational::from_integer(n.into())).collect();
        if !int {
            for h in [-5i64, -3, -1, 1, 3, 5] {
                v.push(Rational::new(h.into(), 2.into()));
            }
        }
        v
    };
    let cands: Vec<Vec<Rational>> = fixed
        .iter()
        .map(|&fv| candidates(is_int[fv as usize]))
        .collect();
    let total: u128 = cands.iter().map(|c| c.len() as u128).product();
    if total > 30_000 {
        return false;
    }

    let mut idx = alloc::vec![0usize; fixed.len()];
    loop {
        // Substitute each fixed variable with its current candidate value.
        let mut cons = constraints.to_vec();
        for (fi, &fv) in fixed.iter().enumerate() {
            let val = Polynomial::constant(cands[fi][idx[fi]].clone());
            for (p, _) in cons.iter_mut() {
                if p.degree_of(fv) > 0 {
                    *p = subst_var(p, fv, &val);
                }
            }
        }
        // The residual is univariate in the free variable (or constant).
        let (reduced, _vars) = remap_vars(&cons);
        let dec = if is_int[free as usize] {
            crate::nlsat::univariate::decide_int(&reduced, 0)
        } else {
            crate::nlsat::univariate::decide(&reduced, 0)
        };
        if dec == Some(true) {
            return true;
        }
        // Advance the odometer over the fixed-variable candidate grid.
        let mut i = 0;
        loop {
            if i == fixed.len() {
                return false;
            }
            idx[i] += 1;
            if idx[i] < cands[i].len() {
                break;
            }
            idx[i] = 0;
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn mono(pairs: &[(Var, u32)]) -> Monomial {
        Monomial::from_powers(pairs)
    }

    // Substitute y := 5 - x into x*y: gives x*(5-x) = 5x - x^2.
    #[test]
    fn subst_composes_polynomials() {
        // x*y  (vars 0=x, 1=y)
        let xy = Polynomial::from_terms(alloc::vec![(r(1), mono(&[(0, 1), (1, 1)]))]);
        // repl for y = 5 - x
        let repl = Polynomial::from_terms(alloc::vec![
            (r(5), Monomial::one()),
            (r(-1), mono(&[(0, 1)])),
        ]);
        let out = subst_var(&xy, 1, &repl);
        // expect 5x - x^2
        let expect = Polynomial::from_terms(alloc::vec![
            (r(5), mono(&[(0, 1)])),
            (r(-1), mono(&[(0, 2)])),
        ]);
        assert_eq!(out, expect);
    }

    // Eliminate y from {x*y - 6 = 0, x + y - 5 = 0}: the second gives y = 5 - x,
    // reducing the first to x*(5-x) - 6 = -x^2 + 5x - 6 = 0.
    #[test]
    fn eliminate_reduces_to_univariate() {
        let c = alloc::vec![
            (
                Polynomial::from_terms(alloc::vec![
                    (r(1), mono(&[(0, 1), (1, 1)])),
                    (r(-6), Monomial::one()),
                ]),
                Rel::Eq,
            ),
            (
                Polynomial::from_terms(alloc::vec![
                    (r(1), mono(&[(0, 1)])),
                    (r(1), mono(&[(1, 1)])),
                    (r(-5), Monomial::one()),
                ]),
                Rel::Eq,
            ),
        ];
        let out = eliminate_linear(c, |_, _| true);
        // One constraint left, univariate in x.
        assert_eq!(out.len(), 1);
        let (reduced, vars) = remap_vars(&out);
        assert_eq!(vars.len(), 1); // only x remains
        // reduced[0] is a univariate quadratic; decide it as sat (roots x=2,3).
        assert_eq!(crate::nlsat::univariate::decide(&reduced, 0), Some(true));
    }

    // A variable multiplied by another (x*v) is NOT linearly solvable.
    #[test]
    fn nonlinear_coefficient_not_eliminated() {
        // p = x*v + 1 (v=1); v's coefficient is x, not constant.
        let p = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(0, 1), (1, 1)])),
            (r(1), Monomial::one()),
        ]);
        assert!(solve_linear_for(&p, 1).is_none());
    }

    // x^2 + y = 5 ∧ y > 0  ⇒ eliminate y = 5 - x^2, leaving 5 - x^2 > 0 ⇒ sat.
    #[test]
    fn eliminate_into_inequality() {
        let c = alloc::vec![
            (
                Polynomial::from_terms(alloc::vec![
                    (r(1), mono(&[(0, 2)])),
                    (r(1), mono(&[(1, 1)])),
                    (r(-5), Monomial::one()),
                ]),
                Rel::Eq,
            ),
            (
                Polynomial::from_terms(alloc::vec![(r(1), mono(&[(1, 1)]))]),
                Rel::Gt
            ),
        ];
        let out = eliminate_linear(c, |_, _| true);
        let (reduced, vars) = remap_vars(&out);
        assert_eq!(vars.len(), 1);
        assert_eq!(crate::nlsat::univariate::decide(&reduced, 0), Some(true));
    }
}

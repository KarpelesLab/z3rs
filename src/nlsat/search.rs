//! Model-constructing search for the satisfiability of a conjunction of
//! polynomial constraints over the reals (QF_NRA), in the spirit of the
//! Jovanović–de Moura **nlsat** procedure (`z3/src/nlsat`, Z3 4.17.0, MIT).
//!
//! Where [`cad`](crate::nlsat::cad) builds the *entire* cylindrical algebraic
//! decomposition up front (projecting every polynomial at every level and then
//! materialising the full Cartesian product of cells before checking any
//! constraint), this module walks the same decomposition **depth-first while
//! constructing a model incrementally**: it assigns `x₀, x₁, …` one at a time,
//! keeps a trail of real-algebraic sample values, prunes a branch the instant a
//! fully-determined constraint is violated, and stops at the first verified
//! witness. This is the model-guided half of nlsat: the same sound projection
//! underlies the cells (so an exhaustive search is a sound `unsat`), but the
//! search itself is guided by the partial model, which lets it decide many
//! instances without ever expanding the full decomposition.
//!
//! # Soundness (unconditional)
//!
//! * A returned [`NlResult::Sat`] carries a witness whose every original atom is
//!   re-verified **exactly** with [`sign_at_point`] before the answer is given.
//!   The sign engine only ever certifies a sign it can prove, so a wrong `Sat`
//!   is impossible.
//! * A returned [`NlResult::Unsat`] means the search exhausted a *complete*
//!   cover of sign-invariant cells (the projection is Collins' complete operator,
//!   reused verbatim from [`cad`](crate::nlsat::cad)) and no cell satisfied every
//!   atom. Pruned sub-trees are excluded only because a constraint over
//!   *already-assigned* variables is violated at the exact sample point — a
//!   point evaluation that holds for every extension of that sub-tree — so
//!   nothing satisfiable is ever discarded.
//! * Any inexactness anywhere — a `None` from projection, root isolation, cell
//!   lifting, or [`sign_at_point`] — or any resource cap being hit collapses the
//!   relevant branch to [`NlResult::Unknown`]. The procedure never guesses past
//!   a value it cannot certify, and never reports `Unsat` for a search that was
//!   cut short.
//!
//! It follows that `Unsat` is reported only for a genuinely complete, exact
//! refutation and `Sat` only for a genuinely verified witness; every other
//! outcome is the sound `Unknown` decline.

use alloc::vec::Vec;

use puremp::Rational;

use crate::math::polynomial::{Polynomial, Var};
use crate::nlsat::cad::{base_samples, clean, lift, project};
use crate::nlsat::icp::Rel;
use crate::nlsat::realclosure::{Alg, sign_at_point};

// Resource caps. Beyond these the search declines to a sound `Unknown` rather
// than risk a doubly-exponential blow-up. The projection cost is identical to
// `cad`, so the variable/degree caps mirror it; the depth-first search holds
// only a single branch in memory (not the full cell product), so the node
// budget can be far larger than `cad`'s materialised-cell cap.
const MAX_VARS: usize = 5;
const MAX_DEG: u32 = 12;
const MAX_PROJ: usize = 800;
const NODE_BUDGET: usize = 400_000;

/// The result of a nonlinear-arithmetic decision.
#[derive(Clone, Debug)]
pub enum NlResult {
    /// Satisfiable, with a witness assignment `witness[i]` for variable `xᵢ`
    /// (length `vars`). Every original atom holds exactly at this point.
    Sat(Vec<Alg>),
    /// Unsatisfiable over ℝ: no assignment satisfies the conjunction.
    Unsat,
    /// Declined — a resource cap was hit or an exact certification failed. This
    /// is always a sound fallback; it never hides a definite `Sat`/`Unsat`.
    Unknown,
}

/// Does sign `σ ∈ {−1, 0, +1}` satisfy `⋈ 0`?
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

/// Decide the satisfiability over ℝ of `⋀ᵢ atoms[i]` in the variables
/// `x₀ … x_{vars−1}` (all real).
///
/// Each atom is a polynomial constraint `poly ⋈ 0`. Returns [`NlResult::Sat`]
/// with a verified witness, [`NlResult::Unsat`], or [`NlResult::Unknown`]
/// (a sound decline). See the module docs for the soundness contract.
pub fn nlsat_decide(vars: usize, atoms: &[(Polynomial, Rel)]) -> NlResult {
    // No constraints: any point works (the origin is as good as any).
    if atoms.is_empty() {
        return NlResult::Sat(zeros(vars));
    }

    // Every atom must live in the declared variable range; a stray higher index
    // is a malformed input we decline on rather than mis-index the projection.
    for (p, _) in atoms {
        if p.vars().iter().any(|&v| v as usize >= vars) {
            return NlResult::Unknown;
        }
        if p.total_degree() > MAX_DEG {
            return NlResult::Unknown;
        }
    }

    let n = vars;
    if n > MAX_VARS {
        return NlResult::Unknown;
    }

    // Precompute each atom's highest variable index (None for a constant atom).
    let maxvar: Vec<Option<usize>> = atoms
        .iter()
        .map(|(p, _)| p.vars().last().map(|&v| v as usize))
        .collect();

    // Projection: `levels[k]` is the (Collins-complete) polynomial set whose main
    // variable is `k`, exactly as `cad` builds it. This is what makes an
    // exhaustive search a *sound* `unsat`: the cells it induces are
    // sign-invariant for the whole system.
    let levels = match build_levels(atoms, n) {
        Some(l) => l,
        None => return NlResult::Unknown,
    };

    let ctx = Ctx {
        levels: &levels,
        atoms,
        maxvar: &maxvar,
        n,
    };
    let mut budget = NODE_BUDGET;
    match dfs(&ctx, 0, &mut Vec::new(), &mut budget) {
        Outcome::Found(w) => NlResult::Sat(w),
        Outcome::Exhausted => NlResult::Unsat,
        Outcome::Declined => NlResult::Unknown,
    }
}

/// A witness of all-zero rationals of the given length.
fn zeros(vars: usize) -> Vec<Alg> {
    (0..vars)
        .map(|_| Alg::rational(Rational::from_integer(0.into())))
        .collect()
}

/// Build the per-level projected polynomial sets (`levels[k]` has main variable
/// `k`). `None` on a projection cap or an inexact projection determinant — both
/// sound declines. For `n == 0` there are no levels.
fn build_levels(atoms: &[(Polynomial, Rel)], n: usize) -> Option<Vec<Vec<Polynomial>>> {
    let mut levels: Vec<Vec<Polynomial>> = alloc::vec![Vec::new(); n];
    if n == 0 {
        return Some(levels);
    }
    // Top level holds every (non-constant) atom polynomial; polynomials not
    // involving the top variable are carried down unchanged by `project`.
    levels[n - 1] = clean(
        atoms
            .iter()
            .map(|(p, _)| p.clone())
            .filter(|p| !p.is_zero() && p.as_constant().is_none())
            .collect(),
    );
    for main in (1..n).rev() {
        let proj = project(&levels[main], main as Var)?;
        if proj.len() > MAX_PROJ {
            return None;
        }
        levels[main - 1] = proj;
    }
    Some(levels)
}

/// Read-only search context threaded through the recursion.
struct Ctx<'a> {
    levels: &'a [Vec<Polynomial>],
    atoms: &'a [(Polynomial, Rel)],
    maxvar: &'a [Option<usize>],
    n: usize,
}

/// The outcome of exploring a sub-tree.
enum Outcome {
    /// A verified satisfying witness (search short-circuits and returns it).
    Found(Vec<Alg>),
    /// The sub-tree was fully explored and contained no witness.
    Exhausted,
    /// The sub-tree could not be fully/exactly explored (a cap or an inexact
    /// certification). Combined upward: an `Unsat` conclusion requires *no*
    /// `Declined` anywhere below it.
    Declined,
}

/// Depth-first, model-constructing search. `sample` holds the exact algebraic
/// values already assigned to `x₀ … x_{depth−1}` (a single point, not a cell).
fn dfs(ctx: &Ctx<'_>, depth: usize, sample: &mut Vec<Alg>, budget: &mut usize) -> Outcome {
    if *budget == 0 {
        return Outcome::Declined;
    }
    *budget -= 1;

    // Leaf: every variable is assigned. Re-verify EVERY original atom exactly
    // before declaring a witness (the module's non-negotiable Sat gate).
    if depth == ctx.n {
        for (p, rel) in ctx.atoms {
            match sign_at_point(p, sample) {
                None => return Outcome::Declined,
                Some(s) => {
                    if !rel_holds(s, *rel) {
                        return Outcome::Exhausted;
                    }
                }
            }
        }
        return Outcome::Found(sample.clone());
    }

    // Prune on any atom that has *just* become fully determined at this depth
    // (its highest variable is `depth − 1`, or it is a constant checked at the
    // root). Its sign is fixed by the current point and unaffected by the
    // not-yet-assigned variables, so a violation here rules out the whole
    // sub-tree soundly. Atoms determined at shallower depths were already
    // checked by an ancestor.
    for (i, (p, rel)) in ctx.atoms.iter().enumerate() {
        let ready = match ctx.maxvar[i] {
            None => depth == 0,
            Some(mv) => mv + 1 == depth,
        };
        if ready {
            match sign_at_point(p, sample) {
                None => return Outcome::Declined,
                Some(s) => {
                    if !rel_holds(s, *rel) {
                        return Outcome::Exhausted;
                    }
                }
            }
        }
    }

    // Expand variable `x_depth`: enumerate one representative per sign-invariant
    // cell. At the base it is the 1-D decomposition of the level-0 polynomials;
    // above it is the CAD lift of the current point by the level-`depth` set.
    let children = if depth == 0 {
        base_samples(&ctx.levels[0])
            .into_iter()
            .map(|a| alloc::vec![a])
            .collect::<Vec<_>>()
    } else {
        match lift(sample, &ctx.levels[depth], depth as Var) {
            Some(c) => c,
            None => return Outcome::Declined,
        }
    };
    if children.len() > NODE_BUDGET {
        return Outcome::Declined;
    }

    let mut declined = false;
    for child in children {
        // `lift`/`base_samples` return the full extended point; adopt its last
        // coordinate onto our trail, recurse, then backtrack.
        debug_assert_eq!(child.len(), depth + 1);
        sample.push(child[depth].clone());
        let out = dfs(ctx, depth + 1, sample, budget);
        sample.pop();
        match out {
            Outcome::Found(w) => return Outcome::Found(w),
            Outcome::Exhausted => {}
            Outcome::Declined => declined = true,
        }
    }
    // A definite `unsat` for this sub-tree requires that every cell was explored
    // exactly; any decline below makes the sub-tree itself a decline.
    if declined {
        Outcome::Declined
    } else {
        Outcome::Exhausted
    }
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
    /// Build a polynomial from `(coeff, [(var, deg), …])` terms.
    fn poly(terms: &[(i64, &[(Var, u32)])]) -> Polynomial {
        Polynomial::from_terms(terms.iter().map(|&(c, m)| (r(c), mono(m))).collect())
    }

    /// Assert `res` is `Sat` and its witness exactly satisfies every atom.
    fn assert_sat(res: NlResult, atoms: &[(Polynomial, Rel)]) -> Vec<Alg> {
        match res {
            NlResult::Sat(w) => {
                for (p, rel) in atoms {
                    let s = sign_at_point(p, &w).expect("witness sign must be exactly certifiable");
                    assert!(
                        rel_holds(s, *rel),
                        "witness {w:?} violates atom {p:?} {rel:?} (sign {s})"
                    );
                }
                w
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    fn assert_unsat(res: NlResult) {
        assert!(
            matches!(res, NlResult::Unsat),
            "expected Unsat, got {res:?}"
        );
    }

    fn assert_unknown(res: NlResult) {
        assert!(
            matches!(res, NlResult::Unknown),
            "expected Unknown, got {res:?}"
        );
    }

    // ---- Univariate ------------------------------------------------------

    // x^2 = 2 : SAT, witness ±√2.
    #[test]
    fn x2_eq_2_sat() {
        let atoms = alloc::vec![(poly(&[(1, &[(0, 2)]), (-2, &[])]), Rel::Eq)];
        let w = assert_sat(nlsat_decide(1, &atoms), &atoms);
        // The witness squared is 2: x^2 - 2 vanishes there.
        assert_eq!(
            sign_at_point(&poly(&[(1, &[(0, 2)]), (-2, &[])]), &w),
            Some(0)
        );
    }

    // x^2 = -1 : UNSAT over ℝ.
    #[test]
    fn x2_eq_neg1_unsat() {
        let atoms = alloc::vec![(poly(&[(1, &[(0, 2)]), (1, &[])]), Rel::Eq)];
        assert_unsat(nlsat_decide(1, &atoms));
    }

    // x^2 < 0 : UNSAT over ℝ.
    #[test]
    fn x2_lt_0_unsat() {
        let atoms = alloc::vec![(poly(&[(1, &[(0, 2)])]), Rel::Lt)];
        assert_unsat(nlsat_decide(1, &atoms));
    }

    // x > 0 ∧ x < 1 : SAT, witness in the open interval (0, 1).
    #[test]
    fn x_between_0_and_1_sat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 1)])]), Rel::Gt),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), Rel::Lt),
        ];
        assert_sat(nlsat_decide(1, &atoms), &atoms);
    }

    // x >= 5 ∧ x <= 3 : UNSAT (contradictory linear bounds).
    #[test]
    fn contradictory_linear_unsat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 1)]), (-5, &[])]), Rel::Ge),
            (poly(&[(1, &[(0, 1)]), (-3, &[])]), Rel::Le),
        ];
        assert_unsat(nlsat_decide(1, &atoms));
    }

    // x^3 - x = 0 ∧ x > 0 ∧ x < 1 : UNSAT (roots {-1,0,1}, none in (0,1)).
    #[test]
    fn cubic_no_root_in_gap_unsat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 3)]), (-1, &[(0, 1)])]), Rel::Eq),
            (poly(&[(1, &[(0, 1)])]), Rel::Gt),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), Rel::Lt),
        ];
        assert_unsat(nlsat_decide(1, &atoms));
    }

    // ---- Two variables ---------------------------------------------------

    // x^2 + y^2 = 1 ∧ x = 0 : SAT, witness y = ±1.
    #[test]
    fn circle_and_axis_sat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (-1, &[])]), Rel::Eq),
            (poly(&[(1, &[(0, 1)])]), Rel::Eq),
        ];
        let w = assert_sat(nlsat_decide(2, &atoms), &atoms);
        // x is exactly 0; y is exactly ±1.
        assert_eq!(sign_at_point(&poly(&[(1, &[(0, 1)])]), &w), Some(0));
        assert_eq!(
            sign_at_point(&poly(&[(1, &[(1, 2)]), (-1, &[])]), &w),
            Some(0)
        );
    }

    // x^2 + y^2 < 0 : UNSAT over ℝ.
    #[test]
    fn sum_of_squares_lt_0_unsat() {
        let atoms = alloc::vec![(poly(&[(1, &[(0, 2)]), (1, &[(1, 2)])]), Rel::Lt)];
        assert_unsat(nlsat_decide(2, &atoms));
    }

    // x*y = 1 ∧ x = 0 : UNSAT (x = 0 forces 0 = 1).
    #[test]
    fn hyperbola_and_zero_axis_unsat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 1), (1, 1)]), (-1, &[])]), Rel::Eq),
            (poly(&[(1, &[(0, 1)])]), Rel::Eq),
        ];
        assert_unsat(nlsat_decide(2, &atoms));
    }

    // y = x^2 ∧ y < 0 : UNSAT over ℝ (a square is never negative).
    #[test]
    fn parabola_below_axis_unsat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(1, 1)]), (-1, &[(0, 2)])]), Rel::Eq), // y - x^2 = 0
            (poly(&[(1, &[(1, 1)])]), Rel::Lt),                  // y < 0
        ];
        assert_unsat(nlsat_decide(2, &atoms));
    }

    // x^2 = 2 ∧ y^2 = 3 ∧ x*y > 0 : SAT (x=√2,y=√3 or x=−√2,y=−√3).
    #[test]
    fn irrational_product_sat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (-2, &[])]), Rel::Eq),
            (poly(&[(1, &[(1, 2)]), (-3, &[])]), Rel::Eq),
            (poly(&[(1, &[(0, 1), (1, 1)])]), Rel::Gt),
        ];
        assert_sat(nlsat_decide(2, &atoms), &atoms);
    }

    // A satisfiable hyperbola-inside-a-disc: x^2 + y^2 < 4 ∧ x*y > 1 : SAT.
    #[test]
    fn disc_and_hyperbola_sat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (-4, &[])]), Rel::Lt),
            (poly(&[(1, &[(0, 1), (1, 1)]), (-1, &[])]), Rel::Gt),
        ];
        assert_sat(nlsat_decide(2, &atoms), &atoms);
    }

    // The tighter disc x^2 + y^2 < 1 ∧ x*y > 1 : UNSAT.
    #[test]
    fn disc_and_hyperbola_unsat() {
        let atoms = alloc::vec![
            (poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (-1, &[])]), Rel::Lt),
            (poly(&[(1, &[(0, 1), (1, 1)]), (-1, &[])]), Rel::Gt),
        ];
        assert_unsat(nlsat_decide(2, &atoms));
    }

    // ---- Three variables -------------------------------------------------

    // x^2 + y^2 + z^2 < 1 : SAT (the origin lies inside the unit ball).
    #[test]
    fn unit_ball_interior_sat() {
        let atoms = alloc::vec![(
            poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (1, &[(2, 2)]), (-1, &[]),]),
            Rel::Lt,
        )];
        assert_sat(nlsat_decide(3, &atoms), &atoms);
    }

    // x^2 + y^2 + z^2 = 1 ∧ x + y + z > 2 : UNSAT (McCallum nullifies here; the
    // complete projection reused from `cad` decides it).
    #[test]
    fn sphere_vs_plane_unsat() {
        let atoms = alloc::vec![
            (
                poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (1, &[(2, 2)]), (-1, &[]),]),
                Rel::Eq
            ),
            (
                poly(&[(1, &[(0, 1)]), (1, &[(1, 1)]), (1, &[(2, 1)]), (-2, &[])]),
                Rel::Gt
            ),
        ];
        assert_unsat(nlsat_decide(3, &atoms));
    }

    // A 3-var SAT with an equality and inequalities:
    // x + y + z = 0 ∧ x > 1 ∧ y > 1 : SAT (e.g. x=y=2, z=−4).
    #[test]
    fn three_var_linear_mix_sat() {
        let atoms = alloc::vec![
            (
                poly(&[(1, &[(0, 1)]), (1, &[(1, 1)]), (1, &[(2, 1)])]),
                Rel::Eq
            ),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), Rel::Gt),
            (poly(&[(1, &[(1, 1)]), (-1, &[])]), Rel::Gt),
        ];
        assert_sat(nlsat_decide(3, &atoms), &atoms);
    }

    // ---- Graceful declines ----------------------------------------------

    // Too many variables ⇒ Unknown (never a wrong verdict).
    #[test]
    fn too_many_vars_declines() {
        // A satisfiable-looking system in 6 vars; must decline, not answer.
        let atoms = alloc::vec![(poly(&[(1, &[(0, 1)]), (1, &[(5, 1)]), (-1, &[])]), Rel::Eq)];
        assert_unknown(nlsat_decide(6, &atoms));
    }

    // Too high a total degree ⇒ Unknown.
    #[test]
    fn too_high_degree_declines() {
        // x^13 - 2 = 0 exceeds MAX_DEG; decline rather than risk the cost.
        let atoms = alloc::vec![(poly(&[(1, &[(0, 13)]), (-2, &[])]), Rel::Eq)];
        assert_unknown(nlsat_decide(1, &atoms));
    }

    // A malformed atom referencing a variable outside `vars` ⇒ Unknown.
    #[test]
    fn out_of_range_var_declines() {
        let atoms = alloc::vec![(poly(&[(1, &[(3, 1)]), (-1, &[])]), Rel::Eq)];
        assert_unknown(nlsat_decide(1, &atoms));
    }

    // No constraints ⇒ trivially SAT with an all-zero witness of the right length.
    #[test]
    fn no_constraints_sat() {
        match nlsat_decide(3, &[]) {
            NlResult::Sat(w) => assert_eq!(w.len(), 3),
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    // A false constant constraint ⇒ UNSAT even with zero variables.
    #[test]
    fn false_constant_unsat() {
        // 1 = 0 (constant), zero variables.
        let atoms = alloc::vec![(Polynomial::constant(r(1)), Rel::Eq)];
        assert_unsat(nlsat_decide(0, &atoms));
    }

    // A true constant constraint with zero variables ⇒ SAT.
    #[test]
    fn true_constant_sat() {
        // 0 = 0 is trivially true; 5 > 0 too.
        let atoms = alloc::vec![(Polynomial::constant(r(5)), Rel::Gt)];
        match nlsat_decide(0, &atoms) {
            NlResult::Sat(w) => assert!(w.is_empty()),
            other => panic!("expected Sat, got {other:?}"),
        }
    }
}

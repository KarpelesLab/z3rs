//! Interval constraint propagation (ICP) — a *sound refutation* engine for
//! nonlinear arithmetic.
//!
//! A step toward Z3's `nlsat` (`z3/src/nlsat`, Z3 4.17.0, MIT): where full
//! `nlsat` decides QF_NRA via CAD, this module implements the cheaper,
//! one-directional half — proving **unsatisfiability** by interval arithmetic.
//! Each variable gets an interval box; every constraint `p ⋈ 0` is evaluated
//! over the box with the exact [`Interval`] arithmetic,
//! and single-variable linear bounds narrow the box. If any constraint's value
//! interval is disjoint from the values its relation allows, or a variable's box
//! becomes empty, the system is UNSAT.
//!
//! Because interval evaluation *over-approximates* the true value set, a proven
//! empty/contradictory box is always a genuine refutation (sound). It never
//! concludes SAT — callers fall back to a sound `unknown` — so wiring it in can
//! only turn `unknown` into `unsat`, never change a verdict.

use alloc::vec::Vec;
use core::cmp::Ordering;

use puremp::Rational;

use crate::math::interval::{Bound, Interval};
use crate::math::polynomial::{Polynomial, Var};

/// A comparison relation for a constraint `poly REL 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rel {
    Lt,
    Le,
    Eq,
    Ne,
    Ge,
    Gt,
}

/// A polynomial constraint `poly REL 0`.
#[derive(Clone, Debug)]
pub struct Constraint {
    pub poly: Polynomial,
    pub rel: Rel,
}

impl Constraint {
    pub fn new(poly: Polynomial, rel: Rel) -> Constraint {
        Constraint { poly, rel }
    }
}

/// Evaluate a polynomial over a box of variable intervals, returning the
/// interval hull of its value set (an over-approximation). Each variable's power
/// is raised with [`ipow`] (not repeated multiplication) so a single variable's
/// self-correlation is respected — crucially `x²` over `(-∞,∞)` is `[0,∞)`, not
/// `(-∞,∞)`. Cross-variable products still over-approximate, which stays sound.
pub fn eval_interval(poly: &Polynomial, box_: &[Interval]) -> Interval {
    let mut acc = Interval::point(Rational::from_integer(0.into()));
    for (coeff, mono) in poly.terms() {
        // Product of each variable's power (interval-mul across distinct vars),
        // built without a `point(1)` seed so a lone half-infinite factor is not
        // widened to the whole line by the general interval product.
        let mut term: Option<Interval> = None;
        for v in mono.vars() {
            let e = mono.degree_of(v);
            let vi = box_.get(v as usize).cloned().unwrap_or_else(Interval::all);
            let p = ipow(&vi, e);
            term = Some(match term {
                None => p,
                Some(t) => t.mul(&p),
            });
        }
        let term = term.unwrap_or_else(|| Interval::point(Rational::from_integer(1.into())));
        // Scale by the (scalar) coefficient without going through interval-mul,
        // which would over-widen a half-infinite `term` to the whole line.
        acc = acc.add(&scale(&term, coeff));
    }
    acc
}

/// Multiply an interval by a scalar rational, preserving half-infinite bounds
/// (unlike the general interval product, which conservatively widens).
fn scale(iv: &Interval, c: &Rational) -> Interval {
    if c.is_zero() {
        return Interval::point(Rational::from_integer(0.into()));
    }
    let Some((lo, hi)) = iv.bounds() else {
        return Interval::Empty;
    };
    let scaled = |b: &Bound| -> Bound {
        match b {
            Bound::Infinite => Bound::infinite(),
            Bound::Finite { value, open } => Bound::Finite {
                value: value.mul(c),
                open: *open,
            },
        }
    };
    let (nlo, nhi) = (scaled(lo), scaled(hi));
    if c.is_negative() {
        // Negation swaps the endpoints' roles.
        Interval::new(nhi, nlo)
    } else {
        Interval::new(nlo, nhi)
    }
}

/// An endpoint value on the extended real line.
#[derive(Clone)]
enum Ext {
    NegInf,
    PosInf,
    Val(Rational),
}

impl Ext {
    fn lower_of(b: &Bound) -> Ext {
        match b {
            Bound::Infinite => Ext::NegInf,
            Bound::Finite { value, .. } => Ext::Val(value.clone()),
        }
    }
    fn upper_of(b: &Bound) -> Ext {
        match b {
            Bound::Infinite => Ext::PosInf,
            Bound::Finite { value, .. } => Ext::Val(value.clone()),
        }
    }
    fn pow(&self, e: u32) -> Ext {
        match self {
            Ext::NegInf => {
                if e.is_multiple_of(2) {
                    Ext::PosInf
                } else {
                    Ext::NegInf
                }
            }
            Ext::PosInf => Ext::PosInf,
            Ext::Val(v) => Ext::Val(v.pow(e as i32)),
        }
    }
    /// Sign vs 0: -1, 0, +1 (±∞ are ∓1/+1).
    fn sign(&self) -> i32 {
        match self {
            Ext::NegInf => -1,
            Ext::PosInf => 1,
            Ext::Val(v) => v.signum(),
        }
    }
    fn max(a: Ext, b: Ext) -> Ext {
        match (&a, &b) {
            (Ext::PosInf, _) | (_, Ext::PosInf) => Ext::PosInf,
            (Ext::NegInf, other) | (other, Ext::NegInf) => other.clone(),
            (Ext::Val(x), Ext::Val(y)) => {
                if x >= y {
                    Ext::Val(x.clone())
                } else {
                    Ext::Val(y.clone())
                }
            }
        }
    }
    fn to_lower_bound(&self) -> Bound {
        match self {
            Ext::NegInf | Ext::PosInf => Bound::infinite(),
            Ext::Val(v) => Bound::closed(v.clone()),
        }
    }
    fn to_upper_bound(&self) -> Bound {
        match self {
            Ext::NegInf | Ext::PosInf => Bound::infinite(),
            Ext::Val(v) => Bound::closed(v.clone()),
        }
    }
}

/// The exact interval image of `vi` raised to the nonnegative power `e`,
/// respecting even/odd monotonicity (so squares are nonnegative). Result
/// endpoints are marked *closed* — a sound widening (it never shrinks the value
/// set, so no false refutation).
pub fn ipow(vi: &Interval, e: u32) -> Interval {
    if e == 0 {
        return Interval::point(Rational::from_integer(1.into()));
    }
    if e == 1 {
        return vi.clone(); // identity — preserves the open/closed flags exactly
    }
    let Some((lo, hi)) = vi.bounds() else {
        return Interval::Empty;
    };
    // Raise an endpoint's value to the power `e`, preserving its open/closed flag
    // (`±∞ ↦ ±∞`); the flag carry is what lets `y > 1 ⇒ y² > 1` stay strict.
    let powv = |v: &Rational| -> Rational {
        let mut p = Rational::from_integer(1.into());
        for _ in 0..e {
            p = p.mul(v);
        }
        p
    };
    let powb = |b: &Bound| -> Bound {
        match b {
            Bound::Infinite => Bound::Infinite,
            Bound::Finite { value, open } => Bound::Finite {
                value: powv(value),
                open: *open,
            },
        }
    };
    if e % 2 == 1 {
        // Odd powers are monotonically increasing over all reals.
        return Interval::new(powb(lo), powb(hi));
    }
    let lo_nonneg = matches!(lo, Bound::Finite { value, .. } if !value.is_negative());
    let hi_nonpos = matches!(hi, Bound::Finite { value, .. } if !value.is_positive());
    if lo_nonneg {
        Interval::new(powb(lo), powb(hi)) // increasing on [0, ∞)
    } else if hi_nonpos {
        Interval::new(powb(hi), powb(lo)) // decreasing on (−∞, 0]
    } else {
        // Straddles 0: the minimum 0 is attained (closed); the maximum is the
        // larger endpoint power, or +∞ if either endpoint is infinite.
        let up = match (lo, hi) {
            (Bound::Infinite, _) | (_, Bound::Infinite) => Bound::Infinite,
            (
                Bound::Finite {
                    value: lv,
                    open: lo_open,
                },
                Bound::Finite {
                    value: hv,
                    open: hi_open,
                },
            ) => {
                let (pl, ph) = (powv(lv), powv(hv));
                match pl.cmp(&ph) {
                    Ordering::Greater => Bound::Finite {
                        value: pl,
                        open: *lo_open,
                    },
                    Ordering::Less => Bound::Finite {
                        value: ph,
                        open: *hi_open,
                    },
                    Ordering::Equal => Bound::Finite {
                        value: ph,
                        open: *lo_open && *hi_open,
                    },
                }
            }
        };
        Interval::new(Bound::closed(Rational::from_integer(0.into())), up)
    }
}

/// Can an interval `i` contain a value satisfying `value REL 0`?
fn relation_feasible(i: &Interval, rel: Rel) -> bool {
    let Some((lo, hi)) = i.bounds() else {
        return false; // empty interval satisfies nothing
    };
    // Helpers on the sign of the endpoints.
    let lo_cmp0 = bound_cmp_zero_lower(lo); // is the low end below/at/above 0
    let hi_cmp0 = bound_cmp_zero_upper(hi);
    match rel {
        // poly < 0 feasible iff some value < 0, i.e. the low end is < 0.
        Rel::Lt => lo_cmp0 == SignPos::BelowStrict,
        // poly <= 0 feasible iff the low end is <= 0.
        Rel::Le => matches!(lo_cmp0, SignPos::BelowStrict | SignPos::AtZero),
        // poly > 0 feasible iff the high end is > 0.
        Rel::Gt => hi_cmp0 == SignPos::AboveStrict,
        Rel::Ge => matches!(hi_cmp0, SignPos::AboveStrict | SignPos::AtZero),
        // poly = 0 feasible iff 0 is inside the interval.
        Rel::Eq => i.contains(&Rational::from_integer(0.into())),
        // poly != 0 feasible unless the interval is exactly {0}.
        Rel::Ne => !is_point_zero(i),
    }
}

#[derive(PartialEq, Eq)]
enum SignPos {
    BelowStrict,
    AtZero,
    AboveStrict,
}

/// Where the *lower* endpoint sits relative to 0 (for feasibility of `<`/`<=`,
/// which care about how small the value can get).
fn bound_cmp_zero_lower(lo: &Bound) -> SignPos {
    match lo {
        Bound::Infinite => SignPos::BelowStrict, // -∞ lower bound
        Bound::Finite { value, open } => match value.signum().cmp(&0) {
            Ordering::Less => SignPos::BelowStrict,
            Ordering::Greater => SignPos::AboveStrict,
            // value == 0: if the lower bound is *open* at 0, values are > 0.
            Ordering::Equal => {
                if *open {
                    SignPos::AboveStrict
                } else {
                    SignPos::AtZero
                }
            }
        },
    }
}

/// Where the *upper* endpoint sits relative to 0 (for `>`/`>=`).
fn bound_cmp_zero_upper(hi: &Bound) -> SignPos {
    match hi {
        Bound::Infinite => SignPos::AboveStrict, // +∞ upper bound
        Bound::Finite { value, open } => match value.signum().cmp(&0) {
            Ordering::Greater => SignPos::AboveStrict,
            Ordering::Less => SignPos::BelowStrict,
            Ordering::Equal => {
                if *open {
                    SignPos::BelowStrict
                } else {
                    SignPos::AtZero
                }
            }
        },
    }
}

fn is_point_zero(i: &Interval) -> bool {
    match i.bounds() {
        Some((
            Bound::Finite {
                value: l,
                open: false,
            },
            Bound::Finite {
                value: h,
                open: false,
            },
        )) => l.is_zero() && h.is_zero(),
        _ => false,
    }
}

/// Extract a single-variable linear bound `a*x REL c` from a constraint, if it
/// has that shape, and return the implied interval for `x`.
fn linear_bound(c: &Constraint) -> Option<(Var, Interval)> {
    let p = &c.poly;
    let vars = p.vars();
    if vars.len() != 1 || p.total_degree() != 1 {
        return None;
    }
    let x = vars[0];
    // p = a*x + b with a != 0.
    let a = p
        .terms()
        .iter()
        .find(|(_, m)| m.degree_of(x) == 1)
        .map(|(co, _)| co.clone())?;
    // The constant term `b` (coefficient of the `1` monomial), 0 if absent.
    let b = p
        .terms()
        .iter()
        .find(|(_, m)| m.is_one())
        .map(|(co, _)| co.clone())
        .unwrap_or_else(|| Rational::from_integer(0.into()));
    // a*x + b REL 0  ⇒  x REL' (-b/a), flipping the relation if a < 0.
    let bound_val = b.neg().div(&a);
    let flip = a.is_negative();
    let rel = if flip { flip_rel(c.rel) } else { c.rel };
    let iv = match rel {
        Rel::Lt => Interval::new(Bound::infinite(), Bound::open(bound_val)),
        Rel::Le => Interval::new(Bound::infinite(), Bound::closed(bound_val)),
        Rel::Gt => Interval::new(Bound::open(bound_val), Bound::infinite()),
        Rel::Ge => Interval::new(Bound::closed(bound_val), Bound::infinite()),
        Rel::Eq => Interval::point(bound_val),
        Rel::Ne => return None, // a disequality does not narrow to an interval
    };
    Some((x, iv))
}

fn flip_rel(r: Rel) -> Rel {
    match r {
        Rel::Lt => Rel::Gt,
        Rel::Le => Rel::Ge,
        Rel::Gt => Rel::Lt,
        Rel::Ge => Rel::Le,
        Rel::Eq => Rel::Eq,
        Rel::Ne => Rel::Ne,
    }
}

/// A rational `U ≥ √b` (with `U` tight), for `b ≥ 0` — a sound upper bound on the
/// square root, so `[-U, U]` over-approximates `{v : v² ≤ b}`.
fn sqrt_upper(b: &Rational) -> Rational {
    if !b.is_positive() {
        return Rational::from_integer(0.into());
    }
    let two = Rational::from_integer(2.into());
    let mut lo = Rational::from_integer(0.into());
    // `hi²  ≥ b`: if b ≤ 1 use 1 (1 ≥ b); else b (b² ≥ b).
    let mut hi = if *b > Rational::from_integer(1.into()) {
        b.clone()
    } else {
        Rational::from_integer(1.into())
    };
    for _ in 0..48 {
        let mid = lo.add(&hi).div(&two);
        if mid.mul(&mid) >= *b {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    hi
}

/// The finite lower-bound value of an interval, or `None` if it is `-∞` / empty.
fn interval_inf(iv: &Interval) -> Option<Rational> {
    match iv.bounds()?.0 {
        Bound::Finite { value, .. } => Some(value.clone()),
        Bound::Infinite => None,
    }
}

/// Backward-propagate a bound on `v` from a constraint of the form
/// `a·v² + rest ⋈ 0` with `a` a positive constant and `⋈ ∈ {<, ≤}`: then
/// `v² < −rest/a ≤ −inf(rest)/a`, giving `|v| ≤ √(−inf(rest)/a)`. Returns the
/// (sound over-approximating) interval for `v`, `Empty` if the bound is
/// infeasible, or `None` if the constraint is not of this shape.
fn square_bound(c: &Constraint, v: Var, box_: &[Interval]) -> Option<Interval> {
    // `a·v² + rest ⋈ 0` bounds `v²` when `⋈` implies `a·v²+rest ≤ 0`: a strict or
    // non-strict `<`/`≤`, or an equality (`=0 ⇒ ≤0`). Equalities are the common
    // shape `x²+y²=k`, letting us bound each variable.
    let strict = match c.rel {
        Rel::Lt => true,
        Rel::Le | Rel::Eq => false,
        _ => return None,
    };
    let mut a = Rational::from_integer(0.into());
    let mut rest_terms = alloc::vec::Vec::new();
    for (coeff, mono) in c.poly.terms() {
        match mono.degree_of(v) {
            0 => rest_terms.push((coeff.clone(), mono.clone())),
            2 if mono.total_degree() == 2 => a = a.add(coeff), // exactly v²
            _ => return None, // v¹, v³, or v² times another variable
        }
    }
    let mut rest = Polynomial::from_terms(rest_terms);
    // For an equality, `p = 0 ⇔ −p = 0`, so a negative `v²` coefficient can be
    // flipped positive (e.g. `x² − 2y² = 0` bounds `y` via `2y² = x²`).
    if a.is_negative() && c.rel == Rel::Eq {
        a = a.neg();
        rest = rest.neg();
    }
    if !a.is_positive() {
        return None;
    }
    let c_iv = eval_interval(&rest, box_);
    let inf = interval_inf(&c_iv)?; // −∞ ⇒ no bound
    let b = inf.neg().div(&a); // v² ≤ b (strict for `<`)
    if b.is_negative() {
        return Some(Interval::Empty);
    }
    if b.is_zero() {
        return Some(if strict {
            Interval::Empty // v² < 0 impossible
        } else {
            Interval::point(Rational::from_integer(0.into())) // v² ≤ 0 ⇒ v = 0
        });
    }
    let u = sqrt_upper(&b);
    Some(Interval::closed(u.neg(), u))
}

/// Narrow a variable box from the linear bounds **and** square bounds in
/// `constraints`, to a fixpoint. Returns `None` if a variable's box becomes
/// empty (the system is then unsatisfiable), else the (sound over-approximating)
/// box. Shared by [`refute`] and callers that enumerate integer points.
pub fn narrow_box(constraints: &[Constraint], num_vars: usize) -> Option<Vec<Interval>> {
    let mut box_: Vec<Interval> = alloc::vec![Interval::all(); num_vars];
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 2 * num_vars + 6 {
        changed = false;
        rounds += 1;
        for c in constraints {
            // Single-variable linear bounds.
            if let Some((x, iv)) = linear_bound(c) {
                let tightened = box_[x as usize].intersect(&iv);
                if tightened != box_[x as usize] {
                    box_[x as usize] = tightened;
                    changed = true;
                }
            }
            // Square bounds `a·v² + rest < 0` ⇒ `|v| ≤ √(…)`, for each variable.
            for v in 0..num_vars as Var {
                if let Some(iv) = square_bound(c, v, &box_) {
                    let tightened = box_[v as usize].intersect(&iv);
                    if tightened != box_[v as usize] {
                        box_[v as usize] = tightened;
                        changed = true;
                    }
                }
                // Interval-coefficient linear bounds `c1(rest)·v + c0(rest) ⋈ 0`
                // (bilinear terms like `x·y = k`, which the pure-linear and square
                // rules miss).
                if let Some(iv) = product_bound(c, v, &box_) {
                    let tightened = box_[v as usize].intersect(&iv);
                    if tightened != box_[v as usize] {
                        box_[v as usize] = tightened;
                        changed = true;
                    }
                }
            }
        }
        if box_.iter().any(Interval::is_empty) {
            return None;
        }
    }
    Some(box_)
}

/// Reciprocal `1/b` of a bound (its finite value assumed nonzero); `±∞ ↦ 0`
/// (open).
fn bound_recip(b: &Bound) -> Bound {
    match b {
        Bound::Infinite => Bound::open(Rational::from_integer(0.into())),
        Bound::Finite { value, open } => {
            if value.is_zero() {
                Bound::infinite()
            } else {
                Bound::Finite {
                    value: value.recip(),
                    open: *open,
                }
            }
        }
    }
}

/// Reciprocal of a definite-sign interval (0 excluded): `1/[lo,hi] = [1/hi,1/lo]`.
/// `None` if the interval straddles (or touches) 0.
/// A bound that excludes 0 from below (`> 0`): a positive value, or an open 0.
fn bound_gt_zero(b: &Bound) -> bool {
    matches!(b, Bound::Finite { value, open } if value.is_positive() || (value.is_zero() && *open))
}

/// A bound that excludes 0 from above (`< 0`): a negative value, or an open 0.
fn bound_lt_zero(b: &Bound) -> bool {
    matches!(b, Bound::Finite { value, open } if value.is_negative() || (value.is_zero() && *open))
}

fn interval_recip(iv: &Interval) -> Option<Interval> {
    let (lo, hi) = iv.bounds()?;
    if !bound_gt_zero(lo) && !bound_lt_zero(hi) {
        return None; // straddles or touches 0
    }
    Some(Interval::new(bound_recip(hi), bound_recip(lo)))
}

/// Bound on `v` from a constraint linear in `v` with interval coefficients:
/// `c1(rest)·v + c0(rest) ⋈ 0`. Evaluates `c1`, `c0` over the box; when `c1` has
/// a definite sign, solves for `v`'s interval. Over-approximates (so it is a
/// sound narrowing), catching bilinear products like `x·y = k`.
fn product_bound(c: &Constraint, v: Var, box_: &[Interval]) -> Option<Interval> {
    if c.poly.degree_of(v) != 1 {
        return None;
    }
    let c1 = c.poly.coeff_of_var(v, 1);
    let c0 = c.poly.coeff_of_var(v, 0);
    let a = eval_interval(&c1, box_);
    let b = eval_interval(&c0, box_);
    let (alo, ahi) = a.bounds()?;
    let a_pos = bound_gt_zero(alo);
    let a_neg = bound_lt_zero(ahi);
    if !a_pos && !a_neg {
        return None; // coefficient straddles 0 — no bound
    }
    // Solution of `a·v = -b`  ⇒  `v = -b / a`.
    let recip = interval_recip(&a)?; // also asserts a excludes 0
    let b_zero = matches!(
        b.bounds(),
        Some((Bound::Finite { value: lv, open: false }, Bound::Finite { value: hv, open: false }))
            if lv.is_zero() && hv.is_zero()
    );
    // `-b / a` with `b = 0` is exactly 0 (`a` excludes 0); computing it via the
    // generic interval product would hit `0·∞` and over-approximate.
    let sol = if b_zero {
        Interval::point(Rational::from_integer(0.into()))
    } else {
        b.neg().mul(&recip)
    };
    let (slo, shi) = sol.bounds()?;
    let neg_inf = Bound::infinite();
    let result = match (c.rel, a_pos) {
        (Rel::Eq, _) => sol.clone(),
        // `a·v + b ≤/<​ 0` ⇒ `v ≤ -b/a` (a>0) or `v ≥ -b/a` (a<0); closed bounds
        // (an over-approximation, hence sound).
        (Rel::Le | Rel::Lt, true) | (Rel::Ge | Rel::Gt, false) => {
            Interval::new(neg_inf, shi.clone())
        }
        (Rel::Le | Rel::Lt, false) | (Rel::Ge | Rel::Gt, true) => {
            Interval::new(slo.clone(), neg_inf)
        }
        (Rel::Ne, _) => return None,
    };
    Some(result)
}

/// Attempt to prove `constraints` (a conjunction, all must hold) unsatisfiable
/// over the reals using interval propagation. Returns `true` only when a genuine
/// interval refutation is found (sound); `false` means "not refuted" (unknown).
pub fn refute(constraints: &[Constraint], num_vars: usize) -> bool {
    // Seed the box from single-variable linear bounds, to a fixpoint.
    let Some(box_) = narrow_box(constraints, num_vars) else {
        return true; // an empty box is an immediate refutation
    };

    // Evaluate every constraint over the (narrowed) box; if any is infeasible,
    // the system is UNSAT.
    for c in constraints {
        let val = eval_interval(&c.poly, &box_);
        if !relation_feasible(&val, c.rel) {
            return true;
        }
    }
    false
}

/// The integer range `[lo, hi]` of the interval `iv`, or `None` if either side
/// is unbounded (or too large to fit `i64`). An empty range yields `lo > hi`.
fn int_range(iv: &Interval) -> Option<(i64, i64)> {
    let (lb, ub) = iv.bounds()?;
    let lo = match lb {
        Bound::Infinite => return None,
        Bound::Finite { value, open } => {
            let c = if *open {
                value.floor().add(&1.into())
            } else {
                value.ceil()
            };
            c.to_i64()?
        }
    };
    let hi = match ub {
        Bound::Infinite => return None,
        Bound::Finite { value, open } => {
            let f = if *open {
                value.ceil().sub(&1.into())
            } else {
                value.floor()
            };
            f.to_i64()?
        }
    };
    Some((lo, hi))
}

/// Decide a conjunction of **integer** polynomial constraints when interval
/// propagation bounds every variable to a finite box: exhaustively enumerate the
/// integer points and verify each exactly. Complete for that (bounded) fragment.
/// Returns `None` when a variable is unbounded or the box is too large to search.
pub fn decide_bounded_int(constraints: &[Constraint], num_vars: usize) -> Option<bool> {
    let box_ = match narrow_box(constraints, num_vars) {
        None => return Some(false), // empty box ⇒ unsat
        Some(b) => b,
    };
    let mut ranges: Vec<(i64, i64)> = Vec::with_capacity(num_vars);
    let mut total: u128 = 1;
    for iv in &box_ {
        let (lo, hi) = int_range(iv)?;
        if lo > hi {
            return Some(false); // an empty integer range ⇒ unsat
        }
        total = total.saturating_mul((hi - lo + 1) as u128);
        if total > 300_000 {
            return None; // search space too large — decline
        }
        ranges.push((lo, hi));
    }
    // Odometer over the integer box.
    let mut point: Vec<i64> = ranges.iter().map(|&(lo, _)| lo).collect();
    loop {
        let sat = constraints.iter().all(|c| {
            let val = c
                .poly
                .eval(&|v| Rational::from_integer(point[v as usize].into()));
            match c.rel {
                Rel::Lt => val.is_negative(),
                Rel::Le => val.is_negative() || val.is_zero(),
                Rel::Gt => val.is_positive(),
                Rel::Ge => val.is_positive() || val.is_zero(),
                Rel::Eq => val.is_zero(),
                Rel::Ne => !val.is_zero(),
            }
        });
        if sat {
            return Some(true);
        }
        // Advance the odometer.
        let mut i = 0;
        loop {
            if i == num_vars {
                return Some(false); // exhausted the whole box, none satisfied
            }
            point[i] += 1;
            if point[i] <= ranges[i].1 {
                break;
            }
            point[i] = ranges[i].0;
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::polynomial::Monomial;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn x_pow(v: Var, e: u32) -> Monomial {
        Monomial::from_powers(&[(v, e)])
    }
    // `a*x0 + b`.
    fn poly1(a: i64, b: i64) -> Polynomial {
        poly1v(a, b, 0)
    }
    // `a*x_var + b`.
    fn poly1v(a: i64, b: i64, var: Var) -> Polynomial {
        Polynomial::from_terms(vec![
            (r(a), Monomial::from_powers(&[(var, 1)])),
            (r(b), Monomial::one()),
        ])
    }

    // x*x < 0 is unsatisfiable over the reals.
    #[test]
    fn square_negative_unsat() {
        // poly = x^2, rel < 0
        let p = Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 2))]);
        assert!(refute(&[Constraint::new(p, Rel::Lt)], 1));
    }

    // x > 2 ∧ x*x < 4 is unsatisfiable (x>2 ⇒ x²>4).
    #[test]
    fn bound_and_square_unsat() {
        // c1: x - 2 > 0
        let c1 = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 1)), (r(-2), Monomial::one())]),
            Rel::Gt,
        );
        // c2: x^2 - 4 < 0
        let c2 = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 2)), (r(-4), Monomial::one())]),
            Rel::Lt,
        );
        assert!(refute(&[c1, c2], 1));
    }

    // x^2 + y^2 < 1 ∧ x > 2 is unsatisfiable.
    #[test]
    fn circle_and_bound_unsat() {
        let c1 = Constraint::new(
            Polynomial::from_terms(alloc::vec![
                (r(1), x_pow(0, 2)),
                (r(1), x_pow(1, 2)),
                (r(-1), Monomial::one()),
            ]),
            Rel::Lt,
        );
        let c2 = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 1)), (r(-2), Monomial::one())]),
            Rel::Gt,
        );
        assert!(refute(&[c1, c2], 2));
    }

    // A satisfiable nonlinear system is NOT refuted (sound: no false unsat).
    #[test]
    fn satisfiable_not_refuted() {
        // x*x = 4 (has solutions ±2) — ICP must not claim unsat.
        let c = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 2)), (r(-4), Monomial::one())]),
            Rel::Eq,
        );
        assert!(!refute(&[c], 1));
    }

    // Linear-only contradictions are caught too (x >= 5 ∧ x <= 3).
    #[test]
    fn linear_box_empty_unsat() {
        let c1 = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 1)), (r(-5), Monomial::one())]),
            Rel::Ge,
        );
        let c2 = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 1)), (r(-3), Monomial::one())]),
            Rel::Le,
        );
        assert!(refute(&[c1, c2], 1));
    }

    // Bounded integer search: x·y = 12 ∧ 1≤x≤4 ∧ 1≤y≤4 is SAT (x=3,y=4).
    #[test]
    fn bounded_int_product_sat() {
        let c = vec![
            // x*y - 12 = 0
            Constraint::new(
                Polynomial::from_terms(vec![
                    (r(1), Monomial::from_powers(&[(0, 1), (1, 1)])),
                    (r(-12), Monomial::one()),
                ]),
                Rel::Eq,
            ),
            Constraint::new(poly1(1, -1), Rel::Ge), // x >= 1
            Constraint::new(poly1(1, -4), Rel::Le), // x <= 4
            Constraint::new(poly1v(1, -1, 1), Rel::Ge), // y >= 1
            Constraint::new(poly1v(1, -4, 1), Rel::Le), // y <= 4
        ];
        assert_eq!(decide_bounded_int(&c, 2), Some(true));
    }

    // x·y − x = 0 ∧ x>1 ∧ y>1 is UNSAT: x(y−1)=0 forces x=0 or y=1.
    #[test]
    fn bounded_int_xy_eq_x_unsat() {
        let c = vec![
            Constraint::new(
                Polynomial::from_terms(vec![
                    (r(1), Monomial::from_powers(&[(0, 1), (1, 1)])), // x·y
                    (r(-1), Monomial::from_powers(&[(0, 1)])),        // − x
                ]),
                Rel::Eq,
            ),
            Constraint::new(poly1(1, -1), Rel::Gt), // x > 1
            Constraint::new(poly1v(1, -1, 1), Rel::Gt), // y > 1
        ];
        assert_eq!(decide_bounded_int(&c, 2), Some(false));
    }

    // x·y = 7 ∧ 1≤x≤3 ∧ 1≤y≤3 is UNSAT (7 is prime, exceeds the box).
    #[test]
    fn bounded_int_product_unsat() {
        let c = vec![
            Constraint::new(
                Polynomial::from_terms(vec![
                    (r(1), Monomial::from_powers(&[(0, 1), (1, 1)])),
                    (r(-7), Monomial::one()),
                ]),
                Rel::Eq,
            ),
            Constraint::new(poly1(1, -1), Rel::Ge),
            Constraint::new(poly1(1, -3), Rel::Le),
            Constraint::new(poly1v(1, -1, 1), Rel::Ge),
            Constraint::new(poly1v(1, -3, 1), Rel::Le),
        ];
        assert_eq!(decide_bounded_int(&c, 2), Some(false));
    }

    // Square narrowing: x²+y²<1 ∧ xy>1 is UNSAT (|x|,|y|<1 ⇒ |xy|<1).
    #[test]
    fn square_narrowing_refutes() {
        let c = vec![
            // x² + y² - 1 < 0
            Constraint::new(
                Polynomial::from_terms(vec![
                    (r(1), x_pow(0, 2)),
                    (r(1), x_pow(1, 2)),
                    (r(-1), Monomial::one()),
                ]),
                Rel::Lt,
            ),
            // x*y - 1 > 0
            Constraint::new(
                Polynomial::from_terms(vec![
                    (r(1), Monomial::from_powers(&[(0, 1), (1, 1)])),
                    (r(-1), Monomial::one()),
                ]),
                Rel::Gt,
            ),
        ];
        assert!(refute(&c, 2));
    }

    // Square narrowing must NOT over-narrow: x²+y²<4 ∧ xy>1 is SATISFIABLE
    // (e.g. x=y=1.2), so it must NOT be refuted.
    #[test]
    fn square_narrowing_no_false_refute() {
        let c = vec![
            Constraint::new(
                Polynomial::from_terms(vec![
                    (r(1), x_pow(0, 2)),
                    (r(1), x_pow(1, 2)),
                    (r(-4), Monomial::one()),
                ]),
                Rel::Lt,
            ),
            Constraint::new(
                Polynomial::from_terms(vec![
                    (r(1), Monomial::from_powers(&[(0, 1), (1, 1)])),
                    (r(-1), Monomial::one()),
                ]),
                Rel::Gt,
            ),
        ];
        assert!(!refute(&c, 2), "wrongly refuted a satisfiable system");
    }

    // Unbounded ⇒ declined (None).
    #[test]
    fn unbounded_int_declined() {
        let c = vec![Constraint::new(
            Polynomial::from_terms(vec![(r(1), Monomial::from_powers(&[(0, 1), (1, 1)]))]),
            Rel::Eq,
        )];
        assert_eq!(decide_bounded_int(&c, 2), None);
    }

    // A feasible linear system is not refuted.
    #[test]
    fn feasible_linear_not_refuted() {
        let c1 = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 1)), (r(-1), Monomial::one())]),
            Rel::Ge,
        );
        let c2 = Constraint::new(
            Polynomial::from_terms(alloc::vec![(r(1), x_pow(0, 1)), (r(-5), Monomial::one())]),
            Rel::Le,
        );
        assert!(!refute(&[c1, c2], 1));
    }
}

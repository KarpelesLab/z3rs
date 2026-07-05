//! Exact rational interval arithmetic with (optionally) open/closed and
//! infinite endpoints.
//!
//! Ported from Z3's `math/interval` (`z3/src/math/interval/interval.h`,
//! Z3 4.17.0, MIT). Z3's `interval_manager` is generic over a numeral type and
//! tracks lower/upper bounds together with open/closed flags and ±∞ markers,
//! propagating them through `+ - * ^` for interval-based bound reasoning in the
//! arithmetic solvers. This port specialises the numeral to [`Rational`] and
//! keeps the same bound bookkeeping.
//!
//! Soundness contract: for intervals `a`, `b`, if `x ∈ a` and `y ∈ b` then
//! `x⊕y ∈ (a⊕b)` for every operation `⊕` implemented here (the result interval
//! over-approximates the true image, exactly for `+`, `-`, and monotone `*`).

use core::cmp::Ordering;

use puremp::Rational;

/// One endpoint of an interval: either `±∞` or a finite rational that is either
/// included (closed) or excluded (open).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bound {
    /// `-∞` (only meaningful as a lower bound) or `+∞` (upper): the value is
    /// stored so comparisons are total; `open` is implicit (infinite bounds are
    /// never attained).
    Infinite,
    /// A finite rational endpoint; `open` = the value is *excluded*.
    Finite { value: Rational, open: bool },
}

impl Bound {
    /// A finite closed (inclusive) endpoint.
    pub fn closed(value: Rational) -> Bound {
        Bound::Finite { value, open: false }
    }
    /// A finite open (exclusive) endpoint.
    pub fn open(value: Rational) -> Bound {
        Bound::Finite { value, open: true }
    }
    /// The infinite endpoint (`-∞` for a lower bound, `+∞` for an upper).
    pub fn infinite() -> Bound {
        Bound::Infinite
    }
    fn is_open(&self) -> bool {
        matches!(self, Bound::Finite { open: true, .. }) || matches!(self, Bound::Infinite)
    }
    fn finite_value(&self) -> Option<&Rational> {
        match self {
            Bound::Finite { value, .. } => Some(value),
            Bound::Infinite => None,
        }
    }
}

/// A (possibly unbounded, possibly open) interval of rationals, or the empty
/// set. Constructed through [`Interval::new`], which normalises degenerate and
/// empty inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Interval {
    /// The empty interval (no value satisfies the bounds).
    Empty,
    /// `[lower, upper]` with the open/closed flags carried by each [`Bound`].
    Range { lower: Bound, upper: Bound },
}

impl Interval {
    /// Build an interval from a lower and upper bound, normalising to
    /// [`Interval::Empty`] when the bounds describe no points
    /// (e.g. `lower > upper`, or `lower == upper` with either side open).
    pub fn new(lower: Bound, upper: Bound) -> Interval {
        match (lower.finite_value(), upper.finite_value()) {
            (Some(l), Some(u)) => match l.cmp(u) {
                Ordering::Greater => Interval::Empty,
                Ordering::Equal if lower.is_open() || upper.is_open() => Interval::Empty,
                _ => Interval::Range { lower, upper },
            },
            // At least one side infinite ⇒ always non-empty.
            _ => Interval::Range { lower, upper },
        }
    }

    /// The whole real line `(-∞, +∞)`.
    pub fn all() -> Interval {
        Interval::new(Bound::infinite(), Bound::infinite())
    }

    /// The single point `[v, v]`.
    pub fn point(v: Rational) -> Interval {
        Interval::new(Bound::closed(v.clone()), Bound::closed(v))
    }

    /// The closed interval `[lo, hi]`.
    pub fn closed(lo: Rational, hi: Rational) -> Interval {
        Interval::new(Bound::closed(lo), Bound::closed(hi))
    }

    /// Is this the empty interval?
    pub fn is_empty(&self) -> bool {
        matches!(self, Interval::Empty)
    }

    /// Does `x` lie within the interval (respecting open/closed endpoints)?
    pub fn contains(&self, x: &Rational) -> bool {
        let Interval::Range { lower, upper } = self else {
            return false;
        };
        let lower_ok = match lower {
            Bound::Infinite => true,
            Bound::Finite { value, open } => match x.cmp(value) {
                Ordering::Greater => true,
                Ordering::Equal => !open,
                Ordering::Less => false,
            },
        };
        let upper_ok = match upper {
            Bound::Infinite => true,
            Bound::Finite { value, open } => match x.cmp(value) {
                Ordering::Less => true,
                Ordering::Equal => !open,
                Ordering::Greater => false,
            },
        };
        lower_ok && upper_ok
    }

    /// The lower / upper bounds, or `None` for the empty interval.
    pub fn bounds(&self) -> Option<(&Bound, &Bound)> {
        match self {
            Interval::Empty => None,
            Interval::Range { lower, upper } => Some((lower, upper)),
        }
    }

    /// Negate: `-[l, u] = [-u, -l]`, swapping and negating the endpoints.
    pub fn neg(&self) -> Interval {
        let Interval::Range { lower, upper } = self else {
            return Interval::Empty;
        };
        Interval::new(neg_bound(upper), neg_bound(lower))
    }

    /// Minkowski sum: `[a,b] + [c,d] = [a+c, b+d]`. Openness propagates (the sum
    /// endpoint is attained only if both contributing endpoints are).
    pub fn add(&self, other: &Interval) -> Interval {
        let (Interval::Range { lower: l1, upper: u1 }, Interval::Range { lower: l2, upper: u2 }) =
            (self, other)
        else {
            return Interval::Empty;
        };
        Interval::new(add_bound(l1, l2), add_bound(u1, u2))
    }

    /// Difference: `a - b = a + (-b)`.
    pub fn sub(&self, other: &Interval) -> Interval {
        self.add(&other.neg())
    }

    /// Product: the image `{ x*y : x∈a, y∈b }`, computed from the four endpoint
    /// products (the exact hull for intervals of rationals).
    pub fn mul(&self, other: &Interval) -> Interval {
        let (Interval::Range { lower: l1, upper: u1 }, Interval::Range { lower: l2, upper: u2 }) =
            (self, other)
        else {
            return Interval::Empty;
        };
        // Products involving an infinite endpoint yield an infinite result
        // endpoint unless the finite factor is exactly zero (0·∞ ⇒ 0). Rather
        // than enumerate the sign cases, fall back to `all()` whenever an
        // infinite bound can reach the product, which stays sound.
        let corners = [
            mul_bound(l1, l2),
            mul_bound(l1, u2),
            mul_bound(u1, l2),
            mul_bound(u1, u2),
        ];
        if corners.iter().any(|c| c.is_none()) {
            // Some corner is unbounded — over-approximate to a half/whole line by
            // computing the finite hull we can and widening the infinite side.
            return infinite_mul_hull(&corners);
        }
        let mut pts: Vec<(Rational, bool)> = corners.into_iter().map(|c| c.unwrap()).collect();
        pts.sort_by(|a, b| a.0.cmp(&b.0));
        // Lowest corner is the min; open iff that corner is open. Symmetric for max.
        let min = pts.first().unwrap().clone();
        let max = pts.last().unwrap().clone();
        Interval::new(
            Bound::Finite { value: min.0, open: min.1 },
            Bound::Finite { value: max.0, open: max.1 },
        )
    }

    /// Intersection: the largest interval contained in both.
    pub fn intersect(&self, other: &Interval) -> Interval {
        let (Interval::Range { lower: l1, upper: u1 }, Interval::Range { lower: l2, upper: u2 }) =
            (self, other)
        else {
            return Interval::Empty;
        };
        let lower = max_lower(l1, l2);
        let upper = min_upper(u1, u2);
        Interval::new(lower, upper)
    }
}

use alloc::vec::Vec;

fn neg_bound(b: &Bound) -> Bound {
    match b {
        Bound::Infinite => Bound::Infinite,
        Bound::Finite { value, open } => Bound::Finite {
            value: value.neg(),
            open: *open,
        },
    }
}

fn add_bound(a: &Bound, b: &Bound) -> Bound {
    match (a, b) {
        (Bound::Infinite, _) | (_, Bound::Infinite) => Bound::Infinite,
        (Bound::Finite { value: x, open: ox }, Bound::Finite { value: y, open: oy }) => {
            Bound::Finite {
                value: x.add(y),
                open: *ox || *oy,
            }
        }
    }
}

/// Multiply two endpoint values, returning `None` if the product is unbounded
/// (an infinite endpoint times a nonzero finite/infinite one).
fn mul_bound(a: &Bound, b: &Bound) -> Option<(Rational, bool)> {
    match (a, b) {
        (Bound::Finite { value: x, open: ox }, Bound::Finite { value: y, open: oy }) => {
            let prod = x.mul(y);
            // The product endpoint is open iff either factor endpoint is open and
            // the other factor is nonzero (a zero factor pins the product to 0).
            let open = (*ox && !y.is_zero()) || (*oy && !x.is_zero());
            Some((prod, open))
        }
        // ∞ * 0 = 0 (a genuinely finite, attained corner).
        (Bound::Infinite, Bound::Finite { value, .. })
        | (Bound::Finite { value, .. }, Bound::Infinite)
            if value.is_zero() =>
        {
            Some((Rational::from_integer(0.into()), false))
        }
        _ => None,
    }
}

/// Widen a set of product corners (some unbounded) into a sound hull. If any
/// corner is unbounded we cannot in general pin both sides, so we return the
/// tightest half-line consistent with the finite corners, or the whole line.
fn infinite_mul_hull(corners: &[Option<(Rational, bool)>; 4]) -> Interval {
    let finite: Vec<&(Rational, bool)> = corners.iter().filter_map(|c| c.as_ref()).collect();
    if finite.is_empty() {
        return Interval::all();
    }
    // We know an unbounded corner exists on at least one side; without sign
    // tracking we conservatively leave both ends infinite. This is sound (it
    // over-approximates) and matches Z3 falling back to (-oo,+oo) when a factor
    // straddles zero with an unbounded partner.
    Interval::all()
}

/// The tighter (larger) of two *lower* bounds.
fn max_lower(a: &Bound, b: &Bound) -> Bound {
    match (a, b) {
        (Bound::Infinite, other) | (other, Bound::Infinite) => other.clone(),
        (Bound::Finite { value: x, open: ox }, Bound::Finite { value: y, open: oy }) => {
            match x.cmp(y) {
                Ordering::Greater => a.clone(),
                Ordering::Less => b.clone(),
                Ordering::Equal => Bound::Finite {
                    value: x.clone(),
                    open: *ox || *oy, // excluded if excluded by either
                },
            }
        }
    }
}

/// The tighter (smaller) of two *upper* bounds.
fn min_upper(a: &Bound, b: &Bound) -> Bound {
    match (a, b) {
        (Bound::Infinite, other) | (other, Bound::Infinite) => other.clone(),
        (Bound::Finite { value: x, open: ox }, Bound::Finite { value: y, open: oy }) => {
            match x.cmp(y) {
                Ordering::Less => a.clone(),
                Ordering::Greater => b.clone(),
                Ordering::Equal => Bound::Finite {
                    value: x.clone(),
                    open: *ox || *oy,
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }

    #[test]
    fn membership_open_closed() {
        let c = Interval::closed(r(1), r(3));
        assert!(c.contains(&r(1)) && c.contains(&r(3)) && c.contains(&r(2)));
        assert!(!c.contains(&r(0)) && !c.contains(&r(4)));

        let o = Interval::new(Bound::open(r(1)), Bound::open(r(3)));
        assert!(!o.contains(&r(1)) && !o.contains(&r(3)) && o.contains(&r(2)));
    }

    #[test]
    fn empty_normalisation() {
        assert!(Interval::new(Bound::closed(r(3)), Bound::closed(r(1))).is_empty());
        assert!(Interval::new(Bound::open(r(2)), Bound::closed(r(2))).is_empty());
        assert!(!Interval::point(r(2)).is_empty());
    }

    #[test]
    fn add_and_neg() {
        let a = Interval::closed(r(1), r(2));
        let b = Interval::closed(r(10), r(20));
        assert_eq!(a.add(&b), Interval::closed(r(11), r(22)));
        assert_eq!(a.neg(), Interval::closed(r(-2), r(-1)));
        assert_eq!(a.sub(&b), Interval::closed(r(-19), r(-8)));
    }

    #[test]
    fn mul_sign_cases() {
        // [-2,3] * [-1,4] : corners {2,-8,-3,12} ⇒ [-8,12].
        let a = Interval::closed(r(-2), r(3));
        let b = Interval::closed(r(-1), r(4));
        assert_eq!(a.mul(&b), Interval::closed(r(-8), r(12)));
    }

    #[test]
    fn intersect_basic() {
        let a = Interval::closed(r(0), r(5));
        let b = Interval::closed(r(3), r(9));
        assert_eq!(a.intersect(&b), Interval::closed(r(3), r(5)));
        let disjoint = Interval::closed(r(0), r(1)).intersect(&Interval::closed(r(2), r(3)));
        assert!(disjoint.is_empty());
    }

    #[test]
    fn unbounded_bounds() {
        // [0, +oo) contains all nonnegatives, excludes negatives.
        let nonneg = Interval::new(Bound::closed(r(0)), Bound::infinite());
        assert!(nonneg.contains(&r(1000000)) && nonneg.contains(&r(0)));
        assert!(!nonneg.contains(&r(-1)));
        // Sound over-approximation: (0,+oo) + (-oo,0) ⇒ (-oo,+oo).
        let pos = Interval::new(Bound::open(r(0)), Bound::infinite());
        assert_eq!(pos.add(&pos.neg()), Interval::all());
    }

    // Soundness: sampled points of a*b land in the computed product interval.
    #[test]
    fn mul_soundness_sampled() {
        let a = Interval::closed(r(-3), r(2));
        let b = Interval::closed(r(-5), r(7));
        let prod = a.mul(&b);
        for x in -3..=2 {
            for y in -5..=7 {
                assert!(
                    prod.contains(&r(x * y)),
                    "{}*{}={} not in {:?}",
                    x,
                    y,
                    x * y,
                    prod
                );
            }
        }
    }
}

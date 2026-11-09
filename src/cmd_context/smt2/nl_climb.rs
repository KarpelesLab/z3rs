//! z3's optimizer on one real objective `x` bounded by one power,
//! `x^k ≤ U` (or `< U`), when the exact nonlinear procedures are off
//! (`opt.optsmt_nlsat false`) or leave an open limit uncertified.
//!
//! z3's `optsmt::geometric_search` climbs over the models `theory_lra`
//! returns; `x · … · x` is a monomial column `m` of its `lar_solver`, kept
//! equal to `x^k` by `nla_core`. The numbers z3 reports follow from that
//! machinery step by step:
//!
//! * **Climb.** Each round asserts the blocker `x > v` and the arithmetic
//!   solver moves `x` onto the strict bound `(v, +ε)`. The monomial column
//!   carries the bounds `(v^k, +ε)` (nla's monomial bounds) and the
//!   asserted `U` (`(U, −ε)` when strict), so `find_delta_for_strict_bounds`
//!   picks `δ = min(1, (U − v^k)/(1 − y_U))` and the model is `x = v + δ`.
//!   While `v + δ` satisfies the bound the patcher sets `m := x^k` and the
//!   climb goes on.
//! * **Cuts.** At the first `w = v + δ` past the root `r = U^{1/k}`,
//!   `nra_solver::check_assignment` refutes the point with the cell bound
//!   `x ≤ c`, `c` the upper end of `r`'s isolating interval bisected until
//!   below the current LP value of `x`; the LP then sits at `c` and the next
//!   check cuts again. `m_check_assignment_fail_cnt` is never reset and
//!   `arith.nl.nra_check_assignment_max_fail` is 7, so seven cuts are made,
//!   the last one `c₇`.
//! * **nlsat.** nla then calls nlsat on the whole problem, whose model is
//!   the simplest dyadic in the cell `(v, r)` (`select`); that is the
//!   lower bound `s` z3 continues from.
//! * **Bound.** Maximizing the LP under the cuts gives `c₇`, refuted as a
//!   blocker but kept as the dual upper bound, and nla adds the order lemma
//!   `x < c₇ ∨ m − c₇·x ≥ 0` (squares) and the monotonicity lemma
//!   `x < c₇ ∨ m ≥ c₇^k`, which the core satisfies with `x < c₇` and the
//!   negated other literals.
//! * **Bisection.** `optsmt::bisect` then alternates `x > lo` and
//!   `x ≥ (lo + hi)/2` over `[s, c₇]`. Each probe moves `x` (and `m`) to
//!   its new lower bound when below it, takes the concrete point for the
//!   least `δ` of all strict bounds, and patches `m := x^k` when that stays
//!   within `m`'s bounds (an LP model); otherwise nlsat answers with
//!   `select` in the probe's cell. A probe whose `m` lower bound passes `U`
//!   is infeasible.
//!
//! Minimizing an even power is the mirror image (z3 maximizes `−x`).
//! Everything outside this pattern (a rational root below the strict
//! bound, `U` too small for the climb to start at `x = 1`, a climb that
//! never overshoots) is left to the caller's general procedures.

use alloc::vec::Vec;
use puremp::{Int, Rational};

/// `x^k ≤ U` (`< U` when `strict`), `k ≥ 2`, `U > 0`.
#[derive(Clone, Debug)]
pub(super) struct Power {
    pub k: u32,
    pub u: Rational,
    pub strict: bool,
}

/// What z3's optimizer reports for the maximum of `x`.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Outcome {
    /// Attained (and proven) optimum.
    Optimum(Rational),
    /// `unknown` with the proven bracket `[lo, hi]` (lo attained).
    Interval(Rational, Rational),
}

/// Where the climb leaves z3's search: the incumbent `start` (nlsat's model
/// after the cuts), the last cut `cut` (the dual upper bound) and the value
/// the monomial column holds.
#[derive(Clone, Debug)]
pub(super) struct Climb {
    pub start: Rational,
    pub cut: Rational,
    mono: Rational,
    /// nla's order lemma `x < c ∨ m − c·x ≥ 0` is in the LP (squares
    /// refuted by cuts).
    order_lemma: bool,
    /// Rounds the climb's LP models advanced before the cuts (`None` for
    /// the climb below a rational root).
    steps: Option<usize>,
}

/// An `inf_rational` value `x + y·ε`.
type Impq = (Rational, Rational);

const CHECK_ASSIGNMENT_MAX_FAIL: usize = 7;
const MAX_CLIMB_ROUNDS: usize = 64;
const MAX_CLIMB_BITS: u32 = 4096;

impl Climb {
    /// The climb below a rational root of a strict bound, whose LP bound
    /// `x < r` is no lemma: side constraints leave its bisection unchanged.
    pub fn below_rational_root(&self) -> bool {
        self.steps.is_none()
    }
}

impl Power {
    fn one() -> Rational {
        Rational::from_integer(Int::from(1))
    }

    /// `q^k` holds the bound.
    fn holds(&self, q: &Rational) -> bool {
        let p = q.pow(self.k as i32);
        if self.strict { p < self.u } else { p <= self.u }
    }

    /// `0 < q < r`.
    fn below_root(&self, q: &Rational) -> bool {
        q.pow(self.k as i32) < self.u
    }

    /// `ε` coefficient of the bound `U`.
    fn y_u(&self) -> Rational {
        if self.strict {
            Rational::from_integer(Int::from(-1))
        } else {
            Rational::from_integer(Int::from(0))
        }
    }

    /// `(⌊r·2^j⌋ + 1)/2^j`: the upper end of the dyadic interval of width
    /// `2^-j` around the (irrational) root.
    fn dyadic_upper(&self, j: u32) -> Rational {
        let s = Rational::power_of_two((j * self.k) as i32);
        let n = self.u.mul(&s).floor().root(self.k as u64);
        Rational::new(n.add(&Int::from(1)), Int::from(1)).div(&Rational::power_of_two(j as i32))
    }

    /// The rational root, if `U` is a `k`-th power.
    fn rational_root(&self) -> Option<Rational> {
        let (a, b) = (self.u.numerator(), self.u.denominator());
        let (ra, rb) = (a.root(self.k as u64), b.root(self.k as u64));
        (ra.pow(self.k as u64) == *a && rb.pow(self.k as u64) == *b).then(|| Rational::new(ra, rb))
    }

    /// nlsat's sample in the cell `(v, r)`: the dyadic `n/2^j` with the
    /// least `j` strictly between, the least such `n`.
    fn select_below(&self, v: &Rational) -> Rational {
        for j in 0i32.. {
            let s = Rational::power_of_two(j);
            let n = v.mul(&s).floor().add(&Int::from(1));
            let c = Rational::new(n, Int::from(1)).div(&s);
            if self.below_root(&c) {
                return c;
            }
        }
        unreachable!("a dyadic lies strictly between distinct reals")
    }

    /// The climb up to the bisection, or the optimum when the climb itself
    /// proves it (`None` outside the modelled pattern).
    pub fn climb(&self) -> Option<Result<Climb, Rational>> {
        let one = Self::one();
        let yu = self.y_u();
        let denom = one.sub(&yu);
        let root = self.rational_root();
        if let (Some(r), true) = (&root, self.strict) {
            return self.climb_to_rational(r);
        }
        // The first model after `x = 0`: x moves onto `(0, +ε)`. An even
        // power's column still holds 1 from the round's `x = −1`, an odd
        // one is pushed onto its lower bound `(0, +ε)`.
        let mut v = if self.k.is_multiple_of(2) {
            if self.u < one || (self.strict && self.u == one) {
                return None;
            }
            if self.strict {
                one.clone().min(self.u.sub(&one))
            } else {
                one.clone()
            }
        } else {
            if !self.u.is_positive() {
                return None;
            }
            one.clone().min(self.u.div(&denom))
        };
        let mut rounds = 0;
        let w = loop {
            rounds += 1;
            // A climb converging below the root never overshoots, its
            // denominators growing as the k-th power each round.
            if rounds > MAX_CLIMB_ROUNDS || v.denominator().bit_len() > MAX_CLIMB_BITS {
                return None;
            }
            let vk = v.pow(self.k as i32);
            if vk >= self.u {
                // `(v^k, +ε)` against `U`: no model above v.
                return Some(Err(v));
            }
            let d = one.clone().min(self.u.sub(&vk).div(&denom));
            let w = v.add(&d);
            if !self.holds(&w) {
                break w;
            }
            v = w;
        };
        if let Some(r) = root {
            // The cell bound is the root itself; the LP attains it.
            return Some(Err(r));
        }
        let mut cut = w;
        let mut cuts = 0;
        for j in 0u32.. {
            if cuts == CHECK_ASSIGNMENT_MAX_FAIL {
                break;
            }
            let c = self.dyadic_upper(j);
            if c < cut {
                cut = c;
                cuts += 1;
            }
        }
        let start = self.select_below(&v);
        // The column last took a concrete value while `x` sat at the last
        // cut: `(U, y_U)` at the least δ of `x ∈ ((v, +ε), c₇]` and
        // `m ∈ ((v^k, +ε), (U, y_U))`.
        let d0 = one
            .min(cut.sub(&v))
            .min(self.u.sub(&v.pow(self.k as i32)).div(&denom));
        let mono = self.u.add(&yu.mul(&d0));
        Some(Ok(Climb {
            start,
            cut,
            mono,
            order_lemma: self.k == 2,
            steps: Some(rounds - 1),
        }))
    }

    /// The climb below a rational root `r` of a strict bound: nla's
    /// monomial bounds give the LP `x < r` from the start, so the LP
    /// maximum is `(r, −ε)` and the climb runs on its concrete points. The
    /// first model takes `x` from the round's `−1` onto `(0, +ε)`, below
    /// `(r, −ε)` and with the column at 1 under `(U, −ε)`; each further round
    /// demands `x ≥ v + 1` (the maximum `r − ε` is refuted as a blocker) and
    /// the LP's maximum point is concrete at the least δ of
    /// `x ∈ [v + 1, (r, −ε))`. The bisection then starts from the last model
    /// below `r`.
    fn climb_to_rational(&self, r: &Rational) -> Option<Result<Climb, Rational>> {
        let one = Self::one();
        if *r < one {
            return None;
        }
        let two = Rational::from_integer(Int::from(2));
        let mut v = one.clone().min(r.div(&two));
        if self.k.is_multiple_of(2) && *r > one {
            v = v.min(self.u.sub(&one));
        }
        loop {
            let b = v.add(&one);
            if b >= *r {
                break;
            }
            v = b.max(r.sub(&one));
        }
        Some(Ok(Climb {
            mono: v.pow(self.k as i32),
            start: v,
            cut: r.clone(),
            order_lemma: false,
            steps: None,
        }))
    }

    /// `optsmt::bisect` over `[climb.start, climb.cut]` for `rounds` rounds.
    pub fn bisect(&self, climb: &Climb, rounds: usize) -> Option<Outcome> {
        let zero = Rational::from_integer(Int::from(0));
        let one = Self::one();
        let minus_one = one.neg();
        let c = climb.cut.clone();
        let kk = self.k as i32;
        let x_upper: Impq = (c.clone(), minus_one.clone());
        let m_upper: Impq = (self.u.clone(), self.y_u());
        let mut x: Impq = x_upper.clone();
        let mut m: Impq = (climb.mono.clone(), zero.clone());
        let (mut lo, mut hi) = (climb.start.clone(), c.clone());
        let two = Rational::from_integer(Int::from(2));
        let mut strict = true;
        for _ in 0..rounds {
            if lo >= hi {
                break;
            }
            let (b, by) = if strict {
                (lo.clone(), one.clone())
            } else {
                (lo.add(&hi).div(&two), zero.clone())
            };
            let x_lower: Impq = (b.clone(), by.clone());
            let m_lower: Impq = (b.pow(kk), by.clone());
            // m's bounds cross: the probe is infeasible.
            let crossed = m_lower.0 > m_upper.0
                || (m_lower.0 == m_upper.0 && (by.is_positive() || self.strict));
            let model = if crossed {
                None
            } else {
                if impq_lt(&x, &x_lower) {
                    x = x_lower.clone();
                }
                if impq_lt(&m, &m_lower) {
                    m = m_lower.clone();
                }
                // The order lemma's row `t = m − c·x < 0` (squares only).
                let t = || -> Impq { (m.0.sub(&c.mul(&x.0)), m.1.sub(&c.mul(&x.1))) };
                let t_upper: Impq = (zero.clone(), minus_one.clone());
                if climb.order_lemma && impq_lt(&t_upper, &t()) {
                    // A pivot this model does not follow.
                    return None;
                }
                let mut delta = one.clone();
                update_delta(&mut delta, &x_lower, &x);
                update_delta(&mut delta, &x, &x_upper);
                update_delta(&mut delta, &m_lower, &m);
                update_delta(&mut delta, &m, &m_upper);
                if climb.order_lemma {
                    update_delta(&mut delta, &t(), &t_upper);
                }
                let xv = x.0.add(&delta.mul(&x.1));
                let mv = m.0.add(&delta.mul(&m.1));
                x = (xv.clone(), zero.clone());
                if self.holds(&xv) {
                    // The patcher makes `m = x^k`: an LP model.
                    m = (xv.pow(kk), zero.clone());
                    Some(xv)
                } else {
                    m = (mv, zero.clone());
                    // nlsat's model in the probe's cell below the root.
                    Some(self.select_below(&b))
                }
            };
            match model {
                None if strict => return Some(Outcome::Optimum(lo)),
                None => hi = b,
                Some(q) => {
                    if q > lo {
                        lo = q;
                    }
                }
            }
            strict = !strict;
        }
        Some(if lo >= hi {
            Outcome::Optimum(lo)
        } else {
            Outcome::Interval(lo, hi)
        })
    }

    /// `optsmt::bisect` over `[climb.start, climb.cut]` when side constraints
    /// over uninterpreted functions are asserted too.
    ///
    /// Model-based theory combination then makes the search decide above the
    /// base level, so the climb's cuts and lemmas are popped with the trial
    /// scopes and each probe starts from the base LP: `x` bounded below by
    /// the probe alone, the column `m = x^k` between nla's monomial bound and
    /// `U`. Lemmas a probe learns live until its scope is popped. Each final
    /// check of a probe is one `nla_core::check`:
    ///
    /// * the concrete point of the least `δ` of all strict bounds; an
    ///   assignment with `m = x^k` is a model, and so is one whose `x^k` lies
    ///   within `m`'s bounds (the patcher sets `m := x^k`);
    /// * the bound squeeze (`optimize_nl_bounds`) while it is eager (fewer
    ///   than three fruitless squeezes, one left from the climb; never when
    ///   minimizing, where the objective is the term `−x`) or every fourth
    ///   call: `m` moves to its upper bound and `x` to its upper bound
    ///   if a lemma gave one, else to its lower bound;
    /// * `bounded_nlsat` when its backoff allows (the climb's run left the
    ///   delay at 4, each cheap run halves its bound): nlsat's model is the
    ///   simplest dyadic in the cell `(b, r)`;
    /// * otherwise an order or monotonicity lemma, which the core satisfies
    ///   with `x < x₀` at the current value `x₀`: each kind once per scope
    ///   (nla's throttle), the order lemma for squares only, neither over
    ///   values past machine integers (a call without a lemma changes
    ///   nothing).
    ///
    /// nla's calls count from the climb: 20 plus 5 per LP round the climb
    /// advanced before its cuts.
    pub fn bisect_uf(&self, climb: &Climb, rounds: usize, minimize: bool) -> Option<Outcome> {
        let steps = climb.steps?;
        let zero = Rational::from_integer(Int::from(0));
        let one = Self::one();
        let minus_one = one.neg();
        let kk = self.k as i32;
        let m_upper: Impq = (self.u.clone(), self.y_u());
        let mut calls = 20 + 5 * steps;
        let (mut delay, mut delay_bound) = (4u32, 5u32);
        let mut squeeze_fails = if minimize { 3 } else { 1 };
        // The climb's last trial `x ≥ lo + 1` left x there and m at U.
        let mut x: Impq = (climb.start.add(&one), zero.clone());
        let mut m: Impq = m_upper.clone();
        let (mut lo, mut hi) = (climb.start.clone(), climb.cut.clone());
        let two = Rational::from_integer(Int::from(2));
        let mut strict = true;
        for _ in 0..rounds {
            if lo >= hi {
                break;
            }
            let (b, by) = if strict {
                (lo.clone(), one.clone())
            } else {
                (lo.add(&hi).div(&two), zero.clone())
            };
            let x_lower: Impq = (b.clone(), by.clone());
            let m_lower: Impq = (b.pow(kk), by.clone());
            let crossed = m_lower.0 > m_upper.0
                || (m_lower.0 == m_upper.0 && (by.is_positive() || self.strict));
            let mut model = None;
            if !crossed {
                if impq_lt(&x, &x_lower) {
                    x = x_lower.clone();
                }
                if impq_lt(&m, &m_lower) {
                    m = m_lower.clone();
                }
                let mut x_upper: Option<Impq> = None;
                let (mut order_left, mut monotone_left) = (true, true);
                // Points of the order lemmas, whose rows `m − x₀·x < 0` the
                // LP keeps.
                let mut order_rows: Vec<Rational> = Vec::new();
                let t_upper: Impq = (zero.clone(), minus_one.clone());
                let concrete =
                    |x: &mut Impq, m: &mut Impq, x_upper: &Option<Impq>, rows: &[Rational]| {
                        let mut delta = one.clone();
                        update_delta(&mut delta, &x_lower, x);
                        if let Some(u) = x_upper {
                            update_delta(&mut delta, x, u);
                        }
                        update_delta(&mut delta, &m_lower, m);
                        update_delta(&mut delta, m, &m_upper);
                        for x0 in rows {
                            let t: Impq = (m.0.sub(&x0.mul(&x.0)), m.1.sub(&x0.mul(&x.1)));
                            update_delta(&mut delta, &t, &t_upper);
                        }
                        *x = (x.0.add(&delta.mul(&x.1)), zero.clone());
                        *m = (m.0.add(&delta.mul(&m.1)), zero.clone());
                    };
                loop {
                    calls += 1;
                    if calls > 100_000 {
                        return None;
                    }
                    concrete(&mut x, &mut m, &x_upper, &order_rows);
                    let xk: Impq = (x.0.pow(kk), zero.clone());
                    if xk.0 == m.0 {
                        model = Some(x.0.clone());
                        break;
                    }
                    if !impq_lt(&xk, &m_lower) && !impq_lt(&m_upper, &xk) {
                        m = xk;
                        model = Some(x.0.clone());
                        break;
                    }
                    if squeeze_fails < 3 || calls.is_multiple_of(4) {
                        squeeze_fails += 1;
                        x = x_upper.clone().unwrap_or_else(|| x_lower.clone());
                        m = m_upper.clone();
                        concrete(&mut x, &mut m, &x_upper, &order_rows);
                        if x.0.pow(kk) == m.0 {
                            model = Some(x.0.clone());
                            break;
                        }
                    }
                    delay = delay.saturating_sub(1);
                    if delay < 2 {
                        delay_bound /= 2;
                        delay = delay_bound;
                        model = Some(self.select_below(&b));
                        break;
                    }
                    if self.k == 2 && order_left && is_small(&x.0) {
                        order_left = false;
                        order_rows.push(x.0.clone());
                    } else if monotone_left && is_small(&x.0) && is_small(&m.0) {
                        monotone_left = false;
                    } else {
                        continue;
                    }
                    let u: Impq = (x.0.clone(), minus_one.clone());
                    x = u.clone();
                    x_upper = Some(u);
                }
            }
            match model {
                None if strict => return Some(Outcome::Optimum(lo)),
                None => hi = b,
                Some(q) => {
                    if q > lo {
                        lo = q;
                    }
                }
            }
            strict = !strict;
        }
        Some(if lo >= hi {
            Outcome::Optimum(lo)
        } else {
            Outcome::Interval(lo, hi)
        })
    }
}

/// z3's `rational::is_small`: numerator and denominator fit in an `int`.
fn is_small(q: &Rational) -> bool {
    let lim = Int::from(i32::MAX as i64);
    q.numerator().abs() <= lim && *q.denominator() <= lim
}

fn impq_lt(a: &Impq, b: &Impq) -> bool {
    a.0 < b.0 || (a.0 == b.0 && a.1 < b.1)
}

/// `lar_core_solver::update_delta`: shrink `delta` so that
/// `l.x + δ·l.y ≤ u.x + δ·u.y`.
fn update_delta(delta: &mut Rational, l: &Impq, u: &Impq) {
    if l.0 < u.0 && l.1 > u.1 {
        let d = u.0.sub(&l.0).div(&l.1.sub(&u.1));
        if d < *delta {
            *delta = d;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64, d: i64) -> Rational {
        Rational::new(Int::from(n), Int::from(d))
    }

    fn power(k: u32, u: Rational, strict: bool) -> Power {
        Power { k, u, strict }
    }

    #[test]
    fn square_root_two() {
        // opt_nlsat_disabled: x*x <= 2, 8 bisection rounds.
        let p = power(2, r(2, 1), false);
        let cl = p.climb().unwrap().unwrap();
        assert_eq!(cl.start, r(5, 4));
        assert_eq!(cl.cut, r(2897, 2048));
        assert_eq!(
            p.bisect(&cl, 8),
            Some(Outcome::Interval(
                r(185363, 131072),
                r(229157189, 162037760)
            ))
        );
        // x*x < 2: the climb moves by 1/2, the same incumbent, one more cut.
        let p = power(2, r(2, 1), true);
        let cl = p.climb().unwrap().unwrap();
        assert_eq!(cl.start, r(5, 4));
        assert_eq!(cl.cut, r(5793, 4096));
    }

    #[test]
    fn uninterpreted_side_constraint() {
        // opt_nlsat_uf_fallback: x*x <= 2 next to (f x) <= 5, 64 rounds.
        let p = power(2, r(2, 1), false);
        let cl = p.climb().unwrap().unwrap();
        let big = |s: &str| Int::from_str_radix(s, 10).unwrap();
        assert_eq!(
            p.bisect_uf(&cl, 64, false),
            Some(Outcome::Interval(
                Rational::new(big("208701085205324515397"), big("147573952589676412928")),
                Rational::new(big("417402170410709805943"), big("295147905179352825856"))
            ))
        );
        // Minimizing: no eager squeeze, the lemmas start from lo + 1.
        assert_eq!(
            p.bisect_uf(&cl, 8, true),
            Some(Outcome::Interval(r(92681, 65536), r(185365, 131072)))
        );
        // x^3 < 4: only the monotonicity lemma applies to a cube.
        let p = power(3, r(4, 1), true);
        let cl = p.climb().unwrap().unwrap();
        assert_eq!(
            p.bisect_uf(&cl, 8, false),
            Some(Outcome::Interval(r(13003, 8192), r(1664511, 1048576)))
        );
    }

    #[test]
    fn cube_and_attained() {
        let p = power(3, r(3, 1), true);
        let cl = p.climb().unwrap().unwrap();
        assert_eq!(
            p.bisect(&cl, 8),
            Some(Outcome::Interval(r(3023065, 2097152), r(11815, 8192)))
        );
        assert_eq!(
            power(2, r(1, 1), false).climb().unwrap().unwrap_err(),
            r(1, 1)
        );
        // x*x < 4: the LP bounds x below 2 from the start.
        let p = power(2, r(4, 1), true);
        let cl = p.climb().unwrap().unwrap();
        assert_eq!((cl.start.clone(), cl.cut.clone()), (r(1, 1), r(2, 1)));
        assert_eq!(
            p.bisect(&cl, 8),
            Some(Outcome::Interval(r(511, 256), r(2, 1)))
        );
    }
}

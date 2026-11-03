//! Ultimately periodic abstraction of a set of word lengths — a port of
//! z3's `util/len_abs.{h,cpp}`.
//!
//! The value `{ n : lo ≤ n ≤ hi, (n mod period) ∈ residues }` over-approximates
//! the length set `Λ(L) = { |w| : w ∈ L }` of a regular language: every
//! operation may lose precision, never soundness. The regex `info` carries it,
//! and a membership whose string length cannot reach any residue is refuted
//! (`seq_util::can_be_member`).

/// The largest period: residues are a 64-bit mask.
pub const MAX_PERIOD: u32 = 64;

/// An over-approximation of a set of word lengths (z3's `len_abs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LenAbs {
    lo: u32,
    hi: u32,
    period: u32,
    residues: u64,
}

/// All residues modulo `q`.
fn full_mask(q: u32) -> u64 {
    if q >= MAX_PERIOD { !0 } else { (1u64 << q) - 1 }
}

fn gcd(a: u32, b: u32) -> u32 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// The lcm of two effective periods (0 is the identity), or 0 when it
/// exceeds [`MAX_PERIOD`].
fn bounded_lcm(a: u32, b: u32) -> u32 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let l = u64::from(a / gcd(a, b)) * u64::from(b);
    if l > u64::from(MAX_PERIOD) {
        0
    } else {
        l as u32
    }
}

/// A common modulus: the lcm when it stays within [`MAX_PERIOD`], else the gcd.
fn common_period(a: u32, b: u32) -> u32 {
    let mut q = bounded_lcm(a, b);
    if q == 0 {
        q = gcd(a, b);
    }
    if q == 0 { 1 } else { q }
}

/// z3's `add_truncate`.
fn add_truncate(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

/// z3's `mul_truncate`.
fn mul_truncate(a: u32, b: u32) -> u32 {
    a.saturating_mul(b)
}

impl LenAbs {
    /// The trivial value, which constrains nothing.
    pub const TOP: LenAbs = LenAbs::bounds(0, u32::MAX);

    /// The lengths in `[lo, hi]`.
    pub const fn bounds(lo: u32, hi: u32) -> LenAbs {
        LenAbs {
            lo,
            hi,
            period: 1,
            residues: 1,
        }
    }

    /// The least length.
    pub fn lo(&self) -> u32 {
        self.lo
    }

    /// The abstraction's period.
    pub fn period(&self) -> u32 {
        self.period
    }

    /// Is the abstracted set empty (which certifies the language is)?
    pub fn is_empty(&self) -> bool {
        if self.lo > self.hi || self.residues == 0 {
            return true;
        }
        if self.period <= 1 {
            return false;
        }
        if self.hi == u32::MAX || self.hi - self.lo >= self.period - 1 {
            return false;
        }
        !(self.lo..=self.hi).any(|n| self.residues & (1u64 << (n % self.period)) != 0)
    }

    /// The residues modulo `q`, over-approximated, as a mask over `[0, q)`.
    fn residues_mod(&self, q: u32) -> u64 {
        if q == 0 || self.is_empty() {
            return 0;
        }
        if q >= MAX_PERIOD {
            return full_mask(q);
        }
        let mut res = 0u64;
        if self.hi != u32::MAX && self.hi - self.lo < MAX_PERIOD {
            for n in self.lo..=self.hi {
                if self.residues & (1u64 << (n % self.period)) != 0 {
                    res |= 1u64 << (n % q);
                }
            }
            return res;
        }
        if q <= self.period && self.period.is_multiple_of(q) {
            for r in 0..self.period {
                if self.residues & (1u64 << r) != 0 {
                    res |= 1u64 << (r % q);
                }
            }
            return res;
        }
        if q > self.period && q.is_multiple_of(self.period) {
            for r in 0..self.period {
                if self.residues & (1u64 << r) != 0 {
                    let mut t = r;
                    while t < q {
                        res |= 1u64 << t;
                        t += self.period;
                    }
                }
            }
            return res;
        }
        full_mask(q)
    }

    /// The gcd of the abstracted set (0 when it is empty or `{0}`).
    fn gcd(&self) -> u32 {
        if self.is_empty() {
            return 0;
        }
        let mut g = 0;
        let span = if self.period > (u32::MAX - self.lo) / 2 {
            u32::MAX
        } else {
            self.lo + 2 * self.period
        };
        let hi = self.hi.min(span);
        let mut n = self.lo;
        loop {
            if self.residues & (1u64 << (n % self.period)) != 0 {
                g = gcd(g, n);
            }
            if g == 1 {
                return 1;
            }
            if n >= hi {
                break;
            }
            n += 1;
        }
        if self.hi == u32::MAX {
            g = gcd(g, self.period);
        }
        g
    }

    /// The period to combine with (0: a set of at most one element adapts).
    fn eff_period(&self) -> u32 {
        if self.lo == self.hi { 0 } else { self.period }
    }

    /// Lengths of a concatenation: pointwise sums.
    pub fn concat(&self, other: &LenAbs) -> LenAbs {
        let mut r = LenAbs::bounds(
            add_truncate(self.lo, other.lo),
            add_truncate(self.hi, other.hi),
        );
        let g = gcd(self.eff_period(), other.eff_period());
        if g > 1 {
            let (a, b) = (self.residues_mod(g), other.residues_mod(g));
            let mut res = 0u64;
            for i in 0..g {
                if a & (1u64 << i) == 0 {
                    continue;
                }
                for j in 0..g {
                    if b & (1u64 << j) != 0 {
                        res |= 1u64 << ((i + j) % g);
                    }
                }
            }
            r.period = g;
            r.residues = res;
        }
        r
    }

    /// Lengths of a union.
    pub fn unite(&self, other: &LenAbs) -> LenAbs {
        let mut r = LenAbs::bounds(self.lo.min(other.lo), self.hi.max(other.hi));
        let q = common_period(self.eff_period(), other.eff_period());
        if q > 1 {
            r.period = q;
            r.residues = self.residues_mod(q) | other.residues_mod(q);
        }
        r
    }

    /// A set contained in both (sound for an intersection).
    pub fn meet(&self, other: &LenAbs) -> LenAbs {
        let mut r = LenAbs::bounds(self.lo.max(other.lo), self.hi.min(other.hi));
        let q = common_period(self.eff_period(), other.eff_period());
        if q > 1 {
            r.period = q;
            r.residues = self.residues_mod(q) & other.residues_mod(q);
        }
        r
    }

    /// The multiples of the gcd, from `lo` (shared by star and plus).
    fn repeat(&self, lo: u32) -> LenAbs {
        let mut r = LenAbs::bounds(lo, if self.hi == 0 { 0 } else { u32::MAX });
        let g = self.gcd();
        if g > 1 && g <= MAX_PERIOD {
            r.period = g;
            r.residues = 1;
        }
        r
    }

    /// Lengths of a Kleene star.
    pub fn star(&self) -> LenAbs {
        self.repeat(0)
    }

    /// Lengths of a Kleene plus.
    pub fn plus(&self) -> LenAbs {
        self.repeat(self.lo)
    }

    /// Lengths of an option: also 0.
    pub fn opt(&self) -> LenAbs {
        LenAbs {
            lo: 0,
            hi: self.hi,
            period: self.period,
            residues: self.residues | 1,
        }
    }

    /// Lengths of `lower` to `upper` repetitions.
    pub fn repeat_range(&self, lower: u32, upper: u32) -> LenAbs {
        let mut r = LenAbs::bounds(mul_truncate(self.lo, lower), mul_truncate(self.hi, upper));
        if upper == u32::MAX || upper > MAX_PERIOD {
            let g = self.gcd();
            if g > 1 && g <= MAX_PERIOD {
                r.period = g;
                r.residues = 1;
            }
        } else {
            let q = if self.period > 1 {
                self.period
            } else {
                self.gcd()
            };
            if q > 1 && q <= MAX_PERIOD {
                let base = self.residues_mod(q);
                let (mut acc, mut cur) = (0u64, 1u64);
                for k in 0..=upper {
                    if k >= lower {
                        acc |= cur;
                    }
                    let mut next = 0u64;
                    for i in 0..q {
                        if cur & (1u64 << i) == 0 {
                            continue;
                        }
                        for j in 0..q {
                            if base & (1u64 << j) != 0 {
                                next |= 1u64 << ((i + j) % q);
                            }
                        }
                    }
                    cur = next;
                }
                r.period = q;
                r.residues = acc;
            }
        }
        r
    }

    /// Can a length `cst + g·k` (`k ≥ 0`) have one of the residues?
    pub fn residue_reachable(&self, cst: u32, g: u32) -> bool {
        let period = self.period;
        if period == 0 {
            return true;
        }
        let c = cst % period;
        let d = if g == 0 { period } else { gcd(g, period) };
        (0..period).any(|i| {
            self.residues & (1u64 << i) != 0
                && if g == 0 {
                    i == c
                } else {
                    (i + period - c).is_multiple_of(d)
                }
        })
    }
}

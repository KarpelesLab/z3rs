//! A deterministic work budget for the polynomial algorithms whose cost can
//! explode (subresultant sequences, elimination by resultants): z3 bounds
//! them with its resource limit (`rlimit`), checked inside their loops. A
//! [`Fuel`] is passed down explicitly; each step burns an estimate of the
//! work it did, and the computation gives up (returns `None`) once it is
//! spent.

use core::cell::Cell;

use crate::math::polynomial::Polynomial;

/// A work budget, shared by the computations it is passed to.
#[derive(Debug)]
pub struct Fuel {
    left: Cell<u64>,
}

impl Fuel {
    /// A budget of `n` work units.
    pub fn new(n: u64) -> Fuel {
        Fuel { left: Cell::new(n) }
    }

    /// No budget: never runs out.
    pub fn unlimited() -> Fuel {
        Fuel::new(u64::MAX)
    }

    /// Whether this budget never runs out.
    pub fn is_unlimited(&self) -> bool {
        self.left.get() == u64::MAX
    }

    /// Spend `n` units; `None` once the budget is exhausted.
    pub fn burn(&self, n: u64) -> Option<()> {
        let left = self.left.get();
        if left == u64::MAX {
            return Some(());
        }
        if left < n {
            self.left.set(0);
            return None;
        }
        self.left.set(left - n);
        Some(())
    }

    /// Spend the size of `p` (see [`size`]).
    pub fn burn_poly(&self, p: &Polynomial) -> Option<()> {
        if self.is_unlimited() {
            return Some(());
        }
        self.burn(size(p))
    }
}

/// The work of computing `p`: its size in 64-bit words (one per term, plus
/// its coefficient's) times the size of its largest coefficient, as
/// multiplying coefficients costs more than linear time in their size.
pub fn size(p: &Polynomial) -> u64 {
    let mut words = 0u64;
    let mut widest = 1u64;
    for (c, _) in p.terms() {
        let w = 1 + u64::from(c.numerator().bit_len() + c.denominator().bit_len()) / 64;
        words += w;
        widest = widest.max(w);
    }
    words.saturating_mul(widest)
}

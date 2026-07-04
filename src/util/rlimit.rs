//! Resource limit — a cooperative cancellation budget, mirroring Z3's
//! `rlimit` (`z3/src/util/rlimit.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! Z3 threads a shared `reslimit` through every long-running procedure; work is
//! charged against it at choice points, and once the limit is reached the
//! procedure bails out with a resource-out result. z3rs's theory checks already
//! thread explicit `u64` budgets (branch-and-bound depth, Fourier–Motzkin
//! resolvents, disequality splits, SAT conflicts) so that every check
//! terminates with a sound `unknown` on exhaustion; this type gives those
//! budgets a shared, resettable form with the same semantics.

/// A monotone work counter with an optional ceiling. A `limit` of `0` means
/// unlimited. Increment at choice points and stop once [`Rlimit::exhausted`].
#[derive(Clone, Debug, Default)]
pub struct Rlimit {
    count: u64,
    limit: u64,
}

impl Rlimit {
    /// An unlimited budget (nothing is ever exhausted).
    pub fn new() -> Self {
        Self::default()
    }

    /// A budget that is exhausted once `limit` units of work are charged.
    /// `limit == 0` is unlimited.
    pub fn with_limit(limit: u64) -> Self {
        Self { count: 0, limit }
    }

    /// Set (or clear, with `0`) the ceiling without resetting the count.
    pub fn set_limit(&mut self, limit: u64) {
        self.limit = limit;
    }

    /// The ceiling (`0` = unlimited).
    pub fn limit(&self) -> u64 {
        self.limit
    }

    /// Units charged so far.
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Has the budget been reached? Always `false` when unlimited.
    pub fn exhausted(&self) -> bool {
        self.limit != 0 && self.count >= self.limit
    }

    /// Charge one unit; returns `true` while there is budget left (i.e. not
    /// exhausted *after* the charge), so it reads well in a loop guard.
    pub fn inc(&mut self) -> bool {
        self.inc_by(1)
    }

    /// Charge `n` units (saturating); returns `true` while budget remains.
    pub fn inc_by(&mut self, n: u64) -> bool {
        self.count = self.count.saturating_add(n);
        !self.exhausted()
    }

    /// Reset the charged count to zero, keeping the ceiling.
    pub fn reset(&mut self) {
        self.count = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::Rlimit;

    #[test]
    fn unlimited_never_exhausts() {
        let mut r = Rlimit::new();
        for _ in 0..1000 {
            assert!(r.inc());
        }
        assert!(!r.exhausted());
        assert_eq!(r.count(), 1000);
    }

    #[test]
    fn limited_exhausts_at_ceiling() {
        let mut r = Rlimit::with_limit(3);
        assert!(r.inc()); // 1
        assert!(r.inc()); // 2
        assert!(!r.inc()); // 3 → reached
        assert!(r.exhausted());
        assert!(!r.inc()); // still exhausted
    }

    #[test]
    fn inc_by_and_reset() {
        let mut r = Rlimit::with_limit(10);
        assert!(r.inc_by(4));
        assert!(!r.inc_by(20)); // saturates past the limit
        assert!(r.exhausted());
        r.reset();
        assert!(!r.exhausted());
        assert_eq!(r.count(), 0);
    }
}

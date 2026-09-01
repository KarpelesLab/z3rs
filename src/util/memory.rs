//! Process memory accounting and an optional hard ceiling — a small analogue of
//! z3's memory manager (`z3/src/util/memory_manager.cpp`), which counts every
//! allocation so a runaway can be *capped* rather than exhausting the machine.
//!
//! The `z3rs` binary installs a global allocator that feeds [`try_alloc`] /
//! [`on_dealloc`] here; the solver consults [`over_soft_limit`] at its
//! resource-check points to bail out with a sound `unknown` before the hard
//! ceiling aborts the process. With no limit set (the default) this is a pair of
//! relaxed atomic counters and imposes no policy — behaviour is unchanged.

use core::sync::atomic::{AtomicUsize, Ordering};

static CURRENT: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
/// Hard ceiling in bytes; `0` = unlimited.
static HARD_LIMIT: AtomicUsize = AtomicUsize::new(0);

/// Charge `n` bytes. Returns `false` (and charges nothing) if the allocation
/// would push past the hard ceiling — the caller (the global allocator) must
/// then refuse the allocation, which makes the process abort cleanly at the cap
/// instead of consuming unbounded memory.
#[inline]
pub fn try_alloc(n: usize) -> bool {
    let lim = HARD_LIMIT.load(Ordering::Relaxed);
    let prev = CURRENT.fetch_add(n, Ordering::Relaxed);
    let now = prev.wrapping_add(n);
    if lim != 0 && now > lim {
        CURRENT.fetch_sub(n, Ordering::Relaxed);
        return false;
    }
    let mut peak = PEAK.load(Ordering::Relaxed);
    while now > peak {
        match PEAK.compare_exchange_weak(peak, now, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => break,
            Err(p) => peak = p,
        }
    }
    true
}

/// Release `n` bytes previously charged by [`try_alloc`].
#[inline]
pub fn on_dealloc(n: usize) {
    CURRENT.fetch_sub(n, Ordering::Relaxed);
}

/// Bytes currently allocated (as tracked by the global allocator).
pub fn current() -> usize {
    CURRENT.load(Ordering::Relaxed)
}

/// High-water mark of [`current`] since process start.
pub fn peak() -> usize {
    PEAK.load(Ordering::Relaxed)
}

/// The hard ceiling in bytes (`0` = unlimited).
pub fn hard_limit() -> usize {
    HARD_LIMIT.load(Ordering::Relaxed)
}

/// Set the hard ceiling in megabytes (`0` = unlimited).
pub fn set_limit_mb(mb: usize) {
    HARD_LIMIT.store(mb.saturating_mul(1024 * 1024), Ordering::Relaxed);
}

/// Whether current usage has crossed the *soft* limit (90 % of the hard
/// ceiling) — the point at which a cooperative check should return `unknown`,
/// leaving headroom to unwind before the allocator refuses an allocation. Always
/// `false` when unlimited, so it is inert unless a limit is set.
#[inline]
pub fn over_soft_limit() -> bool {
    let lim = HARD_LIMIT.load(Ordering::Relaxed);
    lim != 0 && CURRENT.load(Ordering::Relaxed) > lim / 10 * 9
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accounting_roundtrips_and_unlimited_never_caps() {
        set_limit_mb(0);
        let before = current();
        assert!(try_alloc(1024));
        assert_eq!(current(), before + 1024);
        on_dealloc(1024);
        assert_eq!(current(), before);
        assert!(!over_soft_limit());
    }
}

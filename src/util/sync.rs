//! Minimal synchronization primitives usable in `no_std`.
//!
//! Z3 guards its global symbol table (and a few other singletons) with a mutex.
//! In `no_std` we cannot use `std::sync::Mutex`, so this provides a tiny
//! `const`-constructible spinlock built only on `core::sync::atomic` — enough
//! for the low-contention, short-critical-section singletons z3rs needs. It is
//! not a general-purpose mutex (no poisoning, no fairness, no blocking).

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicBool, Ordering};

/// A small spinlock. `const`-constructible so it can back a `static`.
pub struct SpinLock<T> {
    locked: AtomicBool,
    value: UnsafeCell<T>,
}

// Safe to share across threads: access to `value` is serialized by `locked`.
unsafe impl<T: Send> Sync for SpinLock<T> {}
unsafe impl<T: Send> Send for SpinLock<T> {}

impl<T> SpinLock<T> {
    /// Create a new spinlock (usable in a `const`/`static` initializer).
    pub const fn new(value: T) -> Self {
        SpinLock {
            locked: AtomicBool::new(false),
            value: UnsafeCell::new(value),
        }
    }

    /// Acquire the lock, spinning until it is free. Returns a guard that
    /// releases the lock on drop.
    pub fn lock(&self) -> SpinGuard<'_, T> {
        while self
            .locked
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            // Spin until the lock looks free before retrying the CAS.
            while self.locked.load(Ordering::Relaxed) {
                core::hint::spin_loop();
            }
        }
        SpinGuard { lock: self }
    }
}

/// RAII guard for [`SpinLock`]; releases the lock when dropped.
pub struct SpinGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> Deref for SpinGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // Safety: we hold the lock, so we have exclusive access.
        unsafe { &*self.lock.value.get() }
    }
}

impl<T> DerefMut for SpinGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // Safety: we hold the lock, so we have exclusive access.
        unsafe { &mut *self.lock.value.get() }
    }
}

impl<T> Drop for SpinGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lock_gives_mutable_access() {
        let lock = SpinLock::new(0u32);
        {
            let mut g = lock.lock();
            *g += 41;
            *g += 1;
        }
        assert_eq!(*lock.lock(), 42);
    }

    #[test]
    fn usable_as_static() {
        static COUNTER: SpinLock<u32> = SpinLock::new(0);
        *COUNTER.lock() += 1;
        assert_eq!(*COUNTER.lock(), 1);
    }
}

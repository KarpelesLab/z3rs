//! Boolean variables and literals — ported from `z3/src/sat/sat_types.h`
//! (Z3 4.17.0, MIT). Literals use Z3's `2*var + sign` packing so that negation
//! is a single bit flip and the literal is its own dense table index.

use core::fmt;
use core::ops::Not;

/// A propositional variable (a dense index).
pub type Var = u32;

/// A literal: a variable together with a sign. Encoded as `2*var + sign`, where
/// `sign == 1` denotes the *negative* literal (Z3's convention).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Lit(u32);

impl Lit {
    /// The literal `var` with the given sign (`true` = negated).
    #[inline]
    pub const fn new(var: Var, sign: bool) -> Lit {
        Lit((var << 1) | sign as u32)
    }

    /// The positive literal for `var`.
    #[inline]
    pub const fn pos(var: Var) -> Lit {
        Lit::new(var, false)
    }

    /// The negative literal for `var`.
    #[inline]
    pub const fn neg(var: Var) -> Lit {
        Lit::new(var, true)
    }

    /// The underlying variable.
    #[inline]
    pub const fn var(self) -> Var {
        self.0 >> 1
    }

    /// Is this the negative literal?
    #[inline]
    pub const fn sign(self) -> bool {
        (self.0 & 1) == 1
    }

    /// The dense index (`2*var + sign`), suitable for a lookup table.
    #[inline]
    pub const fn index(self) -> u32 {
        self.0
    }

    /// Reconstruct a literal from its [`index`](Self::index).
    #[inline]
    pub const fn from_index(i: u32) -> Lit {
        Lit(i)
    }
}

impl Not for Lit {
    type Output = Lit;
    /// Negate the literal (flip the sign bit).
    #[inline]
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.sign() {
            write!(f, "-{}", self.var())
        } else {
            write!(f, "{}", self.var())
        }
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Lit({self})")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn packing_and_negation() {
        let p = Lit::pos(3);
        let n = Lit::neg(3);
        assert_eq!(p.var(), 3);
        assert!(!p.sign());
        assert!(n.sign());
        assert_eq!(!p, n);
        assert_eq!(!n, p);
        assert_eq!(!!p, p);
        // index round-trips.
        assert_eq!(Lit::from_index(p.index()), p);
        assert_eq!(p.index(), 6);
        assert_eq!(n.index(), 7);
    }

    #[test]
    fn display() {
        use alloc::format;
        assert_eq!(format!("{}", Lit::pos(2)), "2");
        assert_eq!(format!("{}", Lit::neg(2)), "-2");
    }
}

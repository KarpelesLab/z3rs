//! Ported from `z3/src/util/lbool.{h,cpp}` (Z3 4.17.0, MIT). See NOTICE.
//!
//! Lifted (three-valued) boolean.

use core::fmt;
use core::ops::Not;

/// A lifted boolean: false, undefined, or true.
///
/// Discriminants match Z3 (`l_false = -1`, `l_undef = 0`, `l_true = 1`) so that
/// negation is arithmetic negation of the discriminant.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i8)]
pub enum LBool {
    /// `l_false`
    False = -1,
    /// `l_undef`
    Undef = 0,
    /// `l_true`
    True = 1,
}

pub use LBool::{False as L_FALSE, True as L_TRUE, Undef as L_UNDEF};

impl LBool {
    /// Lift a `bool`: `true -> True`, `false -> False`.
    #[inline]
    pub const fn from_bool(b: bool) -> LBool {
        if b { LBool::True } else { LBool::False }
    }

    /// The discriminant (`-1`, `0`, or `1`).
    #[inline]
    pub const fn to_int(self) -> i8 {
        self as i8
    }

    /// Build from a discriminant: negative → `False`, zero → `Undef`,
    /// positive → `True`.
    #[inline]
    pub const fn from_int(v: i32) -> LBool {
        if v < 0 {
            LBool::False
        } else if v > 0 {
            LBool::True
        } else {
            LBool::Undef
        }
    }

    /// `"satisfiable"` / `"unsatisfiable"` / `"unknown"` (Z3's `to_sat_str`).
    #[inline]
    pub const fn to_sat_str(self) -> &'static str {
        match self {
            LBool::True => "satisfiable",
            LBool::False => "unsatisfiable",
            LBool::Undef => "unknown",
        }
    }
}

impl Not for LBool {
    type Output = LBool;
    /// Negation: `True <-> False`, `Undef` fixed (Z3's `operator~`).
    #[inline]
    fn not(self) -> LBool {
        match self {
            LBool::False => LBool::True,
            LBool::True => LBool::False,
            LBool::Undef => LBool::Undef,
        }
    }
}

impl From<bool> for LBool {
    #[inline]
    fn from(b: bool) -> LBool {
        LBool::from_bool(b)
    }
}

impl fmt::Display for LBool {
    /// Matches Z3's `operator<<`: `l_false` / `l_true` / `l_undef`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            LBool::False => "l_false",
            LBool::True => "l_true",
            LBool::Undef => "l_undef",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn negation_matches_arithmetic() {
        assert_eq!(!LBool::True, LBool::False);
        assert_eq!(!LBool::False, LBool::True);
        assert_eq!(!LBool::Undef, LBool::Undef);
        // ~ is arithmetic negation of the discriminant.
        for v in [LBool::False, LBool::Undef, LBool::True] {
            assert_eq!((!v).to_int(), -v.to_int());
        }
    }

    #[test]
    fn lifting_roundtrips() {
        assert_eq!(LBool::from(true), LBool::True);
        assert_eq!(LBool::from(false), LBool::False);
        assert_eq!(LBool::from_int(-5), LBool::False);
        assert_eq!(LBool::from_int(0), LBool::Undef);
        assert_eq!(LBool::from_int(7), LBool::True);
    }

    #[test]
    fn display_and_sat_str() {
        assert_eq!(format!("{}", LBool::True), "l_true");
        assert_eq!(format!("{}", LBool::Undef), "l_undef");
        assert_eq!(LBool::True.to_sat_str(), "satisfiable");
        assert_eq!(LBool::False.to_sat_str(), "unsatisfiable");
        assert_eq!(LBool::Undef.to_sat_str(), "unknown");
    }
}

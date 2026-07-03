//! Ported from `z3/src/util/zstring.{h,cpp}` (Z3 4.17.0, MIT). See NOTICE.
//!
//! A string of Unicode code points, the value type of the SMT-LIB string theory.
//!
//! This is a minimal core: it stores the code points and round-trips through
//! Rust `&str`. Full SMT-LIB escaping/encoding (`\u{...}`, BMP/ASCII encodings)
//! will be filled in with the sequence/string theory (Phase 5); the [`Display`]
//! here is a plain rendering, not the SMT-LIB escaped form.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// The largest code point Z3's string theory represents (Unicode range).
pub const MAX_CHAR: u32 = 0x3FFFF;

/// A string as a sequence of Unicode code points.
#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct Zstring {
    chars: Vec<u32>,
}

impl Zstring {
    /// The empty string.
    #[inline]
    pub const fn new() -> Zstring {
        Zstring { chars: Vec::new() }
    }

    /// Number of code points.
    #[inline]
    pub fn len(&self) -> usize {
        self.chars.len()
    }

    /// Is the string empty?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.chars.is_empty()
    }

    /// The code point at `i`.
    #[inline]
    pub fn char_at(&self, i: usize) -> u32 {
        self.chars[i]
    }

    /// The code points.
    #[inline]
    pub fn as_slice(&self) -> &[u32] {
        &self.chars
    }

    /// Build from raw code points.
    #[inline]
    pub fn from_code_points(chars: Vec<u32>) -> Zstring {
        Zstring { chars }
    }

    /// Render to a Rust `String` (invalid scalar values are skipped).
    pub fn to_rust_string(&self) -> String {
        self.chars
            .iter()
            .filter_map(|&c| char::from_u32(c))
            .collect()
    }
}

impl From<&str> for Zstring {
    fn from(s: &str) -> Zstring {
        Zstring {
            chars: s.chars().map(|c| c as u32).collect(),
        }
    }
}

impl fmt::Display for Zstring {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for &c in &self.chars {
            match char::from_u32(c) {
                Some(ch) => f.write_str(ch.encode_utf8(&mut [0u8; 4]))?,
                None => write!(f, "\\u{{{c:x}}}")?,
            }
        }
        Ok(())
    }
}

impl fmt::Debug for Zstring {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.to_rust_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    #[test]
    fn roundtrip_and_indexing() {
        let z = Zstring::from("abc");
        assert_eq!(z.len(), 3);
        assert_eq!(z.char_at(0), b'a' as u32);
        assert_eq!(z.to_rust_string(), "abc");
        assert_eq!(z.to_string(), "abc");
        assert!(Zstring::new().is_empty());
    }

    #[test]
    fn eq_and_unicode() {
        assert_eq!(Zstring::from("x"), Zstring::from("x"));
        assert_ne!(Zstring::from("x"), Zstring::from("y"));
        let z = Zstring::from("héllo");
        assert_eq!(z.to_rust_string(), "héllo");
    }
}

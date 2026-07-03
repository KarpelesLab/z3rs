//! Ported from `z3/src/util/symbol.{h,cpp}` (Z3 4.17.0, MIT). See NOTICE.
//!
//! Lisp-like interned symbols. A [`Symbol`] is a small `Copy` handle that is one
//! of: null, a numeric symbol (`k!<n>`), or an interned string. String symbols
//! are interned into a global table so that equal strings share one allocation;
//! equality and hashing are then O(1) (pointer identity + a precomputed hash),
//! which matters because symbol comparison is extremely hot in the AST layer.
//!
//! Unlike Z3's tagged-pointer encoding, we use a small enum plus interned
//! `&'static` handles (interned strings live for the program's lifetime, exactly
//! as in Z3, whose symbol table is never freed during solving).

use core::cmp::Ordering;
use core::fmt;
use core::ptr;

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;

use crate::util::hash::string_hash;
use crate::util::sync::SpinLock;

/// An interned string symbol: its precomputed hash and its text.
struct Interned {
    hash: u32,
    text: &'static str,
}

/// Global intern table, keyed by the interned text. `const`-constructible so it
/// can back a `static` without lazy-init machinery.
static INTERN: SpinLock<BTreeMap<&'static str, &'static Interned>> = SpinLock::new(BTreeMap::new());

fn intern(s: &str) -> &'static Interned {
    let mut table = INTERN.lock();
    if let Some(&e) = table.get(s) {
        return e;
    }
    // Leak a copy so the handle is `&'static` (interned symbols are never freed).
    let text: &'static str = Box::leak(String::from(s).into_boxed_str());
    let hash = string_hash(text.as_bytes(), 17);
    let e: &'static Interned = Box::leak(Box::new(Interned { hash, text }));
    table.insert(text, e);
    e
}

#[derive(Clone, Copy)]
enum Repr {
    Null,
    Numeric(u32),
    Str(&'static Interned),
}

/// An interned symbol.
#[derive(Clone, Copy)]
pub struct Symbol(Repr);

impl Symbol {
    /// The null symbol.
    pub const NULL: Symbol = Symbol(Repr::Null);

    /// Intern a string symbol.
    #[inline]
    pub fn new(s: &str) -> Symbol {
        Symbol(Repr::Str(intern(s)))
    }

    /// Build a numeric symbol (`k!<idx>`).
    #[inline]
    pub const fn numeric(idx: u32) -> Symbol {
        Symbol(Repr::Numeric(idx))
    }

    /// Is this the null symbol?
    #[inline]
    pub const fn is_null(self) -> bool {
        matches!(self.0, Repr::Null)
    }

    /// Is this a numeric symbol?
    #[inline]
    pub const fn is_numerical(self) -> bool {
        matches!(self.0, Repr::Numeric(_))
    }

    /// Is this a non-empty string symbol?
    #[inline]
    pub fn is_non_empty_string(self) -> bool {
        matches!(self.0, Repr::Str(e) if !e.text.is_empty())
    }

    /// The numeric index, if this is a numeric symbol.
    #[inline]
    pub const fn num(self) -> Option<u32> {
        match self.0 {
            Repr::Numeric(n) => Some(n),
            _ => None,
        }
    }

    /// The string contents, if this is a string symbol.
    #[inline]
    pub fn as_str(self) -> Option<&'static str> {
        match self.0 {
            Repr::Str(e) => Some(e.text),
            _ => None,
        }
    }

    /// True if this string symbol contains `c` (false for null/numeric).
    #[inline]
    pub fn contains(self, c: char) -> bool {
        matches!(self.0, Repr::Str(e) if e.text.contains(c))
    }

    /// Z3's `symbol::hash`.
    #[inline]
    pub fn hash(self) -> u32 {
        match self.0 {
            Repr::Null => 0x9e37_79d9,
            Repr::Numeric(n) => n,
            Repr::Str(e) => e.hash,
        }
    }

    /// A stable discriminant rank used for total ordering.
    #[inline]
    const fn rank(self) -> u8 {
        match self.0 {
            Repr::Null => 0,
            Repr::Numeric(_) => 1,
            Repr::Str(_) => 2,
        }
    }
}

impl PartialEq for Symbol {
    #[inline]
    fn eq(&self, other: &Symbol) -> bool {
        match (self.0, other.0) {
            (Repr::Null, Repr::Null) => true,
            (Repr::Numeric(a), Repr::Numeric(b)) => a == b,
            // Interning guarantees equal strings share one `Interned`.
            (Repr::Str(a), Repr::Str(b)) => ptr::eq(a, b),
            _ => false,
        }
    }
}

impl Eq for Symbol {}

impl PartialEq<str> for Symbol {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        matches!(self.0, Repr::Str(e) if e.text == other)
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Symbol) -> Ordering {
        match (self.0, other.0) {
            (Repr::Numeric(a), Repr::Numeric(b)) => a.cmp(&b),
            (Repr::Str(a), Repr::Str(b)) => a.text.cmp(b.text),
            _ => self.rank().cmp(&other.rank()),
        }
    }
}

impl PartialOrd for Symbol {
    #[inline]
    fn partial_cmp(&self, other: &Symbol) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl core::hash::Hash for Symbol {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        // Match `Eq`: string symbols hash by identity, not by content bytes.
        match self.0 {
            Repr::Null => state.write_u8(0),
            Repr::Numeric(n) => {
                state.write_u8(1);
                state.write_u32(n);
            }
            Repr::Str(e) => {
                state.write_u8(2);
                state.write_usize(ptr::from_ref(e) as usize);
            }
        }
    }
}

impl Default for Symbol {
    #[inline]
    fn default() -> Symbol {
        Symbol::NULL
    }
}

impl From<&str> for Symbol {
    #[inline]
    fn from(s: &str) -> Symbol {
        Symbol::new(s)
    }
}

impl From<u32> for Symbol {
    #[inline]
    fn from(idx: u32) -> Symbol {
        Symbol::numeric(idx)
    }
}

impl fmt::Display for Symbol {
    /// Matches Z3's `operator<<`: text, `null`, or `k!<n>`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Repr::Str(e) => f.write_str(e.text),
            Repr::Null => f.write_str("null"),
            Repr::Numeric(n) => write!(f, "k!{n}"),
        }
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol({self})")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn equal_strings_are_interned_to_one_handle() {
        let a = Symbol::new("hello");
        let b = Symbol::new("hello");
        let c = Symbol::new("world");
        assert_eq!(a, b);
        assert_ne!(a, c);
        // Same interned pointer → identity equality.
        match (a.0, b.0) {
            (Repr::Str(pa), Repr::Str(pb)) => assert!(ptr::eq(pa, pb)),
            _ => panic!("expected string symbols"),
        }
        assert_eq!(a.hash(), b.hash());
    }

    #[test]
    fn numeric_and_null_symbols() {
        assert!(Symbol::NULL.is_null());
        assert!(!Symbol::NULL.is_numerical());
        let k = Symbol::numeric(7);
        assert!(k.is_numerical());
        assert_eq!(k.num(), Some(7));
        assert_eq!(k, Symbol::from(7u32));
        assert_ne!(k, Symbol::numeric(8));
        assert_eq!(k.hash(), 7);
    }

    #[test]
    fn accessors_and_display() {
        let s = Symbol::new("foo");
        assert_eq!(s.as_str(), Some("foo"));
        assert!(s.is_non_empty_string());
        assert!(s.contains('o'));
        assert!(s == *"foo");
        assert_eq!(format!("{s}"), "foo");
        assert_eq!(format!("{}", Symbol::numeric(3)), "k!3");
        assert_eq!(format!("{}", Symbol::NULL), "null");
        assert!(!Symbol::new("").is_non_empty_string());
    }

    #[test]
    fn total_order_is_deterministic() {
        // null < numeric < string; within a kind, by value/text.
        assert!(Symbol::NULL < Symbol::numeric(0));
        assert!(Symbol::numeric(0) < Symbol::new("a"));
        assert!(Symbol::numeric(1) < Symbol::numeric(2));
        assert!(Symbol::new("a") < Symbol::new("b"));
    }
}

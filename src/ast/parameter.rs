//! Ported from the `parameter` class in `z3/src/ast/ast.{h,cpp}` (Z3 4.17.0, MIT).
//!
//! A `parameter` decorates a sort or function declaration with extra data — a
//! bit-vector width, a rounding mode, an algebraic numeral, a nested sort, etc.
//! It is a tagged union; the variant order matches Z3's `parameter::kind_t`.

use core::fmt;
use core::hash::{Hash, Hasher};

use puremp::Rational;

use crate::ast::AstId;
use crate::util::symbol::Symbol;
use crate::util::zstring::Zstring;

/// The kind of a [`Parameter`] (matches Z3's `parameter::kind_t` order).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum ParameterKind {
    /// `PARAM_INT`
    Int = 0,
    /// `PARAM_AST`
    Ast = 1,
    /// `PARAM_SYMBOL`
    Symbol = 2,
    /// `PARAM_ZSTRING`
    Zstring = 3,
    /// `PARAM_RATIONAL`
    Rational = 4,
    /// `PARAM_DOUBLE`
    Double = 5,
    /// `PARAM_EXTERNAL` — plugin-specific opaque id.
    External = 6,
}

/// A declaration/sort parameter.
#[derive(Clone, Debug)]
pub enum Parameter {
    /// An integer.
    Int(i32),
    /// A reference to an AST node.
    Ast(AstId),
    /// A symbol.
    Symbol(Symbol),
    /// A string literal.
    Zstring(Zstring),
    /// A rational.
    Rational(Rational),
    /// A `f64`.
    Double(f64),
    /// A plugin-specific opaque id (`PARAM_EXTERNAL`).
    External(u32),
}

impl Parameter {
    /// The parameter's kind.
    pub const fn kind(&self) -> ParameterKind {
        match self {
            Parameter::Int(_) => ParameterKind::Int,
            Parameter::Ast(_) => ParameterKind::Ast,
            Parameter::Symbol(_) => ParameterKind::Symbol,
            Parameter::Zstring(_) => ParameterKind::Zstring,
            Parameter::Rational(_) => ParameterKind::Rational,
            Parameter::Double(_) => ParameterKind::Double,
            Parameter::External(_) => ParameterKind::External,
        }
    }

    /// Is this an integer parameter?
    pub const fn is_int(&self) -> bool {
        matches!(self, Parameter::Int(_))
    }
    /// Is this an AST parameter?
    pub const fn is_ast(&self) -> bool {
        matches!(self, Parameter::Ast(_))
    }
    /// Is this a symbol parameter?
    pub const fn is_symbol(&self) -> bool {
        matches!(self, Parameter::Symbol(_))
    }
    /// Is this a string parameter?
    pub const fn is_zstring(&self) -> bool {
        matches!(self, Parameter::Zstring(_))
    }
    /// Is this a rational parameter?
    pub const fn is_rational(&self) -> bool {
        matches!(self, Parameter::Rational(_))
    }
    /// Is this a double parameter?
    pub const fn is_double(&self) -> bool {
        matches!(self, Parameter::Double(_))
    }
    /// Is this an external parameter?
    pub const fn is_external(&self) -> bool {
        matches!(self, Parameter::External(_))
    }

    /// The integer value, if this is an integer parameter.
    pub const fn get_int(&self) -> Option<i32> {
        match self {
            Parameter::Int(i) => Some(*i),
            _ => None,
        }
    }
    /// The AST handle, if this is an AST parameter.
    pub const fn get_ast(&self) -> Option<AstId> {
        match self {
            Parameter::Ast(a) => Some(*a),
            _ => None,
        }
    }
    /// The symbol, if this is a symbol parameter.
    pub const fn get_symbol(&self) -> Option<Symbol> {
        match self {
            Parameter::Symbol(s) => Some(*s),
            _ => None,
        }
    }
    /// The string, if this is a string parameter.
    pub fn get_zstring(&self) -> Option<&Zstring> {
        match self {
            Parameter::Zstring(s) => Some(s),
            _ => None,
        }
    }
    /// The rational, if this is a rational parameter.
    pub fn get_rational(&self) -> Option<&Rational> {
        match self {
            Parameter::Rational(r) => Some(r),
            _ => None,
        }
    }
    /// The double, if this is a double parameter.
    pub const fn get_double(&self) -> Option<f64> {
        match self {
            Parameter::Double(d) => Some(*d),
            _ => None,
        }
    }
    /// The external id, if this is an external parameter.
    pub const fn get_ext_id(&self) -> Option<u32> {
        match self {
            Parameter::External(id) => Some(*id),
            _ => None,
        }
    }
}

impl From<i32> for Parameter {
    fn from(v: i32) -> Parameter {
        Parameter::Int(v)
    }
}
impl From<AstId> for Parameter {
    fn from(a: AstId) -> Parameter {
        Parameter::Ast(a)
    }
}
impl From<Symbol> for Parameter {
    fn from(s: Symbol) -> Parameter {
        Parameter::Symbol(s)
    }
}
impl From<Rational> for Parameter {
    fn from(r: Rational) -> Parameter {
        Parameter::Rational(r)
    }
}
impl From<f64> for Parameter {
    fn from(d: f64) -> Parameter {
        Parameter::Double(d)
    }
}

impl PartialEq for Parameter {
    fn eq(&self, other: &Parameter) -> bool {
        match (self, other) {
            (Parameter::Int(a), Parameter::Int(b)) => a == b,
            (Parameter::Ast(a), Parameter::Ast(b)) => a == b,
            (Parameter::Symbol(a), Parameter::Symbol(b)) => a == b,
            (Parameter::Zstring(a), Parameter::Zstring(b)) => a == b,
            (Parameter::Rational(a), Parameter::Rational(b)) => a == b,
            // Compare by bits so `Eq`/`Hash` stay consistent (incl. NaN).
            (Parameter::Double(a), Parameter::Double(b)) => a.to_bits() == b.to_bits(),
            (Parameter::External(a), Parameter::External(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Parameter {}

impl Hash for Parameter {
    fn hash<H: Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Parameter::Int(i) => i.hash(state),
            Parameter::Ast(a) => a.hash(state),
            Parameter::Symbol(s) => s.hash(state),
            Parameter::Zstring(s) => s.hash(state),
            Parameter::Rational(r) => r.hash(state),
            Parameter::Double(d) => d.to_bits().hash(state),
            Parameter::External(id) => id.hash(state),
        }
    }
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Parameter::Int(i) => write!(f, "{i}"),
            Parameter::Ast(a) => write!(f, "#{}", a.0),
            Parameter::Symbol(s) => write!(f, "{s}"),
            Parameter::Zstring(s) => write!(f, "\"{s}\""),
            Parameter::Rational(r) => write!(f, "{r}"),
            Parameter::Double(d) => write!(f, "{d}"),
            Parameter::External(id) => write!(f, "{id}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use puremp::Int;

    #[test]
    fn kinds_and_accessors() {
        let p = Parameter::Int(42);
        assert_eq!(p.kind(), ParameterKind::Int);
        assert_eq!(p.get_int(), Some(42));
        assert_eq!(p.get_symbol(), None);

        let s = Parameter::from(Symbol::new("bv"));
        assert!(s.is_symbol());
        assert_eq!(s.get_symbol(), Some(Symbol::new("bv")));

        let r = Parameter::from(Rational::new(Int::from(3), Int::from(4)));
        assert!(r.is_rational());
        assert_eq!(r.get_rational().unwrap().to_string(), "3/4");
    }

    #[test]
    fn equality_and_kind_order() {
        assert_eq!(Parameter::Int(1), Parameter::Int(1));
        assert_ne!(Parameter::Int(1), Parameter::Int(2));
        // Different kinds are never equal, even with a "similar" payload.
        assert_ne!(Parameter::Int(1), Parameter::External(1));
        // kind_t order matches Z3.
        assert_eq!(ParameterKind::Int as u8, 0);
        assert_eq!(ParameterKind::Rational as u8, 4);
        assert_eq!(ParameterKind::External as u8, 6);
    }

    #[test]
    fn double_uses_bit_equality() {
        assert_eq!(Parameter::Double(1.5), Parameter::Double(1.5));
        assert_eq!(Parameter::Double(f64::NAN), Parameter::Double(f64::NAN));
        assert_eq!(format!("{}", Parameter::Ast(AstId(7))), "#7");
    }
}

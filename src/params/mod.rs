//! # `params` — Parameter descriptor tables (`param_descrs`) for every module
//!
//! **Port phase 1.** Ported from `z3/src/params` (Z3 4.17.0, MIT): specifically
//! `param_descrs` (`z3/src/util/params.{h,cpp}`, the descriptor half) and the
//! per-module registration pattern of `gparams` (`z3/src/params/*_params.cpp`).
//!
//! The *value* store — a bag of `key → value` bindings used to configure a
//! module at runtime — lives in [`crate::util::params::Params`]. This module is
//! the complementary *schema*: a [`ParamDescrs`] describes which parameters a
//! module accepts, each parameter's [`ParamKind`], its default, and a one-line
//! documentation string, exactly as Z3's `param_descrs` does. It is used to
//! validate user-supplied parameters (`(set-option …)` / command-line `key=val`)
//! and to answer `(get-option …)` / `-pd` help queries.

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::util::params::{ParamValue, Params};

/// The declared kind of a parameter — mirrors Z3's `param_kind`
/// (`CPK_BOOL`, `CPK_UINT`, `CPK_DOUBLE`, `CPK_STRING`, `CPK_SYMBOL`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamKind {
    Bool,
    Uint,
    Double,
    /// Free-form string.
    String,
    /// A symbol; stored as a string, distinguished from `String` only for docs.
    Symbol,
}

impl ParamKind {
    /// Does `value` match this declared kind? (`String`/`Symbol` both accept the
    /// string-valued [`ParamValue::Str`].)
    pub fn accepts(&self, value: &ParamValue) -> bool {
        matches!(
            (self, value),
            (ParamKind::Bool, ParamValue::Bool(_))
                | (ParamKind::Uint, ParamValue::UInt(_))
                | (ParamKind::Double, ParamValue::Double(_))
                | (ParamKind::String, ParamValue::Str(_))
                | (ParamKind::Symbol, ParamValue::Str(_))
        )
    }

    /// The Z3-style name of the kind (used in help output).
    pub fn name(&self) -> &'static str {
        match self {
            ParamKind::Bool => "bool",
            ParamKind::Uint => "unsigned int",
            ParamKind::Double => "double",
            ParamKind::String => "string",
            ParamKind::Symbol => "symbol",
        }
    }
}

/// One parameter's schema entry: its kind, its default value, and a help string.
#[derive(Clone, Debug)]
pub struct ParamDescr {
    pub kind: ParamKind,
    pub default: ParamValue,
    pub doc: String,
}

/// A module's parameter schema — the ordered set of parameters it accepts.
/// Corresponds to Z3's `param_descrs`.
#[derive(Clone, Debug, Default)]
pub struct ParamDescrs {
    entries: BTreeMap<String, ParamDescr>,
}

impl ParamDescrs {
    /// An empty descriptor table.
    pub fn new() -> ParamDescrs {
        ParamDescrs {
            entries: BTreeMap::new(),
        }
    }

    /// Register a parameter. The default value must match `kind`
    /// (a programming error otherwise — asserted in debug builds).
    pub fn insert(&mut self, name: &str, kind: ParamKind, default: ParamValue, doc: &str) {
        debug_assert!(
            kind.accepts(&default),
            "default for `{name}` does not match its kind {kind:?}"
        );
        self.entries.insert(
            name.to_string(),
            ParamDescr {
                kind,
                default,
                doc: doc.to_string(),
            },
        );
    }

    /// Builder-style [`insert`](Self::insert) returning `self`.
    pub fn with(mut self, name: &str, kind: ParamKind, default: ParamValue, doc: &str) -> Self {
        self.insert(name, kind, default, doc);
        self
    }

    /// Look up a parameter's descriptor.
    pub fn get(&self, name: &str) -> Option<&ParamDescr> {
        self.entries.get(name)
    }

    /// Is `name` a declared parameter?
    pub fn contains(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// The number of declared parameters.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The declared parameter names, sorted.
    pub fn names(&self) -> Vec<&str> {
        self.entries.keys().map(String::as_str).collect()
    }

    /// Merge another table into this one (later definitions win). Used to build a
    /// combined schema from several module tables, like Z3's global registry.
    pub fn extend(&mut self, other: &ParamDescrs) {
        for (k, v) in &other.entries {
            self.entries.insert(k.clone(), v.clone());
        }
    }

    /// Validate a value bag against this schema: every key must be declared and
    /// its value's kind must match. Returns the first offending key with a
    /// human-readable reason, mirroring Z3's `param_descrs::validate`.
    pub fn validate(&self, params: &Params) -> Result<(), String> {
        for name in params.keys() {
            match self.entries.get(name) {
                None => return Err(alloc::format!("unknown parameter: {name}")),
                Some(descr) => {
                    let value = params.get(name).expect("key just iterated");
                    if !descr.kind.accepts(value) {
                        return Err(alloc::format!(
                            "parameter {name} expects {}, got a different kind",
                            descr.kind.name()
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// The effective value of `name`: the caller's binding if present and valid,
    /// otherwise the schema default. `None` if `name` is not declared.
    pub fn effective(&self, name: &str, params: &Params) -> Option<ParamValue> {
        let descr = self.entries.get(name)?;
        match params.get(name) {
            Some(v) if descr.kind.accepts(v) => Some(v.clone()),
            _ => Some(descr.default.clone()),
        }
    }
}

/// The descriptor table for the top-level solver parameters that z3rs honours
/// today — a faithful subset of Z3's global `smt`/solver parameter schema. As
/// more modules gain tunable behaviour their tables are merged in here.
pub fn global_descrs() -> ParamDescrs {
    ParamDescrs::new()
        .with(
            "timeout",
            ParamKind::Uint,
            ParamValue::UInt(u32::MAX as u64),
            "timeout in milliseconds (per check-sat)",
        )
        .with(
            "rlimit",
            ParamKind::Uint,
            ParamValue::UInt(0),
            "resource limit (0 means no limit)",
        )
        .with(
            "model",
            ParamKind::Bool,
            ParamValue::Bool(true),
            "produce models for satisfiable queries",
        )
        .with(
            "unsat_core",
            ParamKind::Bool,
            ParamValue::Bool(false),
            "produce unsat cores",
        )
        .with(
            "produce_proofs",
            ParamKind::Bool,
            ParamValue::Bool(false),
            "produce proofs for unsatisfiable queries",
        )
        .with(
            "random_seed",
            ParamKind::Uint,
            ParamValue::UInt(0),
            "random seed for the search",
        )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::params::{ParamValue, Params};

    #[test]
    fn kind_matching() {
        assert!(ParamKind::Bool.accepts(&ParamValue::Bool(true)));
        assert!(!ParamKind::Bool.accepts(&ParamValue::UInt(1)));
        assert!(ParamKind::Uint.accepts(&ParamValue::UInt(7)));
        assert!(ParamKind::Symbol.accepts(&ParamValue::Str("x".into())));
        assert!(ParamKind::String.accepts(&ParamValue::Str("x".into())));
    }

    #[test]
    fn validate_accepts_known_and_rejects_unknown() {
        let d = global_descrs();
        assert!(d.contains("timeout") && d.contains("model"));

        let mut p = Params::new();
        p.set("timeout", ParamValue::UInt(5000));
        p.set("model", ParamValue::Bool(false));
        assert!(d.validate(&p).is_ok());

        let mut bad_key = Params::new();
        bad_key.set("no_such_param", ParamValue::Bool(true));
        assert!(d.validate(&bad_key).is_err());

        let mut bad_kind = Params::new();
        bad_kind.set("timeout", ParamValue::Bool(true)); // should be Uint
        assert!(d.validate(&bad_kind).is_err());
    }

    #[test]
    fn effective_falls_back_to_default() {
        let d = global_descrs();
        let empty = Params::new();
        assert_eq!(d.effective("model", &empty), Some(ParamValue::Bool(true)));

        let mut p = Params::new();
        p.set("model", ParamValue::Bool(false));
        assert_eq!(d.effective("model", &p), Some(ParamValue::Bool(false)));

        assert_eq!(d.effective("undeclared", &p), None);
    }

    #[test]
    fn extend_merges_tables() {
        let mut a = ParamDescrs::new();
        a.insert("x", ParamKind::Bool, ParamValue::Bool(false), "x flag");
        let mut b = ParamDescrs::new();
        b.insert("y", ParamKind::Uint, ParamValue::UInt(3), "y count");
        a.extend(&b);
        assert_eq!(a.len(), 2);
        assert!(a.contains("x") && a.contains("y"));
    }
}

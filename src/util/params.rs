//! Parameters — a small typed key→value store, mirroring Z3's `params_ref`
//! (`z3/src/util/params.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! Z3 threads a `params_ref` through tactics, solvers, and the rewriter to carry
//! configuration (`:produce-models`, `:timeout`, `arith.solver`, …). Here it
//! backs the SMT-LIB `(set-option …)` / `(get-option …)` commands: option names
//! are strings, values are one of a few scalar types.

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};

/// A parameter value: the scalar types SMT-LIB options and Z3's `params_ref`
/// use.
#[derive(Clone, Debug, PartialEq)]
pub enum ParamValue {
    /// A boolean (`true`/`false`).
    Bool(bool),
    /// An unsigned integer.
    UInt(u64),
    /// A floating-point number.
    Double(f64),
    /// A symbol or free-form string value.
    Str(String),
}

/// A key→value parameter map. Keys are option names with any leading `:`
/// stripped, so `(set-option :produce-models true)` and a lookup of
/// `"produce-models"` agree.
#[derive(Clone, Debug, Default)]
pub struct Params {
    entries: BTreeMap<String, ParamValue>,
}

fn norm(key: &str) -> String {
    key.strip_prefix(':').unwrap_or(key).to_string()
}

impl Params {
    /// An empty parameter set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set `key` to `value` (replacing any previous binding).
    pub fn set(&mut self, key: &str, value: ParamValue) {
        self.entries.insert(norm(key), value);
    }

    /// The raw value bound to `key`, if any.
    pub fn get(&self, key: &str) -> Option<&ParamValue> {
        self.entries.get(&norm(key))
    }

    /// A boolean parameter, or `default` if unset or another type.
    pub fn get_bool(&self, key: &str, default: bool) -> bool {
        match self.get(key) {
            Some(ParamValue::Bool(b)) => *b,
            _ => default,
        }
    }

    /// An unsigned-integer parameter, or `default` if unset or another type.
    pub fn get_uint(&self, key: &str, default: u64) -> u64 {
        match self.get(key) {
            Some(ParamValue::UInt(u)) => *u,
            _ => default,
        }
    }

    /// Is `key` bound?
    pub fn contains(&self, key: &str) -> bool {
        self.entries.contains_key(&norm(key))
    }

    /// Number of bound parameters.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Are there no bound parameters?
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::{ParamValue, Params};

    #[test]
    fn set_get_roundtrip_and_colon_normalisation() {
        let mut p = Params::new();
        p.set(":produce-models", ParamValue::Bool(true));
        p.set("timeout", ParamValue::UInt(5000));
        // A leading colon on the option name is normalised away.
        assert!(p.get_bool("produce-models", false));
        assert!(p.get_bool(":produce-models", false));
        assert_eq!(p.get_uint("timeout", 0), 5000);
        assert!(p.contains(":timeout"));
        assert_eq!(p.len(), 2);
    }

    #[test]
    fn defaults_on_missing_or_wrong_type() {
        let mut p = Params::new();
        p.set("random-seed", ParamValue::UInt(7));
        assert!(p.get_bool("random-seed", true)); // wrong type → default
        assert_eq!(p.get_uint("nonexistent", 42), 42); // missing → default
        assert!(p.get("nonexistent").is_none());
    }
}

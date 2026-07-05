//! # `api` — C-compatible API surface + safe idiomatic Rust API
//!
//! **Port phase 9.** Mirrors the solver surface of `z3/src/api` (Z3 4.17.0,
//! MIT). The C ABI lives in [`crate::ffi`] (behind the `ffi` feature); this
//! module is the *safe* Rust API — an ergonomic, incremental [`Solver`] driven
//! by SMT-LIB 2 text, with typed results.
//!
//! ```
//! use z3rs::api::{SatResult, Solver};
//!
//! let mut s = Solver::new();
//! s.assert("(declare-const x Int)(assert (> x 5))(assert (< x 8))")
//!     .unwrap();
//! assert_eq!(s.check().unwrap(), SatResult::Sat);
//! let v = s.get_value("x").unwrap(); // "6" or "7" — a satisfying value
//! assert!(v == "6" || v == "7");
//! ```

use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::cmd_context::Session;

pub mod build;

/// A satisfiability verdict.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SatResult {
    /// The assertions are satisfiable.
    Sat,
    /// The assertions are unsatisfiable.
    Unsat,
    /// Could not be decided (an incomplete procedure gave up); never a guess.
    Unknown,
}

/// A safe, incremental SMT solver. Declarations, assertions, and the push/pop
/// stack persist across calls; assertions are supplied as SMT-LIB 2 text and the
/// results are returned as typed values or strings.
#[derive(Default)]
pub struct Solver {
    session: Session,
}

impl Solver {
    /// A fresh solver with no declarations or assertions.
    pub fn new() -> Solver {
        Solver {
            session: Session::new(),
        }
    }

    /// Interpret SMT-LIB 2 `script` against the accumulated state (declarations,
    /// assertions, options, `push`/`pop`), returning one line per command that
    /// produces output. Errors on a parse or type error.
    pub fn eval(&mut self, script: &str) -> Result<Vec<String>, String> {
        self.session.eval(script)
    }

    /// Add declarations and/or assertions (SMT-LIB 2 text producing no output).
    pub fn assert(&mut self, script: &str) -> Result<(), String> {
        if let Some(line) = self.eval(script)?.into_iter().next() {
            // A command here should not produce a response; surface any that do.
            return Err(alloc::format!("unexpected response from assert: {line}"));
        }
        Ok(())
    }

    /// Decide the current assertions (`(check-sat)`).
    pub fn check(&mut self) -> Result<SatResult, String> {
        match self.eval("(check-sat)")?.first().map(String::as_str) {
            Some("sat") => Ok(SatResult::Sat),
            Some("unsat") => Ok(SatResult::Unsat),
            Some("unknown") => Ok(SatResult::Unknown),
            other => Err(alloc::format!("unexpected check-sat response: {other:?}")),
        }
    }

    /// The value of `term` in the model of the most recent satisfiable `check`
    /// (`(get-value (term))`, with the surrounding `(term …)` stripped).
    pub fn get_value(&mut self, term: &str) -> Result<String, String> {
        let out = self.eval(&alloc::format!("(get-value ({term}))"))?;
        let line = out
            .first()
            .ok_or_else(|| "get-value produced no response".to_string())?;
        // Response shape `((term value))`: peel the two outer parens and the
        // echoed term, leaving the value.
        let peel = |s: &str| -> String {
            s.trim()
                .strip_prefix('(')
                .and_then(|s| s.strip_suffix(')'))
                .unwrap_or(s)
                .trim()
                .to_string()
        };
        let inner = peel(&peel(line));
        Ok(inner
            .strip_prefix(term)
            .map(str::trim)
            .unwrap_or(&inner)
            .to_string())
    }

    /// Enter a new assertion scope (`(push)`).
    pub fn push(&mut self) -> Result<(), String> {
        self.assert("(push)")
    }

    /// Discard the innermost assertion scope (`(pop)`).
    pub fn pop(&mut self) -> Result<(), String> {
        self.assert("(pop)")
    }

    /// Drop all assertions and declarations (`(reset)`).
    pub fn reset(&mut self) -> Result<(), String> {
        self.assert("(reset)")
    }

    /// Decide the current assertions together with a set of literal
    /// `assumptions` (`(check-sat-assuming (a₁ … aₙ))`), without adding them
    /// permanently — the basis for assumption-based unsat cores.
    ///
    /// ```
    /// use z3rs::api::{SatResult, Solver};
    /// let mut s = Solver::new();
    /// s.assert("(declare-const p Bool)(declare-const q Bool)(assert (=> p q))").unwrap();
    /// assert_eq!(s.check_assuming(&["p", "(not q)"]).unwrap(), SatResult::Unsat);
    /// assert_eq!(s.check_assuming(&["p"]).unwrap(), SatResult::Sat);
    /// ```
    pub fn check_assuming(&mut self, assumptions: &[&str]) -> Result<SatResult, String> {
        let joined = assumptions.join(" ");
        let out = self.eval(&alloc::format!("(check-sat-assuming ({joined}))"))?;
        match out.first().map(String::as_str) {
            Some("sat") => Ok(SatResult::Sat),
            Some("unsat") => Ok(SatResult::Unsat),
            Some("unknown") => Ok(SatResult::Unknown),
            other => Err(alloc::format!("unexpected response: {other:?}")),
        }
    }

    /// The unsat core of the most recent unsatisfiable check, as the list of
    /// `:named` assertion labels (`(get-unsat-core)`).
    ///
    /// ```
    /// use z3rs::api::{SatResult, Solver};
    /// let mut s = Solver::new();
    /// s.eval("(set-option :produce-unsat-cores true)").unwrap();
    /// s.assert("(declare-const x Int)(assert (! (> x 0) :named a))(assert (! (< x 0) :named b))").unwrap();
    /// assert_eq!(s.check().unwrap(), SatResult::Unsat);
    /// let core = s.get_unsat_core().unwrap();
    /// assert!(core.contains(&"a".to_string()) && core.contains(&"b".to_string()));
    /// ```
    pub fn get_unsat_core(&mut self) -> Result<Vec<String>, String> {
        let out = self.eval("(get-unsat-core)")?;
        let line = out
            .first()
            .ok_or_else(|| "get-unsat-core produced no response".to_string())?;
        let inner = line.trim().trim_start_matches('(').trim_end_matches(')');
        Ok(inner.split_whitespace().map(str::to_string).collect())
    }

    /// The full model of the most recent satisfiable check as `(name, value)`
    /// pairs, parsed from `(get-model)`.
    ///
    /// ```
    /// use z3rs::api::Solver;
    /// let mut s = Solver::new();
    /// s.assert("(declare-const x Int)(assert (= x 42))").unwrap();
    /// s.check().unwrap();
    /// let model = s.get_model().unwrap();
    /// assert!(model.iter().any(|(n, v)| n == "x" && v == "42"));
    /// ```
    pub fn get_model(&mut self) -> Result<Vec<(String, String)>, String> {
        // `(get-model)` prints one `(define-fun name () Sort value)` per line.
        let out = self.eval("(get-model)")?;
        let text = out.join("\n");
        let mut pairs = Vec::new();
        for line in text.lines() {
            let line = line.trim();
            let Some(rest) = line.strip_prefix("(define-fun ") else {
                continue;
            };
            let inner = rest.trim_end().trim_end_matches(')').trim();
            // inner = "name () Sort... value"; name is the first token and the
            // (scalar) value is the last.
            let mut toks = inner.split_whitespace();
            let Some(name) = toks.next() else { continue };
            if let Some(value) = inner.split_whitespace().last() {
                pairs.push((name.to_string(), value.to_string()));
            }
        }
        Ok(pairs)
    }

    /// Simplify an SMT-LIB term with the theory rewriter (`(simplify term)`),
    /// returning the simplified term's printed form.
    ///
    /// ```
    /// use z3rs::api::Solver;
    /// let mut s = Solver::new();
    /// s.assert("(declare-const x Int)").unwrap();
    /// assert_eq!(s.simplify("(+ x 0)").unwrap(), "x");
    /// ```
    pub fn simplify(&mut self, term: &str) -> Result<String, String> {
        let out = self.eval(&alloc::format!("(simplify {term})"))?;
        out.into_iter()
            .next()
            .ok_or_else(|| "simplify produced no response".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solver_incremental() {
        let mut s = Solver::new();
        s.assert("(declare-const x Int)(assert (> x 0))").unwrap();
        assert_eq!(s.check().unwrap(), SatResult::Sat);

        s.push().unwrap();
        s.assert("(assert (< x 0))").unwrap();
        assert_eq!(s.check().unwrap(), SatResult::Unsat);
        s.pop().unwrap();
        assert_eq!(s.check().unwrap(), SatResult::Sat);
    }

    #[test]
    fn solver_get_value() {
        let mut s = Solver::new();
        s.assert("(declare-const b (_ BitVec 8))(assert (= (bvadd b #x01) #x10))")
            .unwrap();
        assert_eq!(s.check().unwrap(), SatResult::Sat);
        assert_eq!(s.get_value("b").unwrap(), "#x0f");
    }

    #[test]
    fn solver_optimization() {
        let mut s = Solver::new();
        s.assert("(declare-const x Int)(assert (<= x 10))(assert (>= x 0))(maximize x)")
            .unwrap();
        assert_eq!(s.check().unwrap(), SatResult::Sat);
        assert_eq!(s.get_value("x").unwrap(), "10");
    }
}

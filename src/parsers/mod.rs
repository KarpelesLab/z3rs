//! # `parsers` — the frontend parsers, gathered as one entry point
//!
//! **Port phase 8.** Ported from `z3/src/parsers` (Z3 4.17.0, MIT). Z3 splits
//! its input readers across several components; z3rs implements each next to the
//! engine that consumes it and re-exports them here so the `z3rs` binary's
//! frontends (`-smt2` / `-dimacs` / `-dl` / `-drat`) resolve from one module:
//!
//! - **SMT-LIB 2** command scripts (and the legacy **SMT-LIB 1.2** `(benchmark …)`
//!   form) → [`crate::cmd_context::run_smt2`] / [`crate::cmd_context::Session`].
//! - **DIMACS CNF** → [`crate::sat::parse_dimacs`].
//! - **DRAT** proofs → [`crate::sat::drat`] (`parse_cnf` / `parse_proof` / `check`).
//! - **Datalog** (facts / rules / `?-` queries) → [`crate::muz::parse`] and
//!   [`crate::muz::evaluate`].
//!
//! ## Status: IN PROGRESS — all four binary frontends parse & are wired

pub use crate::cmd_context::{Session, run_smt2};
pub use crate::muz::{parse as parse_datalog, evaluate as eval_datalog};
pub use crate::sat::drat::{parse_cnf as parse_drat_cnf, parse_proof as parse_drat_proof};
pub use crate::sat::parse_dimacs;

#[cfg(test)]
mod tests {
    //! Smoke tests that each re-exported frontend entry point is reachable and
    //! parses a minimal input.

    #[test]
    fn all_frontends_reachable() {
        // SMT-LIB2
        assert_eq!(
            super::run_smt2("(declare-const p Bool)(assert p)(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // DIMACS
        assert_eq!(super::parse_dimacs("p cnf 1 1\n1 0\n").unwrap().num_vars(), 1);
        // DRAT
        assert!(super::parse_drat_proof("1 0\n").is_ok());
        // Datalog
        assert!(super::parse_datalog("p(a).").is_ok());
    }
}

//! # `sat` — propositional SAT core
//!
//! **Port phase 4.** Ported from `z3/src/sat` (Z3 4.17.0, MIT).
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Ported so far
//! - [x] literal/variable encoding (`sat_types`) → [`literal`]
//! - [x] a correct DPLL solver with unit propagation → [`solver`]
//! - [x] Tseitin CNF encoding of a Boolean AST formula (`goal2sat` core) → [`tseitin`]
//! - [x] DIMACS CNF parsing → [`dimacs`]
//! - [ ] CDCL: watched literals, clause learning, restarts, in-processing
//! - [ ] `sat_smt` bridge, DRAT proofs
//!
//! ## Status: IN PROGRESS

pub mod dimacs;
pub mod literal;
pub mod solver;
pub mod tseitin;

pub use dimacs::{DimacsError, parse as parse_dimacs};
pub use literal::{Lit, Var};
pub use solver::{SatResult, Solver};
pub use tseitin::{check_skeleton, encode, encode_tracking};

//! # `nlsat` — Nonlinear arithmetic SAT, real closed fields
//!
//! **Port phase 5.** Ported from the Z3 C++ component(s) below.
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Upstream C++ components to port
//! - [~] `z3/src/nlsat` → [`icp`] (interval-propagation *refutation* half of nlsat)
//! - [ ] `z3/src/realclosure`
//!
//! ## Status: IN PROGRESS — sound nonlinear refutation via interval propagation

pub mod cad;
pub mod elim;
pub mod icp;
pub mod realclosure;
pub mod univariate;

pub use icp::{Constraint, Rel, refute};
pub use univariate::decide as decide_univariate;

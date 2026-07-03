//! # `smt` — core SMT engine
//!
//! **Port phase 5.** Ported from `z3/src/smt` (Z3 4.17.0, MIT).
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Ported so far
//! - [x] congruence closure for equality + uninterpreted functions → [`euf`]
//! - [x] a lazy DPLL(T) loop deciding QF_UF → [`solver`]
//! - [ ] online theory propagation, minimized explanations, more theories
//!   (arith/bv/arrays), quantifier instantiation
//!
//! ## Status: IN PROGRESS

pub mod arith;
pub mod euf;
pub mod solver;

pub use arith::{
    Assignment, Constraint, LinExpr, Rel, feasible, feasible_with_diseqs, model, model_with_diseqs,
};
pub use euf::Egraph;
pub use solver::{SmtResult, check};

//! Utilities for comparing and ordering bounds.
//!
//! This is needed because bounds can be compared in two ways:
//! syntactically (in which case a start and end bound positioned on the same place will be considered different),
//! and semantically (in which case since they represent the same place, they are considered equal).

pub mod bound_eq;
pub mod bound_ord;

#[cfg(test)]
mod bound_ord_tests;
// #[cfg(test)]
// mod bound_eq_tests;

pub use bound_eq::*;
pub use bound_ord::*;

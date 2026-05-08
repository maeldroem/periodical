//! Set operations on intervals
//!
//! The main set operations are implemented:
//!
//! - Unions, with [`Unitable`]
//! - Intersections, with [`Intersectable`]
//! - Differences, with [`Differentiable`]
//! - Symmetric differences, with [`SymmetricallyDifferentiable`]

pub mod diff;
pub mod intersect;
pub mod sym_diff;
pub mod unite;

#[cfg(test)]
mod diff_tests;
#[cfg(test)]
mod intersect_tests;
#[cfg(test)]
mod sym_diff_tests;
#[cfg(test)]
mod unite_tests;

#[doc(inline)]
pub use diff::Differentiable;
#[doc(inline)]
pub use intersect::Intersectable;
#[doc(inline)]
pub use sym_diff::SymmetricallyDifferentiable;
#[doc(inline)]
pub use unite::Unitable;

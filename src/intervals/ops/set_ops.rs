//! Set operations on intervals
//!
//! The main set operations are implemented:
//!
//! - Unions, with [`Unitable`]
//! - Intersections, with [`Intersectable`]
//! - Differences, with [`Differentiable`]
//! - Symmetric differences, with [`SymmetricallyDifferentiable`]

use crate::utils::{inline_docs, tests};

pub mod diff;
pub mod intersect;
pub mod sym_diff;
pub mod unite;

tests! {
    mod diff_tests;
    mod intersect_tests;
    mod sym_diff_tests;
    mod unite_tests;
}

inline_docs! {
    pub use diff::Differentiable;
    pub use intersect::Intersectable;
    pub use sym_diff::SymmetricallyDifferentiable;
    pub use unite::Unitable;
}

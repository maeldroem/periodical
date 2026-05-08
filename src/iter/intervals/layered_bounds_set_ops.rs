//! Set operations iterators created from [layered bounds iterators](crate::iter::intervals::layered_bounds)
//!
//! - [Uniting a layered bounds iterator](unite)
//! - [Intersected a layered bounds iterator](intersect)
//! - [Difference using a layered bounds iterator](diff)
//! - [Symmetric difference using a layered bounds iterator](sym_diff)

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
pub use diff::{
    LayeredAbsoluteBoundsDifference,
    LayeredAbsoluteBoundsDifferenceIteratorDispatcher,
    LayeredRelativeBoundsDifference,
    LayeredRelativeBoundsDifferenceIteratorDispatcher,
};
#[doc(inline)]
pub use intersect::{
    LayeredAbsoluteBoundsIntersection,
    LayeredAbsoluteBoundsIntersectionIteratorDispatcher,
    LayeredRelativeBoundsIntersection,
    LayeredRelativeBoundsIntersectionIteratorDispatcher,
};
#[doc(inline)]
pub use sym_diff::{
    LayeredAbsoluteBoundsSymmetricDifference,
    LayeredAbsoluteBoundsSymmetricDifferenceIteratorDispatcher,
    LayeredRelativeBoundsSymmetricDifference,
    LayeredRelativeBoundsSymmetricDifferenceIteratorDispatcher,
};
#[doc(inline)]
pub use unite::{
    LayeredAbsoluteBoundsUnion,
    LayeredAbsoluteBoundsUnionIteratorDispatcher,
    LayeredRelativeBoundsUnion,
    LayeredRelativeBoundsUnionIteratorDispatcher,
};

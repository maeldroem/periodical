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

// #[cfg(test)]
// mod diff_tests;
#[cfg(test)]
mod intersect_tests;
#[cfg(test)]
mod sym_diff_tests;
#[cfg(test)]
mod unite_tests;

#[doc(inline)]
pub use diff::{
    LayeredAbsBoundsDifference,
    LayeredAbsBoundsDifferenceIteratorDispatcher,
    LayeredRelBoundsDifference,
    LayeredRelBoundsDifferenceIteratorDispatcher,
};
#[doc(inline)]
pub use intersect::{
    LayeredAbsBoundsIntersection,
    LayeredAbsBoundsIntersectionIteratorDispatcher,
    LayeredRelBoundsIntersection,
    LayeredRelBoundsIntersectionIteratorDispatcher,
};
#[doc(inline)]
pub use sym_diff::{
    LayeredAbsBoundsSymmetricDifference,
    LayeredAbsBoundsSymmetricDifferenceIteratorDispatcher,
    LayeredRelBoundsSymmetricDifference,
    LayeredRelBoundsSymmetricDifferenceIteratorDispatcher,
};
#[doc(inline)]
pub use unite::{
    LayeredAbsBoundsUnion,
    LayeredAbsBoundsUnionIteratorDispatcher,
    LayeredRelBoundsUnion,
    LayeredRelBoundsUnionIteratorDispatcher,
};

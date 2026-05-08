//! Iterators for interval set operations
//!
//! The following set operations are implemented:
//!
//! - [Unions](unite)
//! - [Intersections](intersect)
//! - [Differences](diff)
//! - [Symmetric differences](sym_diff)

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
    PeerDifference,
    PeerDifferenceIteratorDispatcher,
    PeerDifferenceWith,
    PeerDifferenceWithIteratorDispatcher,
};
#[doc(inline)]
pub use intersect::{
    PeerIntersection,
    PeerIntersectionIteratorDispatcher,
    PeerIntersectionWith,
    PeerIntersectionWithIteratorDispatcher,
};
#[doc(inline)]
pub use sym_diff::{
    PeerSymmetricDifference,
    PeerSymmetricDifferenceIteratorDispatcher,
    PeerSymmetricDifferenceWith,
    PeerSymmetricDifferenceWithIteratorDispatcher,
};
#[doc(inline)]
pub use unite::{
    AccumulativeUnion,
    AccumulativeUnionIteratorDispatcher,
    AccumulativeUnionWith,
    AccumulativeUnionWithIteratorDispatcher,
    PeerUnion,
    PeerUnionIteratorDispatcher,
    PeerUnionWith,
    PeerUnionWithIteratorDispatcher,
};

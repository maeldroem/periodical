//! Interval set operations iterators

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

pub use diff::{
    PeerDifference, PeerDifferenceIteratorDispatcher, PeerDifferenceWith, PeerDifferenceWithIteratorDispatcher,
};
pub use intersect::{
    PeerIntersection, PeerIntersectionIteratorDispatcher, PeerIntersectionWith, PeerIntersectionWithIteratorDispatcher,
};
pub use sym_diff::{
    PeerSymmetricDifference, PeerSymmetricDifferenceIteratorDispatcher, PeerSymmetricDifferenceWith,
    PeerSymmetricDifferenceWithIteratorDispatcher,
};
pub use unite::{
    AccumulativeUnion, AccumulativeUnionIteratorDispatcher, AccumulativeUnionWith,
    AccumulativeUnionWithIteratorDispatcher, PeerUnion, PeerUnionIteratorDispatcher, PeerUnionWith,
    PeerUnionWithIteratorDispatcher,
};

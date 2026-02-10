//! Iterators for interval set operations
//!
//! The following set operations are implemented:
//!
//! - [Unions](unite)
//! - [Intersections](intersect)
//! - [Differences](diff)
//! - [Symmetric differences](sym_diff)

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
}

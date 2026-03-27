//! Interval iterators
//!
//! This module contains various iterators to deal with intervals. With those iterators, you can...
//!
//! - [Retrieve bounds from intervals](bounds)
//! - [Unite bounds](united_bounds)
//! - [Layering bounds to track active layers](layered_bounds)
//! - [Operate set operations on layered bounds](layered_bounds_set_ops)
//! - [Operate set operations on intervals](set_ops)
//! - [Retrieve the complements of intervals](complement)
//! - [Remove empty intervals from a collection](remove_empty)
//!
//! Most iterators have a public `new` method, but most of them come with input requirements.
//! Make sure your input meet those requirements.

use crate::utils::tests;

// pub mod bounds;
pub mod complement;
// pub mod layered_bounds;
// pub mod layered_bounds_set_ops;
// pub mod remove_empty;
// pub mod set_ops;
// pub mod split;
// pub mod united_bounds;

tests! {
    // mod bounds_tests;
    mod complement_tests;
    // mod layered_bounds_tests;
    // mod remove_empty_tests;
    // mod split_tests;
    // mod united_bounds_tests;
}

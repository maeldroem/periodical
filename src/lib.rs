//! Periodical is a time interval management crate that makes dealing with time intervals consistent and reliable.
//!
//! # Features
//!
//! - Absolute and relative time intervals
//! - Set operations on collections of time intervals
//! - Ability to change precision of intervals
//! - Precise overlap positioning
//! - Bound inclusivities support
//! - Convenient overlap interpretations
//!
//! & More, & More to come!
//!
//! # Basic usage
//!
//! Most of the time, you will want to import the global prelude by using `use periodical::prelude::*;`.
//!
//! The global prelude brings common traits into scope, making the methods described by the traits available.
//! It also imports common structures, like [`AbsoluteInterval`](intervals::absolute::AbsoluteInterval)
//! and [`RelativeInterval`](intervals::relative::RelativeInterval).

pub mod intervals;
pub mod iter;
pub mod ops;
pub mod prelude;

#[cfg(feature = "arbitrary")]
mod arbitrary_impl;

#[cfg(feature = "serde")]
mod serde_impl;

#[cfg(test)]
mod ops_tests;
#[cfg(test)]
mod test_utils;

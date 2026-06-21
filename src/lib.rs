//! Periodical is a time interval management crate that makes dealing with time
//! intervals consistent and reliable.
//!
//! # Features
//!
//! - Absolute and relative time intervals
//! - Set operations on collections of time intervals
//! - Ability to change precision of intervals
//! - Precise overlap positioning
//! - Bound inclusivities support
//! - Convenient overlap interpretations
//! - Convenience methods
//! - Handling of periodicity
//! - Parsing and formatting of intervals
//! - Handling of naive durations such as days and weeks
//!
//! & More to come!
//!
//! # Basic usage
//!
//! Most of the time, you will want to import the global prelude by using `use periodical::prelude::*;`.
//!
//! The global prelude brings common traits into scope, making the methods
//! described by the traits available. It also imports common structures, like
//! [`AbsInterval`](intervals::absolute::AbsInterval)
//! and [`RelInterval`](intervals::relative::RelInterval).
//!
//! # Use cases
//!
//! The most common use case is related to handling schedules: availabilities,
//! shifts, holidays, active periods, etc. are all part of that category.
//!
//! Finding the set difference of a collection of intervals, or finding the kind
//! of overlap between intervals are all useful tools made easy through the usage of `periodical`!
//!
//! Tracking tasks or other time-dependent things is also a good use case for
//! `periodical`: Its dependency on `chrono` allows for high-precision tracking,
//! and those times can be rounded to different precisions thanks to
//! `periodical`. This change of time precision is common in professional
//! contexts where time spent on a task may be rounded to the nearest 5/15/30/60
//! minutes or on predefined _time anchors_ throughout the day.
//!
//! Periodicity can be taken advantage on in scheduling: it allows for
//! expressing schedules declaratively, meaning that instead of defining each
//! interval through large periods of time, you can instead define it
//! in terms of how the intervals should be placed.
//!
//! For a textual example, the classical imperative scheduling would be "I have
//! a shift on 2026-02-02 from 08:00 to 16:00, I have a shift on 2026-02-03 from
//! 09:00 to 17:00, I have a shift on 2026-02-05 from 08:00 to 16:00, [..]"
//! whereas the declarative way is similar to "I have a shift from 08:00 to
//! 16:00 every work day except on holidays and vacations. On tuesdays I instead
//! have my shifts from 09:00 to 17:00.".
//!
//! This gives multiple advantages: You can define complex and long schedules
//! easily, have a human-readable representation that can easily be updated, and
//! has a representation that takes up less space compared to the imperative way.
//!
//! # Crate features
//!
//! - `serde` provides serialization and deserialization of all common `periodical` structures
//! - `arbitrary` provides a way of generating structured data from unstructured data, useful for fuzzing

pub mod intervals;
pub mod iter;
pub mod ops;
pub mod prelude;
pub mod time;

mod test_utils;

#[cfg(feature = "arbitrary")]
mod arbitrary_impl;

#[cfg(test)]
mod ops_tests;
#[cfg(test)]
mod test_data;
#[cfg(test)]
mod time_tests;

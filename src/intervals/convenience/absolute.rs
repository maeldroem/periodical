//! Convenience methods for absolute intervals

use crate::utils::tests;

pub mod bounded_interval;
pub mod half_bounded_interval;

tests! {
    mod bounded_interval_tests;
    mod half_bounded_interval_tests;
}

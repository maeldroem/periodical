//! Precision change for relative intervals and bounds

use crate::utils::{inline_docs, tests};

pub mod bound;
pub mod interval;

tests! {
    mod bound_tests;
    mod interval_tests;
}

inline_docs! {
    pub use bound::PreciseRelativeBound;
    pub use interval::PreciseRelativeInterval;
}

//! Precision change for absolute intervals and bounds

pub mod bound;
pub mod interval;

#[cfg(test)]
mod bound_tests;
#[cfg(test)]
mod interval_tests;

#[doc(inline)]
pub use bound::PreciseAbsBound;
#[doc(inline)]
pub use interval::PreciseAbsInterval;

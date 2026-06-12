//! Precision change for relative intervals and bounds

pub mod bound;
pub mod interval;

#[cfg(test)]
mod bound_tests;
#[cfg(test)]
mod interval_tests;

#[doc(inline)]
pub use bound::PreciseRelBound;
#[doc(inline)]
pub use interval::PreciseRelInterval;

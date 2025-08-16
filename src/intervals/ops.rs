//! Interval operations and comparisons
//!
//! Operations and comparisons with intervals are implemented here. You will find methods like
//!
//! - `contains`
//! - `overlaps`
//! - `try_extend`
//!
//! You will also find things that touch to precision of interval bounds as well as rule sets to decide what counts
//! as overlapping and what doesn't.

pub mod abridge;
pub mod bound_containment;
pub mod bound_overlap_ambiguity;
pub mod complement;
pub mod continuation;
pub mod cut;
pub mod extend;
pub mod fill_gap;
pub mod grow;
pub mod overlap;
pub mod precision;
pub mod prelude;
pub mod relativity_conversion;
pub mod remove_overlap;
pub mod remove_overlap_or_gap;
pub mod set_ops;
pub mod shrink;
pub mod time_containment;

#[cfg(test)]
mod abridge_tests;
#[cfg(test)]
mod bound_containment_tests;
#[cfg(test)]
mod bound_overlap_ambiguity_tests;
#[cfg(test)]
mod complement_tests;
#[cfg(test)]
mod continuation_tests;
#[cfg(test)]
mod extend_tests;

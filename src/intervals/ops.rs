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
pub mod bound_overlap_ambiguity;
pub mod bound_position;
pub mod complement;
pub mod continuation;
pub mod cut;
pub mod extend;
pub mod fill_gap;
pub mod grow;
pub mod overlap_position;
pub mod precision;
pub mod prelude;
pub mod relativity_conversion;
pub mod remove_overlap;
pub mod remove_overlap_or_gap;
pub mod set_ops;
pub mod shrink;
pub mod time_containment_position;

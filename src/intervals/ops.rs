//! Various operations related to intervals and bounds
//!
//! _Operation_ is a relatively vague term, but in this module you will find...
//!
//! - [how to find overlaps between intervals](overlap)
//! - [how to check if a time is contained within an interval](point_containment)
//! - [how to cut intervals](cut)
//! - how to remove [gaps](fill_gap), [overlaps](remove_overlap), even [both](remove_overlap_or_gap)
//! - [how to order bounds](bound_ord)
//! - [how to check if a bound is contained within an interval](bound_containment)
//! - [how to get the complement of an interval](complement)
//! - how to adjust intervals by [growing](grow) or [shrinking](shrink) their bounds
//! - how to [extend] or [abridge] intervals
//! - [how to change the precision of intervals and bounds](precision)
//! - [how to apply set operations to intervals](set_ops)
//! - [how to find the continuations of an interval](continuation)
//! - [how to convert from relative to absolute and conversely](relativity_conversion)
//!
//! And, perchance, more to come in the future!

pub mod abridge;
pub mod bound_containment;
pub mod bound_ord;
pub mod bound_overlap_ambiguity;
pub mod complement;
pub mod continuation;
pub mod cut;
pub mod extend;
pub mod fill_gap;
pub mod grow;
pub mod overlap;
pub mod point_containment;
pub mod precision;
pub mod prelude;
pub mod relativity_conversion;
pub mod remove_overlap;
pub mod remove_overlap_or_gap;
pub mod set_ops;
pub mod shrink;

#[cfg(test)]
mod abridge_tests;
#[cfg(test)]
mod bound_containment_tests;
#[cfg(test)]
mod bound_ord_tests;
#[cfg(test)]
mod bound_overlap_ambiguity_tests;
#[cfg(test)]
mod complement_tests;
#[cfg(test)]
mod continuation_tests;
#[cfg(test)]
mod cut_tests;
#[cfg(test)]
mod extend_tests;
#[cfg(test)]
mod fill_gap_tests;
#[cfg(test)]
mod grow_tests;
#[cfg(test)]
mod overlap_tests;
#[cfg(test)]
mod point_containment_tests;
#[cfg(test)]
mod precision_tests;
#[cfg(test)]
mod relativity_conversion_tests;
#[cfg(test)]
mod remove_overlap_or_gap_tests;
#[cfg(test)]
mod remove_overlap_tests;
#[cfg(test)]
mod set_ops_tests;
#[cfg(test)]
mod shrink_tests;

pub use abridge::Abridgable;
pub use bound_containment::{
    BoundContainmentPosition, BoundContainmentRule, BoundContainmentRuleSet, CanPositionBoundContainment,
    DEFAULT_BOUND_CONTAINMENT_RULES, DisambiguatedBoundContainmentPosition,
};
pub use bound_ord::{BoundOrdering, PartialBoundOrd};
pub use complement::Complementable;
pub use cut::{CutResult, CutType, Cuttable};
pub use extend::Extensible;
pub use fill_gap::GapFillable;
pub use grow::{GrowableEndBound, GrowableStartBound};
pub use overlap::{
    CanPositionOverlap, DEFAULT_OVERLAP_RULES, DisambiguatedOverlapPosition, OverlapPosition, OverlapRule,
    OverlapRuleSet,
};
pub use point_containment::{
    CanPositionPointContainment, DEFAULT_POINT_CONTAINMENT_RULES, DisambiguatedPointContainmentPosition,
    PointContainmentPosition, PointContainmentRule, PointContainmentRuleSet,
};
pub use precision::PreciseAbsoluteInterval;
pub use relativity_conversion::{ToAbsolute, ToRelative};
pub use remove_overlap::{OverlapRemovable, OverlapRemovalResult};
pub use remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
pub use set_ops::{Differentiable, Intersectable, SymmetricallyDifferentiable, Unitable};
pub use shrink::{ShrinkableEndBound, ShrinkableStartBound};

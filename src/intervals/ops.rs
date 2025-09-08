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
pub mod bound_ord;
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
#[cfg(test)]
mod time_containment_tests;

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
pub use precision::PreciseAbsoluteBounds;
pub use relativity_conversion::{ToAbsolute, ToRelative};
pub use remove_overlap::{OverlapRemovable, OverlapRemovalResult};
pub use remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
pub use set_ops::{Differentiable, Intersectable, SymmetricallyDifferentiable, Unitable};
pub use shrink::{ShrinkableEndBound, ShrinkableStartBound};
pub use time_containment::{
    CanPositionTimeContainment, DEFAULT_TIME_CONTAINMENT_RULES, DisambiguatedTimeContainmentPosition,
    TimeContainmentPosition, TimeContainmentRule, TimeContainmentRuleSet,
};

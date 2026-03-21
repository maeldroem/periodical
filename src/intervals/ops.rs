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

use crate::utils::{inline_docs, tests};

pub mod abridge;
pub mod bound_containment;
pub mod bound_ord;
pub mod bound_overlap_ambiguity;
pub mod complement;
// pub mod continuation;
// pub mod cut;
// pub mod extend;
// pub mod fill_gap;
// pub mod grow;
// pub mod overlap;
// pub mod point_containment;
// pub mod precision;
// pub mod relativity_conversion;
// pub mod remove_overlap;
// pub mod remove_overlap_or_gap;
// pub mod set_ops;
// pub mod shrink;
// pub mod split;

tests! {
    mod abridge_tests;
    mod bound_containment_tests;
    mod bound_ord_tests;
    mod bound_overlap_ambiguity_tests;
    mod complement_tests;
//     mod continuation_tests;
//     mod cut_tests;
//     mod extend_tests;
//     mod fill_gap_tests;
//     mod grow_tests;
//     mod overlap_tests;
//     mod point_containment_tests;
//     mod precision_tests;
//     mod relativity_conversion_tests;
//     mod remove_overlap_or_gap_tests;
//     mod remove_overlap_tests;
//     mod set_ops_tests;
//     mod shrink_tests;
//     mod split_tests;
}

inline_docs! {
    pub use abridge::Abridgable;
    pub use bound_containment::{
        BoundContainmentPosition, BoundContainmentRule, BoundContainmentRuleSet, CanPositionBoundContainment,
        DEFAULT_BOUND_CONTAINMENT_RULES, DisambiguatedBoundContainmentPosition,
    };
    pub use bound_ord::{BoundOrdering, PartialBoundOrd};
    pub use bound_overlap_ambiguity::{
        BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
    };
    pub use complement::Complementable;
    // pub use cut::{CutResult, CutType, Cuttable};
    // pub use extend::Extensible;
    // pub use fill_gap::GapFillable;
    // pub use grow::{GrowableEndBound, GrowableStartBound};
    // pub use overlap::{
    //     CanPositionOverlap, DEFAULT_OVERLAP_RULES, DisambiguatedOverlapPosition, OverlapPosition, OverlapRule,
    //     OverlapRuleSet,
    // };
    // pub use point_containment::{
    //     CanPositionPointContainment, DEFAULT_POINT_CONTAINMENT_RULES, DisambiguatedPointContainmentPosition,
    //     PointContainmentPosition, PointContainmentRule, PointContainmentRuleSet,
    // };
    // pub use precision::PreciseAbsoluteInterval;
    // pub use relativity_conversion::{ToAbsolute, ToRelative};
    // pub use remove_overlap::{OverlapRemovable, OverlapRemovalResult};
    // pub use remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
    // pub use set_ops::{Differentiable, Intersectable, SymmetricallyDifferentiable, Unitable};
    // pub use shrink::{ShrinkableEndBound, ShrinkableStartBound};
}

//! Bound positioning

use std::cmp::Ordering;

use super::prelude::*;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::{AbsoluteBounds, EmptiableAbsoluteBounds};

/// Bound position relative to an interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundPosition {
    /// The given bound was found before the interval's beginning
    OutsideBefore,
    /// The given bound was found after the interval's end
    OutsideAfter,
    /// The given bound was found outside the interval
    ///
    /// This result is only possible when dealing with empty intervals.
    Outside,
    /// The given bound was found exactly on the start of the interval
    ///
    /// The bound ambiguity is stored within this variant.
    OnStart(Option<BoundOverlapAmbiguity>),
    /// The given bound was found exactly on the end of the interval
    ///
    /// The ambiguity is stored within this variant.
    OnEnd(Option<BoundOverlapAmbiguity>),
    /// The given bound was found exactly on the start and end of the interval
    ///
    /// This result is only possible when the given bound is inclusive and the interval is a single point in time
    /// with inclusive bounds.
    Equal,
    /// The given bound was found inside the interval
    Inside,
}

impl BoundPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate(self) -> DisambiguatedBoundPosition {
        match self {
            Self::OutsideBefore => DisambiguatedBoundPosition::OutsideBefore,
            Self::OutsideAfter => DisambiguatedBoundPosition::OutsideAfter,
            Self::Outside => DisambiguatedBoundPosition::Outside,
            Self::OnStart(..) => DisambiguatedBoundPosition::OnStart,
            Self::OnEnd(..) => DisambiguatedBoundPosition::OnEnd,
            Self::Equal => DisambiguatedBoundPosition::Equal,
            Self::Inside => DisambiguatedBoundPosition::Inside,
        }
    }

    /// Uses a rule set to transform the bound position into a disambiguated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: BoundPositionRuleSet) -> DisambiguatedBoundPosition {
        rule_set.disambiguate(self)
    }
}

/// Disambiguated [`BoundPosition`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DisambiguatedBoundPosition {
    /// See [`OutsideBefore`](BoundPosition::OutsideBefore)
    OutsideBefore,
    /// See [`OutsideAfter`](BoundPosition::OutsideAfter)
    OutsideAfter,
    /// See [`Outside`](BoundPosition::Outside)
    Outside,
    /// See [`OnStart`](BoundPosition::OnStart)
    OnStart,
    /// See [`OnEnd`](BoundPosition::OnEnd)
    OnEnd,
    /// See [`Equal`](BoundPosition::Equal)
    Equal,
    /// See [`Inside`](BoundPosition::Inside)
    Inside,
}

/// Different rule sets for determining whether different [`BoundPosition`]s are considered as containing or not.
///
/// See [`contains`](CanPositionBound::contains) for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum BoundPositionRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds, so both the bound needs and one of the interval's bounds needs to be
    /// inclusive in order to be counted as contained.
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// If the bound is inclusive and falls on an exclusive bound (and reversely), it still counts as contained.
    Lenient,
    /// Very lenient rule set
    ///
    /// Even if both the bound and one interval bound are exclusive, it still counts as contained.
    VeryLenient,
    /// Continuous to future rule set
    ///
    /// Like [`Strict`](BoundPositionRuleSet::Strict) but considers equal an exclusive end bound meeting
    /// an inclusive start bound
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Like [`Strict`](BoundPositionRuleSet::Strict) but considers equal an exclusive start bound meeting
    /// an inclusive end bound
    ContinuousToPast,
}

impl BoundPositionRuleSet {
    /// Disambiguates a bound position according to the rule set
    #[must_use]
    pub fn disambiguate(&self, bound_position: BoundPosition) -> DisambiguatedBoundPosition {
        match self {
            Self::Strict => {
                bound_position_rule_set_disambiguation(bound_position, BoundOverlapDisambiguationRuleSet::Strict)
            },
            Self::Lenient => {
                bound_position_rule_set_disambiguation(bound_position, BoundOverlapDisambiguationRuleSet::Lenient)
            },
            Self::VeryLenient => {
                bound_position_rule_set_disambiguation(bound_position, BoundOverlapDisambiguationRuleSet::VeryLenient)
            },
            Self::ContinuousToFuture => bound_position_rule_set_disambiguation(
                bound_position,
                BoundOverlapDisambiguationRuleSet::ContinuousToFuture,
            ),
            Self::ContinuousToPast => bound_position_rule_set_disambiguation(
                bound_position,
                BoundOverlapDisambiguationRuleSet::ContinuousToPast,
            ),
        }
    }
}

/// Disambiguates a [`BoundPosition`] using the given [`BoundOverlapDisambiguationRuleSet`]
#[must_use]
pub fn bound_position_rule_set_disambiguation(
    bound_position: BoundPosition,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedBoundPosition {
    match bound_position {
        BoundPosition::Outside => DisambiguatedBoundPosition::Outside,
        BoundPosition::OutsideBefore => DisambiguatedBoundPosition::OutsideBefore,
        BoundPosition::OutsideAfter => DisambiguatedBoundPosition::OutsideAfter,
        BoundPosition::OnStart(None) => DisambiguatedBoundPosition::OnStart,
        BoundPosition::OnStart(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                DisambiguatedBoundOverlap::Before => DisambiguatedBoundPosition::OutsideBefore,
                DisambiguatedBoundOverlap::Equal => DisambiguatedBoundPosition::OnStart,
                DisambiguatedBoundOverlap::After => DisambiguatedBoundPosition::Inside,
            }
        },
        BoundPosition::OnEnd(None) => DisambiguatedBoundPosition::OnEnd,
        BoundPosition::OnEnd(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                DisambiguatedBoundOverlap::Before => DisambiguatedBoundPosition::Inside,
                DisambiguatedBoundOverlap::Equal => DisambiguatedBoundPosition::OnEnd,
                DisambiguatedBoundOverlap::After => DisambiguatedBoundPosition::OutsideAfter,
            }
        },
        BoundPosition::Equal => DisambiguatedBoundPosition::Equal,
        BoundPosition::Inside => DisambiguatedBoundPosition::Inside,
    }
}

/// Capacity to position a bound in an interval
///
/// We assume that the given bound comes from another interval than the one operated on.
pub trait CanPositionBound<B> {
    fn bound_position(&self, bound: &B) -> BoundPosition;
}

impl<T> CanPositionBound<AbsoluteStartBound> for T
where
    T: HasEmptiableAbsoluteBounds,
{
    fn bound_position(&self, bound: &AbsoluteStartBound) -> BoundPosition {
        bound_position_abs_start_bound_on_emptiable_abs_bounds(&self.emptiable_abs_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteStartBound`] within the given [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_start_bound_on_emptiable_abs_bounds(
    emptiable_abs_bounds: &EmptiableAbsoluteBounds,
    abs_start_bound: &AbsoluteStartBound,
) -> BoundPosition {
    let EmptiableAbsoluteBounds::Bound(abs_bounds) = emptiable_abs_bounds else {
        return BoundPosition::Outside;
    };

    bound_position_abs_start_bound_on_abs_bounds(abs_bounds, abs_start_bound)
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteStartBound`] within the given [`AbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_start_bound_on_abs_bounds(
    abs_bounds: &AbsoluteBounds,
    abs_start_bound: &AbsoluteStartBound,
) -> BoundPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;

    match (abs_bounds.start(), abs_bounds.end(), abs_start_bound) {
        (StartB::InfinitePast, _, StartB::InfinitePast) => BoundPosition::OnStart(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, StartB::Finite(_)) => BoundPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), StartB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_end.time()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::EndStart(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(_), _, StartB::InfinitePast) => BoundPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, StartB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_start.time()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
                    finite_start.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(finite_start), EndB::Finite(finite_end), StartB::Finite(finite_bound)) => {
            match (
                finite_bound.time().cmp(&finite_start.time()),
                finite_bound.time().cmp(&finite_end.time()),
            ) {
                (Ordering::Less, _) => BoundPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundPosition::Equal,
                    BoundInclusivity::Exclusive => BoundPosition::OutsideBefore,
                },
                (Ordering::Equal, Ordering::Less) => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
                    finite_start.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Equal) => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::EndStart(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Less) => BoundPosition::Inside,
            }
        },
    }
}

impl<T> CanPositionBound<AbsoluteEndBound> for T
where
    T: HasEmptiableAbsoluteBounds,
{
    fn bound_position(&self, bound: &AbsoluteEndBound) -> BoundPosition {
        bound_position_abs_end_bound_on_emptiable_abs_bounds(&self.emptiable_abs_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteEndBound`] within the given [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_end_bound_on_emptiable_abs_bounds(
    emptiable_abs_bounds: &EmptiableAbsoluteBounds,
    abs_end_bound: &AbsoluteEndBound,
) -> BoundPosition {
    let EmptiableAbsoluteBounds::Bound(abs_bounds) = emptiable_abs_bounds else {
        return BoundPosition::Outside;
    };

    bound_position_abs_end_bound_on_abs_bounds(abs_bounds, abs_end_bound)
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteEndBound`] within the given [`AbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_end_bound_on_abs_bounds(
    abs_bounds: &AbsoluteBounds,
    abs_end_bound: &AbsoluteEndBound,
) -> BoundPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;

    match (abs_bounds.start(), abs_bounds.end(), abs_end_bound) {
        (_, EndB::InfiniteFuture, EndB::InfiniteFuture) => BoundPosition::OnEnd(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, EndB::Finite(_)) => BoundPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), EndB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_end.time()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::BothEnds(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (_, EndB::Finite(_), EndB::InfiniteFuture) => BoundPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, EndB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_start.time()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::StartEnd(
                    finite_start.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(finite_start), EndB::Finite(finite_end), EndB::Finite(finite_bound)) => {
            match (
                finite_bound.time().cmp(&finite_start.time()),
                finite_bound.time().cmp(&finite_end.time()),
            ) {
                (Ordering::Less, _) => BoundPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundPosition::Equal,
                    BoundInclusivity::Exclusive => BoundPosition::OutsideAfter,
                },
                (Ordering::Equal, Ordering::Less) => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::StartEnd(
                    finite_start.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Equal) => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::BothEnds(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Less) => BoundPosition::Inside,
            }
        },
    }
}

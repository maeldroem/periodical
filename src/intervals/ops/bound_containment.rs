//! Bound positioning

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;

use super::prelude::*;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeStartBound};
use crate::intervals::{AbsoluteBounds, EmptiableAbsoluteBounds, EmptiableRelativeBounds};

/// Bound position relative to an interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
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
    pub fn disambiguate_using_rule_set(self, rule_set: BoundContainmentRuleSet) -> DisambiguatedBoundPosition {
        rule_set.disambiguate(self)
    }
}

/// Disambiguated [`BoundPosition`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
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
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum BoundContainmentRuleSet {
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

impl BoundContainmentRuleSet {
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

/// Bound containment rules used as the reference for predefined decisions
pub const DEFAULT_BOUND_CONTAINMENT_RULES: [BoundContainmentRule; 1] = [BoundContainmentRule::AllowOnBounds];

/// All rules for determining what counts as containment
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum BoundContainmentRule {
    /// Counts as contained when the bound is on the start of the interval
    AllowOnStart,
    /// Counts as contained when the bound is on the end of the interval
    AllowOnEnd,
    /// Equivalent to [`AllowOnStart`](BoundContainmentRule::AllowOnStart) and [`AllowOnEnd`](BoundContainmentRule::AllowOnEnd)
    AllowOnBounds,
    /// Doesn't count as contained when the bound is on the start of the interval
    DenyOnStart,
    /// Doesn't count as contained when the bound is on the end of the interval
    DenyOnEnd,
    /// Equivalent to [`DenyOnStart`](BoundContainmentRule::DenyOnStart) and [`DenyOnEnd`](BoundContainmentRule::DenyOnEnd)
    DenyOnBounds,
}

impl BoundContainmentRule {
    /// Returns the next state of the running containment decision, given the current one and the disambiguated
    /// bound position
    #[must_use]
    pub fn counts_as_contained(&self, running: bool, disambiguated_pos: DisambiguatedBoundPosition) -> bool {
        match self {
            Self::AllowOnStart => allow_on_start_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::AllowOnEnd => allow_on_end_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::AllowOnBounds => allow_on_bounds_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::DenyOnStart => deny_on_start_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::DenyOnEnd => deny_on_end_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::DenyOnBounds => deny_on_bounds_containment_rule_counts_as_contained(running, disambiguated_pos),
        }
    }
}

/// Checks all the given rules and returns the final boolean regarding bound containment
#[must_use]
pub fn check_bound_containment_rules<'a, RI>(disambiguated_pos: DisambiguatedBoundPosition, rules: RI) -> bool
where
    RI: IntoIterator<Item = &'a BoundContainmentRule>,
{
    let common = matches!(
        disambiguated_pos,
        DisambiguatedBoundPosition::Equal | DisambiguatedBoundPosition::Inside,
    );

    rules.into_iter().fold(common, |is_contained, rule| {
        rule.counts_as_contained(is_contained, disambiguated_pos)
    })
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'allow on start' rule](BoundContainmentRule::AllowOnStart)
#[must_use]
pub fn allow_on_start_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedBoundPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'allow on end' rule](BoundContainmentRule::AllowOnEnd)
#[must_use]
pub fn allow_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedBoundPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'allow on bounds' rule](BoundContainmentRule::AllowOnBounds)
#[must_use]
pub fn allow_on_bounds_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundPosition,
) -> bool {
    running
        || matches!(
            disambiguated_pos,
            DisambiguatedBoundPosition::OnStart | DisambiguatedBoundPosition::OnEnd,
        )
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'deny on start' rule](BoundContainmentRule::DenyOnStart)
#[must_use]
pub fn deny_on_start_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedBoundPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'deny on end' rule](BoundContainmentRule::DenyOnEnd)
#[must_use]
pub fn deny_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedBoundPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'deny on bounds' rule](BoundContainmentRule::DenyOnBounds)
#[must_use]
pub fn deny_on_bounds_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundPosition,
) -> bool {
    running
        && !matches!(
            disambiguated_pos,
            DisambiguatedBoundPosition::OnStart | DisambiguatedBoundPosition::OnEnd,
        )
}

/// Capacity to position a bound in an interval
///
/// We assume that the given bound comes from another interval than the one operated on.
pub trait CanPositionBoundContainment<B> {
    /// Returns the bound position of the given bound
    #[must_use]
    fn bound_position(&self, bound: &B) -> BoundPosition;

    /// Returns the disambiguated bound position of the given bound using the given rule set
    #[must_use]
    fn disambiguated_bound_position(&self, bound: &B, rule_set: BoundContainmentRuleSet) -> DisambiguatedBoundPosition {
        self.bound_position(bound).disambiguate_using_rule_set(rule_set)
    }

    /// Returns whether the given bound is contained in the interval using predetermined rules
    ///
    /// Uses the [default rule set](BoundContainmentRuleSet::default) with default rules.
    #[must_use]
    fn simple_contains(&self, bound: &B) -> bool {
        self.contains(
            bound,
            BoundContainmentRuleSet::default(),
            &DEFAULT_BOUND_CONTAINMENT_RULES,
        )
    }

    /// Returns whether the given bound is contained in the interval using the given [containment rules](BoundContainmentRule)
    #[must_use]
    fn contains<'a, RI>(&self, bound: &B, rule_set: BoundContainmentRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a BoundContainmentRule>,
    {
        check_bound_containment_rules(self.disambiguated_bound_position(bound, rule_set), rules)
    }

    /// Returns whether the given bound is contained in the interval using the given closure
    #[must_use]
    fn contains_using<F>(&self, bound: &B, f: F) -> bool
    where
        F: FnOnce(BoundPosition) -> bool,
    {
        (f)(self.bound_position(bound))
    }

    /// Returns whether the given bound is contained in the interval using the given closure
    /// with a disambiguated position
    #[must_use]
    fn contains_using_simple<F>(&self, bound: &B, rule_set: BoundContainmentRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedBoundPosition) -> bool,
    {
        (f)(self.disambiguated_bound_position(bound, rule_set))
    }
}

impl<T> CanPositionBoundContainment<AbsoluteStartBound> for T
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
                Ordering::Equal => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::StartEnd(
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(_), _, StartB::InfinitePast) => BoundPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, StartB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_start.time()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
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
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Equal) => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::StartEnd(
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Less) => BoundPosition::Inside,
            }
        },
    }
}

impl<T> CanPositionBoundContainment<AbsoluteEndBound> for T
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
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
            }
        },
        (_, EndB::Finite(_), EndB::InfiniteFuture) => BoundPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, EndB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_start.time()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::EndStart(
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
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
                (Ordering::Equal, Ordering::Less) => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::EndStart(
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Equal) => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::BothEnds(
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Less) => BoundPosition::Inside,
            }
        },
    }
}

impl<T> CanPositionBoundContainment<RelativeStartBound> for T
where
    T: HasEmptiableRelativeBounds,
{
    fn bound_position(&self, bound: &RelativeStartBound) -> BoundPosition {
        bound_position_rel_start_bound_on_emptiable_rel_bounds(&self.emptiable_rel_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`RelativeStartBound`] within the given [`EmptiableRelativeBounds`]
#[must_use]
pub fn bound_position_rel_start_bound_on_emptiable_rel_bounds(
    emptiable_rel_bounds: &EmptiableRelativeBounds,
    rel_start_bound: &RelativeStartBound,
) -> BoundPosition {
    let EmptiableRelativeBounds::Bound(rel_bounds) = emptiable_rel_bounds else {
        return BoundPosition::Outside;
    };

    bound_position_rel_start_bound_on_rel_bounds(rel_bounds, rel_start_bound)
}

/// Returns the [`BoundPosition`] of the given [`RelativeStartBound`] within the given [`RelativeBounds`]
#[must_use]
pub fn bound_position_rel_start_bound_on_rel_bounds(
    rel_bounds: &RelativeBounds,
    rel_start_bound: &RelativeStartBound,
) -> BoundPosition {
    type StartB = RelativeStartBound;
    type EndB = RelativeEndBound;

    match (rel_bounds.start(), rel_bounds.end(), rel_start_bound) {
        (StartB::InfinitePast, _, StartB::InfinitePast) => BoundPosition::OnStart(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, StartB::Finite(_)) => BoundPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), StartB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_end.offset()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::StartEnd(
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(_), _, StartB::InfinitePast) => BoundPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, StartB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_start.offset()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(finite_start), EndB::Finite(finite_end), StartB::Finite(finite_bound)) => {
            match (
                finite_bound.offset().cmp(&finite_start.offset()),
                finite_bound.offset().cmp(&finite_end.offset()),
            ) {
                (Ordering::Less, _) => BoundPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundPosition::Equal,
                    BoundInclusivity::Exclusive => BoundPosition::OutsideBefore,
                },
                (Ordering::Equal, Ordering::Less) => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Equal) => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::StartEnd(
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Less) => BoundPosition::Inside,
            }
        },
    }
}

impl<T> CanPositionBoundContainment<RelativeEndBound> for T
where
    T: HasEmptiableRelativeBounds,
{
    fn bound_position(&self, bound: &RelativeEndBound) -> BoundPosition {
        bound_position_rel_end_bound_on_emptiable_rel_bounds(&self.emptiable_rel_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`RelativeEndBound`] within the given [`EmptiableRelativeBounds`]
#[must_use]
pub fn bound_position_rel_end_bound_on_emptiable_rel_bounds(
    emptiable_rel_bounds: &EmptiableRelativeBounds,
    rel_end_bound: &RelativeEndBound,
) -> BoundPosition {
    let EmptiableRelativeBounds::Bound(rel_bounds) = emptiable_rel_bounds else {
        return BoundPosition::Outside;
    };

    bound_position_rel_end_bound_on_rel_bounds(rel_bounds, rel_end_bound)
}

/// Returns the [`BoundPosition`] of the given [`RelativeEndBound`] within the given [`RelativeBounds`]
#[must_use]
pub fn bound_position_rel_end_bound_on_rel_bounds(
    rel_bounds: &RelativeBounds,
    rel_end_bound: &RelativeEndBound,
) -> BoundPosition {
    type StartB = RelativeStartBound;
    type EndB = RelativeEndBound;

    match (rel_bounds.start(), rel_bounds.end(), rel_end_bound) {
        (_, EndB::InfiniteFuture, EndB::InfiniteFuture) => BoundPosition::OnEnd(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, EndB::Finite(_)) => BoundPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), EndB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_end.offset()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::BothEnds(
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
            }
        },
        (_, EndB::Finite(_), EndB::InfiniteFuture) => BoundPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, EndB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_start.offset()) {
                Ordering::Less => BoundPosition::Inside,
                Ordering::Greater => BoundPosition::OutsideAfter,
                Ordering::Equal => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::EndStart(
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(finite_start), EndB::Finite(finite_end), EndB::Finite(finite_bound)) => {
            match (
                finite_bound.offset().cmp(&finite_start.offset()),
                finite_bound.offset().cmp(&finite_end.offset()),
            ) {
                (Ordering::Less, _) => BoundPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundPosition::Equal,
                    BoundInclusivity::Exclusive => BoundPosition::OutsideAfter,
                },
                (Ordering::Equal, Ordering::Less) => BoundPosition::OnStart(Some(BoundOverlapAmbiguity::EndStart(
                    finite_bound.inclusivity(),
                    finite_start.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Equal) => BoundPosition::OnEnd(Some(BoundOverlapAmbiguity::BothEnds(
                    finite_bound.inclusivity(),
                    finite_end.inclusivity(),
                ))),
                (Ordering::Greater, Ordering::Less) => BoundPosition::Inside,
            }
        },
    }
}

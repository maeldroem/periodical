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
pub enum BoundContainmentPosition {
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

impl BoundContainmentPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn strip(self) -> DisambiguatedBoundContainmentPosition {
        match self {
            Self::OutsideBefore => DisambiguatedBoundContainmentPosition::OutsideBefore,
            Self::OutsideAfter => DisambiguatedBoundContainmentPosition::OutsideAfter,
            Self::Outside => DisambiguatedBoundContainmentPosition::Outside,
            Self::OnStart(..) => DisambiguatedBoundContainmentPosition::OnStart,
            Self::OnEnd(..) => DisambiguatedBoundContainmentPosition::OnEnd,
            Self::Equal => DisambiguatedBoundContainmentPosition::Equal,
            Self::Inside => DisambiguatedBoundContainmentPosition::Inside,
        }
    }

    /// Uses a rule set to transform the bound position into a disambiguated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate_using_rule_set(
        self,
        rule_set: BoundContainmentRuleSet,
    ) -> DisambiguatedBoundContainmentPosition {
        rule_set.disambiguate(self)
    }
}

/// Disambiguated [`BoundPosition`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum DisambiguatedBoundContainmentPosition {
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
    pub fn disambiguate(&self, bound_position: BoundContainmentPosition) -> DisambiguatedBoundContainmentPosition {
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
    bound_position: BoundContainmentPosition,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedBoundContainmentPosition {
    match bound_position {
        BoundContainmentPosition::Outside => DisambiguatedBoundContainmentPosition::Outside,
        BoundContainmentPosition::OutsideBefore => DisambiguatedBoundContainmentPosition::OutsideBefore,
        BoundContainmentPosition::OutsideAfter => DisambiguatedBoundContainmentPosition::OutsideAfter,
        BoundContainmentPosition::OnStart(None) => DisambiguatedBoundContainmentPosition::OnStart,
        BoundContainmentPosition::OnStart(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                DisambiguatedBoundOverlap::Before => DisambiguatedBoundContainmentPosition::OutsideBefore,
                DisambiguatedBoundOverlap::Equal => DisambiguatedBoundContainmentPosition::OnStart,
                DisambiguatedBoundOverlap::After => DisambiguatedBoundContainmentPosition::Inside,
            }
        },
        BoundContainmentPosition::OnEnd(None) => DisambiguatedBoundContainmentPosition::OnEnd,
        BoundContainmentPosition::OnEnd(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                DisambiguatedBoundOverlap::Before => DisambiguatedBoundContainmentPosition::Inside,
                DisambiguatedBoundOverlap::Equal => DisambiguatedBoundContainmentPosition::OnEnd,
                DisambiguatedBoundOverlap::After => DisambiguatedBoundContainmentPosition::OutsideAfter,
            }
        },
        BoundContainmentPosition::Equal => DisambiguatedBoundContainmentPosition::Equal,
        BoundContainmentPosition::Inside => DisambiguatedBoundContainmentPosition::Inside,
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
    pub fn counts_as_contained(&self, running: bool, disambiguated_pos: DisambiguatedBoundContainmentPosition) -> bool {
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
pub fn check_bound_containment_rules<'a, RI>(
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
    rules: RI,
) -> bool
where
    RI: IntoIterator<Item = &'a BoundContainmentRule>,
{
    let common = matches!(
        disambiguated_pos,
        DisambiguatedBoundContainmentPosition::Equal | DisambiguatedBoundContainmentPosition::Inside,
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
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'allow on end' rule](BoundContainmentRule::AllowOnEnd)
#[must_use]
pub fn allow_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'allow on bounds' rule](BoundContainmentRule::AllowOnBounds)
#[must_use]
pub fn allow_on_bounds_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running
        || matches!(
            disambiguated_pos,
            DisambiguatedBoundContainmentPosition::OnStart | DisambiguatedBoundContainmentPosition::OnEnd,
        )
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'deny on start' rule](BoundContainmentRule::DenyOnStart)
#[must_use]
pub fn deny_on_start_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'deny on end' rule](BoundContainmentRule::DenyOnEnd)
#[must_use]
pub fn deny_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedBoundPosition`] respects
/// [the 'deny on bounds' rule](BoundContainmentRule::DenyOnBounds)
#[must_use]
pub fn deny_on_bounds_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running
        && !matches!(
            disambiguated_pos,
            DisambiguatedBoundContainmentPosition::OnStart | DisambiguatedBoundContainmentPosition::OnEnd,
        )
}

/// Capacity to position a bound in an interval
///
/// We assume that the given bound comes from another interval than the one operated on.
pub trait CanPositionBoundContainment<B> {
    /// Returns the bound position of the given bound
    #[must_use]
    fn bound_position(&self, bound: &B) -> BoundContainmentPosition;

    /// Returns the disambiguated bound position of the given bound using the given rule set
    #[must_use]
    fn disambiguated_bound_position(
        &self,
        bound: &B,
        rule_set: BoundContainmentRuleSet,
    ) -> DisambiguatedBoundContainmentPosition {
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
        F: FnOnce(BoundContainmentPosition) -> bool,
    {
        (f)(self.bound_position(bound))
    }

    /// Returns whether the given bound is contained in the interval using the given closure
    /// with a disambiguated position
    #[must_use]
    fn contains_using_simple<F>(&self, bound: &B, rule_set: BoundContainmentRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedBoundContainmentPosition) -> bool,
    {
        (f)(self.disambiguated_bound_position(bound, rule_set))
    }
}

impl<T> CanPositionBoundContainment<AbsoluteStartBound> for T
where
    T: HasEmptiableAbsoluteBounds,
{
    fn bound_position(&self, bound: &AbsoluteStartBound) -> BoundContainmentPosition {
        bound_position_abs_start_bound_on_emptiable_abs_bounds(&self.emptiable_abs_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteStartBound`] within the given [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_start_bound_on_emptiable_abs_bounds(
    emptiable_abs_bounds: &EmptiableAbsoluteBounds,
    abs_start_bound: &AbsoluteStartBound,
) -> BoundContainmentPosition {
    let EmptiableAbsoluteBounds::Bound(abs_bounds) = emptiable_abs_bounds else {
        return BoundContainmentPosition::Outside;
    };

    bound_position_abs_start_bound_on_abs_bounds(abs_bounds, abs_start_bound)
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteStartBound`] within the given [`AbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_start_bound_on_abs_bounds(
    abs_bounds: &AbsoluteBounds,
    abs_start_bound: &AbsoluteStartBound,
) -> BoundContainmentPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;

    match (abs_bounds.start(), abs_bounds.end(), abs_start_bound) {
        (StartB::InfinitePast, _, StartB::InfinitePast) => BoundContainmentPosition::OnStart(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, StartB::Finite(_)) => BoundContainmentPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), StartB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_end.time()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::EndStart(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(_), _, StartB::InfinitePast) => BoundContainmentPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, StartB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_start.time()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
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
                (Ordering::Less, _) => BoundContainmentPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundContainmentPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundContainmentPosition::Equal,
                    BoundInclusivity::Exclusive => BoundContainmentPosition::OutsideBefore,
                },
                (Ordering::Equal, Ordering::Less) => BoundContainmentPosition::OnStart(Some(
                    BoundOverlapAmbiguity::BothStarts(finite_start.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Equal) => BoundContainmentPosition::OnEnd(Some(
                    BoundOverlapAmbiguity::EndStart(finite_end.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Less) => BoundContainmentPosition::Inside,
            }
        },
    }
}

impl<T> CanPositionBoundContainment<AbsoluteEndBound> for T
where
    T: HasEmptiableAbsoluteBounds,
{
    fn bound_position(&self, bound: &AbsoluteEndBound) -> BoundContainmentPosition {
        bound_position_abs_end_bound_on_emptiable_abs_bounds(&self.emptiable_abs_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteEndBound`] within the given [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_end_bound_on_emptiable_abs_bounds(
    emptiable_abs_bounds: &EmptiableAbsoluteBounds,
    abs_end_bound: &AbsoluteEndBound,
) -> BoundContainmentPosition {
    let EmptiableAbsoluteBounds::Bound(abs_bounds) = emptiable_abs_bounds else {
        return BoundContainmentPosition::Outside;
    };

    bound_position_abs_end_bound_on_abs_bounds(abs_bounds, abs_end_bound)
}

/// Returns the [`BoundPosition`] of the given [`AbsoluteEndBound`] within the given [`AbsoluteBounds`]
#[must_use]
pub fn bound_position_abs_end_bound_on_abs_bounds(
    abs_bounds: &AbsoluteBounds,
    abs_end_bound: &AbsoluteEndBound,
) -> BoundContainmentPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;

    match (abs_bounds.start(), abs_bounds.end(), abs_end_bound) {
        (_, EndB::InfiniteFuture, EndB::InfiniteFuture) => BoundContainmentPosition::OnEnd(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, EndB::Finite(_)) => BoundContainmentPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), EndB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_end.time()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::BothEnds(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (_, EndB::Finite(_), EndB::InfiniteFuture) => BoundContainmentPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, EndB::Finite(finite_bound)) => {
            match finite_bound.time().cmp(&finite_start.time()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::StartEnd(
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
                (Ordering::Less, _) => BoundContainmentPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundContainmentPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundContainmentPosition::Equal,
                    BoundInclusivity::Exclusive => BoundContainmentPosition::OutsideAfter,
                },
                (Ordering::Equal, Ordering::Less) => BoundContainmentPosition::OnStart(Some(
                    BoundOverlapAmbiguity::StartEnd(finite_start.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Equal) => BoundContainmentPosition::OnEnd(Some(
                    BoundOverlapAmbiguity::BothEnds(finite_end.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Less) => BoundContainmentPosition::Inside,
            }
        },
    }
}

impl<T> CanPositionBoundContainment<RelativeStartBound> for T
where
    T: HasEmptiableRelativeBounds,
{
    fn bound_position(&self, bound: &RelativeStartBound) -> BoundContainmentPosition {
        bound_position_rel_start_bound_on_emptiable_rel_bounds(&self.emptiable_rel_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`RelativeStartBound`] within the given [`EmptiableRelativeBounds`]
#[must_use]
pub fn bound_position_rel_start_bound_on_emptiable_rel_bounds(
    emptiable_rel_bounds: &EmptiableRelativeBounds,
    rel_start_bound: &RelativeStartBound,
) -> BoundContainmentPosition {
    let EmptiableRelativeBounds::Bound(rel_bounds) = emptiable_rel_bounds else {
        return BoundContainmentPosition::Outside;
    };

    bound_position_rel_start_bound_on_rel_bounds(rel_bounds, rel_start_bound)
}

/// Returns the [`BoundPosition`] of the given [`RelativeStartBound`] within the given [`RelativeBounds`]
#[must_use]
pub fn bound_position_rel_start_bound_on_rel_bounds(
    rel_bounds: &RelativeBounds,
    rel_start_bound: &RelativeStartBound,
) -> BoundContainmentPosition {
    type StartB = RelativeStartBound;
    type EndB = RelativeEndBound;

    match (rel_bounds.start(), rel_bounds.end(), rel_start_bound) {
        (StartB::InfinitePast, _, StartB::InfinitePast) => BoundContainmentPosition::OnStart(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, StartB::Finite(_)) => BoundContainmentPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), StartB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_end.offset()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::EndStart(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(_), _, StartB::InfinitePast) => BoundContainmentPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, StartB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_start.offset()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
                    finite_start.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(finite_start), EndB::Finite(finite_end), StartB::Finite(finite_bound)) => {
            match (
                finite_bound.offset().cmp(&finite_start.offset()),
                finite_bound.offset().cmp(&finite_end.offset()),
            ) {
                (Ordering::Less, _) => BoundContainmentPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundContainmentPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundContainmentPosition::Equal,
                    BoundInclusivity::Exclusive => BoundContainmentPosition::OutsideBefore,
                },
                (Ordering::Equal, Ordering::Less) => BoundContainmentPosition::OnStart(Some(
                    BoundOverlapAmbiguity::BothStarts(finite_start.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Equal) => BoundContainmentPosition::OnEnd(Some(
                    BoundOverlapAmbiguity::EndStart(finite_end.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Less) => BoundContainmentPosition::Inside,
            }
        },
    }
}

impl<T> CanPositionBoundContainment<RelativeEndBound> for T
where
    T: HasEmptiableRelativeBounds,
{
    fn bound_position(&self, bound: &RelativeEndBound) -> BoundContainmentPosition {
        bound_position_rel_end_bound_on_emptiable_rel_bounds(&self.emptiable_rel_bounds(), bound)
    }
}

/// Returns the [`BoundPosition`] of the given [`RelativeEndBound`] within the given [`EmptiableRelativeBounds`]
#[must_use]
pub fn bound_position_rel_end_bound_on_emptiable_rel_bounds(
    emptiable_rel_bounds: &EmptiableRelativeBounds,
    rel_end_bound: &RelativeEndBound,
) -> BoundContainmentPosition {
    let EmptiableRelativeBounds::Bound(rel_bounds) = emptiable_rel_bounds else {
        return BoundContainmentPosition::Outside;
    };

    bound_position_rel_end_bound_on_rel_bounds(rel_bounds, rel_end_bound)
}

/// Returns the [`BoundPosition`] of the given [`RelativeEndBound`] within the given [`RelativeBounds`]
#[must_use]
pub fn bound_position_rel_end_bound_on_rel_bounds(
    rel_bounds: &RelativeBounds,
    rel_end_bound: &RelativeEndBound,
) -> BoundContainmentPosition {
    type StartB = RelativeStartBound;
    type EndB = RelativeEndBound;

    match (rel_bounds.start(), rel_bounds.end(), rel_end_bound) {
        (_, EndB::InfiniteFuture, EndB::InfiniteFuture) => BoundContainmentPosition::OnEnd(None),
        (StartB::InfinitePast, EndB::InfiniteFuture, EndB::Finite(_)) => BoundContainmentPosition::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_end), EndB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_end.offset()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::BothEnds(
                    finite_end.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (_, EndB::Finite(_), EndB::InfiniteFuture) => BoundContainmentPosition::OutsideBefore,
        (StartB::Finite(finite_start), EndB::InfiniteFuture, EndB::Finite(finite_bound)) => {
            match finite_bound.offset().cmp(&finite_start.offset()) {
                Ordering::Less => BoundContainmentPosition::Inside,
                Ordering::Greater => BoundContainmentPosition::OutsideAfter,
                Ordering::Equal => BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::StartEnd(
                    finite_start.inclusivity(),
                    finite_bound.inclusivity(),
                ))),
            }
        },
        (StartB::Finite(finite_start), EndB::Finite(finite_end), EndB::Finite(finite_bound)) => {
            match (
                finite_bound.offset().cmp(&finite_start.offset()),
                finite_bound.offset().cmp(&finite_end.offset()),
            ) {
                (Ordering::Less, _) => BoundContainmentPosition::OutsideBefore,
                (_, Ordering::Greater) => BoundContainmentPosition::OutsideAfter,
                (Ordering::Equal, Ordering::Equal) => match finite_bound.inclusivity() {
                    BoundInclusivity::Inclusive => BoundContainmentPosition::Equal,
                    BoundInclusivity::Exclusive => BoundContainmentPosition::OutsideAfter,
                },
                (Ordering::Equal, Ordering::Less) => BoundContainmentPosition::OnStart(Some(
                    BoundOverlapAmbiguity::StartEnd(finite_start.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Equal) => BoundContainmentPosition::OnEnd(Some(
                    BoundOverlapAmbiguity::BothEnds(finite_end.inclusivity(), finite_bound.inclusivity()),
                )),
                (Ordering::Greater, Ordering::Less) => BoundContainmentPosition::Inside,
            }
        },
    }
}

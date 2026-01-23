//! Bound containment positioning
//!
//! Bound containment positioning is the act of positioning _how_ a bound is contained within an interval.
//!
//! The position of the bound is given by [`BoundContainmentPosition`].
//! Since [bound overlap ambiguities](BoundOverlapAmbiguity) can be created, the module provides ways to disambiguate
//! that position, using either your own closure to do that, or a [`BoundContainmentRuleSet`],
//! describing the rule set used for the disambiguation.
//!
//! Once disambiguated, you obtain a [`DisambiguatedBoundContainmentPosition`] that can then be converted
//! to a clear boolean diagnostic of whether the bound is consider _contained_ or not by the interval
//! using [`BoundContainmentRule`]s.

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use super::prelude::*;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeStartBound};
use crate::intervals::{AbsoluteBounds, EmptiableAbsoluteBounds, EmptiableRelativeBounds};

/// Bound position relative to an interval
///
/// Indicates where the bound is situated compared to a given interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum BoundContainmentPosition {
    /// Bound was found before the interval's start
    OutsideBefore,
    /// Bound was found after the interval's end
    OutsideAfter,
    /// Bound was found outside the interval
    ///
    /// This result is only possible when dealing with empty intervals.
    Outside,
    /// Bound was found on the start of the interval
    ///
    /// The bound ambiguity is stored within this variant.
    ///
    /// The bound ambiguity is stored within an [`Option`] because infinite bounds can result in
    /// [`OnStart`](BoundContainmentPosition::OnStart) / [`OnEnd`](BoundContainmentPosition::OnEnd)
    /// positions unambiguously.
    OnStart(Option<BoundOverlapAmbiguity>),
    /// The given bound was found exactly on the end of the interval
    ///
    /// The ambiguity is stored within this variant.
    ///
    /// The bound ambiguity is stored within an [`Option`] because infinite bounds can result in
    /// [`OnStart`](BoundContainmentPosition::OnStart) / [`OnEnd`](BoundContainmentPosition::OnEnd)
    /// positions unambiguously.
    OnEnd(Option<BoundOverlapAmbiguity>),
    /// Bound was found exactly on the start and end of the interval
    ///
    /// This result is only possible when the given bound is inclusive and the interval is a single point in time
    /// with inclusive bounds.
    Equal,
    /// Bound was found inside the interval
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

    /// Uses a rule set to transform the bound position into a disambiguated one
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_containment::{
    /// #     CanPositionBoundContainment, BoundContainmentRuleSet, DisambiguatedBoundContainmentPosition,
    /// # };
    /// let bounds = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    ///
    /// let end_bound = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?
    /// ));
    ///
    /// let bound_position = bounds.bound_position(&end_bound);
    ///
    /// assert_eq!(
    ///     bound_position.disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
    ///     DisambiguatedBoundContainmentPosition::OutsideAfter,
    /// );
    /// assert_eq!(
    ///     bound_position.disambiguate_using_rule_set(BoundContainmentRuleSet::Lenient),
    ///     DisambiguatedBoundContainmentPosition::OnEnd,
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn disambiguate_using_rule_set(
        self,
        rule_set: BoundContainmentRuleSet,
    ) -> DisambiguatedBoundContainmentPosition {
        rule_set.disambiguate(self)
    }
}

/// Disambiguated [`BoundContainmentPosition`]
///
/// Indicates where the bound is situated compared to a given interval without any ambiguity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum DisambiguatedBoundContainmentPosition {
    /// See [`OutsideBefore`](BoundContainmentPosition::OutsideBefore)
    OutsideBefore,
    /// See [`OutsideAfter`](BoundContainmentPosition::OutsideAfter)
    OutsideAfter,
    /// See [`Outside`](BoundContainmentPosition::Outside)
    Outside,
    /// See [`OnStart`](BoundContainmentPosition::OnStart)
    OnStart,
    /// See [`OnEnd`](BoundContainmentPosition::OnEnd)
    OnEnd,
    /// See [`Equal`](BoundContainmentPosition::Equal)
    Equal,
    /// See [`Inside`](BoundContainmentPosition::Inside)
    Inside,
}

/// Rule sets for disambiguating a [`BoundContainmentPosition`]
///
/// See [`contains_bound`](CanPositionBoundContainment::contains_bound) for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum BoundContainmentRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds.
    ///
    /// Two bounds possessing the same point in time need to be inclusive in order to be counted as equal.
    ///
    /// See [`BoundOverlapDisambiguationRuleSet::Strict`].
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// Two bounds possessing the same point in time need to be either inclusive or at least one of them
    /// needs to be exclusive (not both!) in order to be counted as equal.
    ///
    /// See [`BoundOverlapDisambiguationRuleSet::Lenient`].
    Lenient,
    /// Very lenient rule set
    ///
    /// Two bounds possessing the same point in time are counted as equal, regardless of the inclusivity.
    ///
    /// See [`BoundOverlapDisambiguationRuleSet::VeryLenient`].
    VeryLenient,
    /// Continuous to future rule set
    ///
    /// Follows the same principles as [`BoundContainmentRuleSet::Strict`], but adds an exception:
    /// if an exclusive end bound is adjacent to an inclusive start bound, it also counts as equal.
    ///
    /// See [`BoundOverlapDisambiguationRuleSet::ContinuousToFuture`].
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Follows the same principles as [`BoundContainmentRuleSet::Strict`], but adds an exception:
    /// if an exclusive start bound is adjacent to an inclusive end bound, it also counts as equal.
    ///
    /// See [`BoundOverlapDisambiguationRuleSet::ContinuousToFuture`].
    ContinuousToPast,
}

impl BoundContainmentRuleSet {
    /// Disambiguates a [`BoundContainmentPosition`] according to the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_containment::{
    /// #     BoundContainmentPosition, BoundContainmentRuleSet, DisambiguatedBoundContainmentPosition,
    /// # };
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// let bound_position = BoundContainmentPosition::OnStart(
    ///     Some(BoundOverlapAmbiguity::StartEnd(
    ///         BoundInclusivity::Inclusive,
    ///         BoundInclusivity::Exclusive,
    ///     ))
    /// );
    ///
    /// let disambiguated_bound_position = BoundContainmentRuleSet::Strict.disambiguate(bound_position);
    ///
    /// assert_eq!(
    ///     disambiguated_bound_position,
    ///     DisambiguatedBoundContainmentPosition::OutsideBefore,
    /// );
    /// ```
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

/// Disambiguates a [`BoundContainmentPosition`] using the given [`BoundOverlapDisambiguationRuleSet`]
///
/// Converts the unambiguous [`BoundContainmentPosition`]s into [`DisambiguatedBoundContainmentPosition`].
/// For ambiguous [`BoundContainmentPosition`]s, uses the given [`BoundOverlapDisambiguationRuleSet`]
/// to disambiguate the inner ambiguity before converting the result in a [`DisambiguatedBoundContainmentPosition`].
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

/// Rules for determining what counts as containment
///
/// Those rules are used to convert a [`DisambiguatedBoundContainmentPosition`] into a boolean indicating
/// whether the bound is contained within the interval or not, according to the given rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum BoundContainmentRule {
    /// Counts as contained when the bound is on the start of the interval
    AllowOnStart,
    /// Counts as contained when the bound is on the end of the interval
    AllowOnEnd,
    /// Counts as contained when the bound is either on the start or the end of the interval
    AllowOnBounds,
    /// Doesn't count as contained when the bound is on the start of the interval
    DenyOnStart,
    /// Doesn't count as contained when the bound is on the end of the interval
    DenyOnEnd,
    /// Doesn't count as contained when the bound is either on the start or the end of the interval
    DenyOnBounds,
}

impl BoundContainmentRule {
    /// Returns the next state of the running containment decision
    ///
    /// This method takes the running containment decision and the [`DisambiguatedBoundContainmentPosition`]
    /// and returns the next state of the running containment decision.
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

/// Checks all given rules and returns the final boolean regarding bound containment
///
/// Iterates over the given rules and [fold](Iterator::fold) them with [`BoundContainmentRule::counts_as_contained`]
/// in order to get the final boolean regarding whether the bound should be considered contained.
///
/// This method also contains the common logic of considering
/// an [`Equal`](DisambiguatedBoundContainmentPosition::Equal)
/// or [`Inside`](DisambiguatedBoundContainmentPosition::Inside) [`DisambiguatedBoundContainmentPosition`]
/// as being contained.
///
/// If conflicting rules are provided, for example [`AllowOnStart`](BoundContainmentRule::AllowOnStart)
/// and [`DenyOnStart`](BoundContainmentRule::DenyOnStart), the one appearing last is the one taking priority.
///
/// Don't use this method directly, use [`CanPositionBoundContainment::contains_bound`] instead.
///
/// # Examples
///
/// ```
/// # use periodical::intervals::ops::bound_containment::{
/// #     BoundContainmentRule, check_bound_containment_rules, DisambiguatedBoundContainmentPosition,
/// # };
/// let disambiguated_pos = DisambiguatedBoundContainmentPosition::OnStart;
///
/// let deny_on_bounds_diagnostic = check_bound_containment_rules(
///     disambiguated_pos,
///     &[BoundContainmentRule::DenyOnBounds],
/// );
/// let allow_on_bounds_diagnostic = check_bound_containment_rules(
///     disambiguated_pos,
///     &[BoundContainmentRule::AllowOnBounds],
/// );
///
/// assert!(!deny_on_bounds_diagnostic);
/// assert!(allow_on_bounds_diagnostic);
/// ```
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

/// Checks whether the given [`DisambiguatedBoundContainmentPosition`] respects
/// the [`AllowOnStart`](BoundContainmentRule::AllowOnStart) rule
#[must_use]
pub fn allow_on_start_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedBoundContainmentPosition`] respects
/// the [`AllowOnEnd`](BoundContainmentRule::AllowOnEnd) rule
#[must_use]
pub fn allow_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedBoundContainmentPosition`] respects
/// the [`AllowOnBounds`](BoundContainmentRule::AllowOnBounds) rule
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

/// Checks whether the given [`DisambiguatedBoundContainmentPosition`] respects
/// the [`DenyOnStart`](BoundContainmentRule::DenyOnStart) rule
#[must_use]
pub fn deny_on_start_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedBoundContainmentPosition`] respects
/// the [`DenyOnEnd`](BoundContainmentRule::DenyOnEnd) rule
#[must_use]
pub fn deny_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedBoundContainmentPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedBoundContainmentPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedBoundContainmentPosition`] respects
/// the [`DenyOnBounds`](BoundContainmentRule::DenyOnBounds) rule
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
/// # Examples
///
/// ## Fetching the disambiguated position of a bound
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::bound_containment::{
/// #     BoundContainmentRuleSet, CanPositionBoundContainment, DisambiguatedBoundContainmentPosition,
/// # };
/// let interval = BoundedAbsoluteInterval::new(
///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
/// );
///
/// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     BoundInclusivity::Exclusive,
/// ));
///
/// let pos = interval.disambiguated_bound_position(&bound, BoundContainmentRuleSet::Lenient);
///
/// assert_eq!(pos, DisambiguatedBoundContainmentPosition::OnStart);
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
///
/// ## Checking if a bound is contained in an interval
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
/// # use periodical::intervals::ops::bound_containment::{
/// #     CanPositionBoundContainment, DisambiguatedBoundContainmentPosition,
/// # };
/// let interval = BoundedAbsoluteInterval::new(
///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
/// );
///
/// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///     "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?
/// ));
///
/// assert!(interval.simple_contains_bound(&bound));
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait CanPositionBoundContainment<B> {
    /// Returns the bound position relative to the interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_containment::{BoundContainmentPosition, CanPositionBoundContainment};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// let interval = BoundedAbsoluteInterval::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    /// );
    ///
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// let pos = interval.bound_position(&bound);
    ///
    /// assert_eq!(
    ///     pos,
    ///     BoundContainmentPosition::OnStart(
    ///         Some(BoundOverlapAmbiguity::BothStarts(
    ///             BoundInclusivity::Inclusive,
    ///             BoundInclusivity::Exclusive,
    ///         ))
    ///     ),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn bound_position(&self, bound: &B) -> BoundContainmentPosition;

    /// Returns the disambiguated bound position of the given bound using the given rule set
    ///
    /// Uses [`BoundContainmentPosition::disambiguate_using_rule_set`] under the hood.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_containment::{
    /// #     BoundContainmentRuleSet, CanPositionBoundContainment, DisambiguatedBoundContainmentPosition,
    /// # };
    /// let interval = BoundedAbsoluteInterval::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    /// );
    ///
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// let pos = interval.disambiguated_bound_position(&bound, BoundContainmentRuleSet::Lenient);
    ///
    /// assert_eq!(pos, DisambiguatedBoundContainmentPosition::OnStart);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
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
    /// Uses the [default rule set](BoundContainmentRuleSet::default)
    /// with [default rules](DEFAULT_BOUND_CONTAINMENT_RULES)
    /// in [`contains_bound`](CanPositionBoundContainment::contains_bound).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_containment::CanPositionBoundContainment;
    /// let interval = BoundedAbsoluteInterval::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    /// );
    ///
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// assert!(interval.simple_contains_bound(&bound));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn simple_contains_bound(&self, bound: &B) -> bool {
        self.contains_bound(
            bound,
            BoundContainmentRuleSet::default(),
            &DEFAULT_BOUND_CONTAINMENT_RULES,
        )
    }

    /// Returns whether the given bound is contained in the interval
    /// using the given [containment rules](BoundContainmentRule)
    ///
    /// Uses [`check_bound_containment_rules`] under the hood.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_containment::{
    /// #     BoundContainmentRule, BoundContainmentRuleSet, CanPositionBoundContainment,
    /// # };
    /// let interval = BoundedAbsoluteInterval::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    /// );
    ///
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// let is_contained = interval.contains_bound(
    ///     &bound,
    ///     BoundContainmentRuleSet::Lenient,
    ///     &[BoundContainmentRule::AllowOnStart]
    /// );
    ///
    /// assert!(is_contained);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn contains_bound<'a, RI>(&self, bound: &B, rule_set: BoundContainmentRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a BoundContainmentRule>,
    {
        check_bound_containment_rules(self.disambiguated_bound_position(bound, rule_set), rules)
    }

    /// Returns whether the given bound is contained in the interval using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
    /// # use periodical::intervals::ops::bound_containment::CanPositionBoundContainment;
    /// let interval = BoundedAbsoluteInterval::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    /// );
    ///
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?
    /// ));
    ///
    /// let is_contained = interval.contains_bound_using(
    ///     &bound,
    ///     |_bound| false
    /// );
    ///
    /// assert!(!is_contained);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn contains_bound_using<F>(&self, bound: &B, f: F) -> bool
    where
        F: FnOnce(BoundContainmentPosition) -> bool,
    {
        (f)(self.bound_position(bound))
    }

    /// Returns whether the given bound is contained in the interval using the given closure
    /// with a disambiguated position
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval};
    /// # use periodical::intervals::ops::bound_containment::{
    /// #     BoundContainmentRuleSet, CanPositionBoundContainment,
    /// # };
    /// let interval = BoundedAbsoluteInterval::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    /// );
    ///
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?
    /// ));
    ///
    /// let is_contained = interval.contains_bound_using_simple(
    ///     &bound,
    ///     BoundContainmentRuleSet::Lenient,
    ///     |_disambiguated_bound| false
    /// );
    ///
    /// assert!(!is_contained);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn contains_bound_using_simple<F>(&self, bound: &B, rule_set: BoundContainmentRuleSet, f: F) -> bool
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

/// Returns the [`BoundContainmentPosition`] of an [`AbsoluteStartBound`] relative to an [`EmptiableAbsoluteBounds`]
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

/// Returns the [`BoundContainmentPosition`] of an [`AbsoluteStartBound`] relative to an [`AbsoluteBounds`]
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

/// Returns the [`BoundContainmentPosition`] of an [`AbsoluteEndBound`] relative to an [`EmptiableAbsoluteBounds`]
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

/// Returns the [`BoundContainmentPosition`] of an [`AbsoluteEndBound`] relative to an [`AbsoluteBounds`]
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

/// Returns the [`BoundContainmentPosition`] of a [`RelativeStartBound`] relative to an [`EmptiableRelativeBounds`]
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

/// Returns the [`BoundContainmentPosition`] of a [`RelativeStartBound`] relative to a [`RelativeBounds`]
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

/// Returns the [`BoundContainmentPosition`] of a [`RelativeEndBound`] relative to an [`EmptiableRelativeBounds`]
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

/// Returns the [`BoundContainmentPosition`] of a [`RelativeEndBound`] relative to a [`RelativeBounds`]
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

//! Interval overlap positioning
//!
//! Given two intervals, positions the overlap, represented by [`OverlapPosition`].
//!
//! Like [`BoundOverlapAmbiguity`], since two intervals can be adjacent and "meet" at a given point,
//! it creates an ambiguity due to the [`BoundInclusivity`](crate::intervals::meta::BoundInclusivity)
//! of the intervals.
//!
//! Using [`CanPositionOverlap`] will return an [`OverlapPosition`], which will then need to be disambiguated
//! in order to obtain a concrete diagnostic of the overlap.
//!
//! You can disambiguate an [`OverlapPosition`] using an [`OverlapRuleSet`] or a custom closure
//! by using [`OverlapPosition::disambiguate_using`].
//!
//! A disambiguated [`OverlapPosition`] is represented by [`DisambiguatedOverlapPosition`].
//!
//! Once disambiguated, the overlap position can be converted into a boolean decision of whether the two intervals
//! overlap according to your definition, using [`OverlapRule`]s with [`CanPositionOverlap::overlaps`].
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::intervals::ops::overlap::CanPositionOverlap;
//! let first_interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! let second_interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! assert!(first_interval.simple_overlaps(&second_interval));
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::cmp::Ordering;
use std::convert::Infallible;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfBoundedAbsoluteInterval, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfBoundedRelativeInterval, HasEmptiableRelativeBounds, RelativeBounds, RelativeEndBound,
    RelativeFiniteBound, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{AbsoluteInterval, BoundedAbsoluteInterval, BoundedRelativeInterval, RelativeInterval};

/// Overlap position
///
/// Defines where the compared interval was found relative to the reference interval.
///
/// When [`overlap_position`](CanPositionOverlap::overlap_position) evaluates the overlap position,
/// it ignores the [inclusivities](crate::intervals::meta::BoundInclusivity) of the intervals
/// and simply takes into account the position of the bounds.
///
/// If two bounds are adjacent, a [`BoundOverlapAmbiguity`] is created
/// and then stored in the right variant of [`OverlapPosition`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum OverlapPosition {
    /// Compared interval is before the reference interval
    OutsideBefore,
    /// Compared interval is after the reference interval
    OutsideAfter,
    /// Compared interval is outside the reference interval
    ///
    /// This result is only possible when dealing with empty intervals, as an empty interval does not have
    /// a position in time.
    Outside,
    /// Compared interval ends on the start of the reference interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the [`BoundOverlapAmbiguity`].
    EndsOnStart(BoundOverlapAmbiguity),
    /// Compared interval starts on the end of the reference interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the [`BoundOverlapAmbiguity`].
    StartsOnEnd(BoundOverlapAmbiguity),
    /// Compared interval crosses the start of the reference interval
    ///
    /// The compared interval ends within the reference interval,
    /// otherwise the overlap position would be [`Contains`](OverlapPosition::Contains).
    CrossesStart,
    /// Compared interval crosses the end of the reference interval
    ///
    /// The compared interval starts within the reference interval,
    /// otherwise the overlap position would be [`Contains`](OverlapPosition::Contains).
    CrossesEnd,
    /// Compared interval is inside the reference interval
    Inside,
    /// Compared interval is inside the reference interval and both have the same start
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can result
    /// in such an overlap position with no finite bounds involved, hence the [`BoundOverlapAmbiguity`]
    /// being wrapped in an [`Option`].
    InsideAndSameStart(Option<BoundOverlapAmbiguity>),
    /// Compared interval is inside the reference interval and both have the same end
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can result
    /// in such an overlap position with no finite bounds involved, hence the [`BoundOverlapAmbiguity`]
    /// being wrapped in an [`Option`].
    InsideAndSameEnd(Option<BoundOverlapAmbiguity>),
    /// Compared interval is equal to the reference interval
    ///
    /// Since two pairs of bounds are overlapping, this creates an ambiguity,
    /// hence the pair of [`BoundOverlapAmbiguity`].
    ///
    /// Since half-bounded intervals only have a single defined bound, the second ambiguity
    /// is wrapped in an [`Option`].
    /// Also, when you compare two unbounded intervals, neither have defined bounds, but still are equal,
    /// so both [`BoundOverlapAmbiguity`] are wrapped in [`Option`].
    ///
    /// # Invariants
    ///
    /// The second [`Option`] can never be [`Some`] if the first [`Option`] is [`None`].
    Equal(Option<BoundOverlapAmbiguity>, Option<BoundOverlapAmbiguity>),
    /// Compared interval contains the reference interval and both have the same start
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can result
    /// in such an overlap position with no finite bounds involved, hence the [`BoundOverlapAmbiguity`]
    /// being wrapped in an [`Option`].
    ContainsAndSameStart(Option<BoundOverlapAmbiguity>),
    /// Compared interval contains the reference interval and both have the same end
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can result
    /// in such an overlap position with no finite bounds involved, hence the [`BoundOverlapAmbiguity`]
    /// being wrapped in an [`Option`].
    ContainsAndSameEnd(Option<BoundOverlapAmbiguity>),
    /// Compared interval fully contains the reference interval
    Contains,
}

impl OverlapPosition {
    /// Strips information about bound ambiguities and conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// # use periodical::intervals::ops::overlap::{DisambiguatedOverlapPosition, OverlapPosition};
    /// assert_eq!(
    ///     OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::StartEnd(
    ///         BoundInclusivity::Exclusive,
    ///         BoundInclusivity::Exclusive,
    ///     )).strip(),
    ///     DisambiguatedOverlapPosition::EndsOnStart,
    /// );
    /// ```
    #[must_use]
    pub fn strip(self) -> DisambiguatedOverlapPosition {
        match self {
            OverlapPosition::OutsideBefore => DisambiguatedOverlapPosition::OutsideBefore,
            OverlapPosition::OutsideAfter => DisambiguatedOverlapPosition::OutsideAfter,
            OverlapPosition::Outside => DisambiguatedOverlapPosition::Outside,
            OverlapPosition::EndsOnStart(..) => DisambiguatedOverlapPosition::EndsOnStart,
            OverlapPosition::StartsOnEnd(..) => DisambiguatedOverlapPosition::StartsOnEnd,
            OverlapPosition::CrossesStart => DisambiguatedOverlapPosition::CrossesStart,
            OverlapPosition::CrossesEnd => DisambiguatedOverlapPosition::CrossesEnd,
            OverlapPosition::Inside => DisambiguatedOverlapPosition::Inside,
            OverlapPosition::InsideAndSameStart(..) => DisambiguatedOverlapPosition::InsideAndSameStart,
            OverlapPosition::InsideAndSameEnd(..) => DisambiguatedOverlapPosition::InsideAndSameEnd,
            OverlapPosition::Equal(..) => DisambiguatedOverlapPosition::Equal,
            OverlapPosition::ContainsAndSameStart(..) => DisambiguatedOverlapPosition::ContainsAndSameStart,
            OverlapPosition::ContainsAndSameEnd(..) => DisambiguatedOverlapPosition::ContainsAndSameEnd,
            OverlapPosition::Contains => DisambiguatedOverlapPosition::Contains,
        }
    }

    /// Disambiguates using an [`OverlapRuleSet`]
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// # use periodical::intervals::ops::overlap::{DisambiguatedOverlapPosition, OverlapPosition, OverlapRuleSet};
    /// let pos = OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::StartEnd(
    ///     BoundInclusivity::Exclusive,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert_eq!(
    ///     pos.disambiguate_using_rule_set(OverlapRuleSet::VeryLenient),
    ///     DisambiguatedOverlapPosition::EndsOnStart,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: OverlapRuleSet) -> DisambiguatedOverlapPosition {
        rule_set.disambiguate(self)
    }

    /// Uses the given closure to disambiguate the [`OverlapPosition`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// # use periodical::intervals::ops::overlap::{DisambiguatedOverlapPosition, OverlapPosition};
    /// let pos = OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::StartEnd(
    ///     BoundInclusivity::Inclusive,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// let disambiguation_closure = |position: OverlapPosition| -> DisambiguatedOverlapPosition {
    ///     match position {
    ///         OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::StartEnd(i1, i2)) => {
    ///             if matches!(
    ///                 (i1, i2),
    ///                 (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
    ///             ) {
    ///                 DisambiguatedOverlapPosition::EndsOnStart
    ///             } else {
    ///                 DisambiguatedOverlapPosition::OutsideBefore
    ///             }
    ///         },
    ///         _ => unimplemented!(),
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     pos.disambiguate_using(disambiguation_closure),
    ///     DisambiguatedOverlapPosition::EndsOnStart,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate_using<F>(self, f: F) -> DisambiguatedOverlapPosition
    where
        F: FnOnce(OverlapPosition) -> DisambiguatedOverlapPosition,
    {
        (f)(self)
    }
}

/// Disambiguated [`OverlapPosition`]
///
/// Indicates where the overlap is situated compared to the reference interval without any ambiguity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum DisambiguatedOverlapPosition {
    /// See [`OverlapPosition::OutsideBefore`]
    OutsideBefore,
    /// See [`OverlapPosition::OutsideAfter`]
    OutsideAfter,
    /// See [`OverlapPosition::Outside`]
    Outside,
    /// See [`OverlapPosition::EndsOnStart`]
    EndsOnStart,
    /// See [`OverlapPosition::StartsOnEnd`]
    StartsOnEnd,
    /// See [`OverlapPosition::CrossesStart`]
    CrossesStart,
    /// See [`OverlapPosition::CrossesEnd`]
    CrossesEnd,
    /// See [`OverlapPosition::Inside`]
    Inside,
    /// See [`OverlapPosition::InsideAndSameStart`]
    InsideAndSameStart,
    /// See [`OverlapPosition::InsideAndSameEnd`]
    InsideAndSameEnd,
    /// See [`OverlapPosition::Equal`]
    Equal,
    /// See [`OverlapPosition::ContainsAndSameStart`]
    ContainsAndSameStart,
    /// See [`OverlapPosition::ContainsAndSameEnd`]
    ContainsAndSameEnd,
    /// See [`OverlapPosition::Contains`]
    Contains,
}

/// Rule sets for disambiguating an [`OverlapPosition`]
///
/// See [`overlaps`](CanPositionOverlap::overlaps) for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum OverlapRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds.
    ///
    /// # Overlap examples
    ///
    /// ```text
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:                 [-------]
    /// OutsideBefore       [------)       :
    /// OutsideAfter               :       (-----]
    /// InsideAndSameStart         [-------)
    /// InsideAndSameEnd           (-------]
    /// Inside                     (-------)
    /// ContainsAndSameStart       [----------)
    /// ContainsAndSameEnd      (----------]
    ///
    /// Reference:                 (-------)
    /// OutsideBefore       [------]       :
    /// OutsideAfter               :       [-----]
    /// Contains                   [-------]
    /// ContainsAndSameStart       (-------]
    /// ContainsAndSameEnd         [-------)
    /// Contains                 [---------]
    /// Contains                   [----------]
    /// ```
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// Two bounds possessing the same point in time need to be either inclusive or at least one of them
    /// needs to be exclusive (not both!) in order to be counted as equal.
    ///
    /// # Overlap examples
    ///
    /// ```text
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:                [------]
    /// StartsOnEnd               :      (-----]
    /// EndsOnStart         [-----)      :
    /// Equal                     (------]
    /// Equal                     [------)
    /// Equal                     (------)
    /// InsideAndSameStart        (---]  :
    /// InsideAndSameEnd          :  [---)
    /// ContainsAndSameStart      (----------]
    /// ContainsAndSameEnd    [----------)
    ///
    /// Reference:                (------)
    /// StartsOnEnd               :      [-----]
    /// EndsOnStart         [-----]      :
    /// Equal                     [------]
    /// Equal                     (------]
    /// Equal                     [------)
    /// InsideAndSameStart        [---]  :
    /// InsideAndSameEnd          :  [---]
    /// ContainsAndSameStart      [---------]
    /// ContainsAndSameEnd     [---------]
    /// ```
    Lenient,
    /// Very lenient rule set
    ///
    /// Two bounds possessing the same point in time are counted as equal, regardless of the inclusivity.
    VeryLenient,
    /// Continuous to future rule set
    ///
    /// Follows the same principles as [`OverlapRuleSet::Strict`], but adds an exception:
    /// if an exclusive end bound is adjacent to an inclusive start bound, it also counts as equal.
    ///
    /// # Overlap examples
    ///
    /// ```text
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            [------)
    /// EndsOnStart      [----)      :
    /// EndsOnStart      [----]      :
    /// StartsOnEnd           :      [-----]
    /// OutsideAfter          :      (-----]
    ///
    /// Reference:            (------]
    /// OutsideBefore    [----]      :
    /// OutsideBefore    [----)      :
    /// StartsOnEnd           :      [-----]
    /// OutsideAfter          :      (-----)
    /// ```
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Follows the same principles as [`OverlapRuleSet::Strict`], but adds an exception:
    /// if an exclusive start bound is adjacent to an inclusive end bound, it also counts as equal.
    ///
    /// # Overlap examples
    ///
    /// ```text
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            (------]
    /// EndsOnStart      [----]      :
    /// OutsideBefore    [----)      :
    /// StartsOnEnd           :      [-----]
    /// StartsOnEnd           :      (-----)
    ///
    /// Reference:            [------)
    /// OutsideBefore    [----)      :
    /// EndsOnStart      [----]      :
    /// OutsideAfter          :      [-----]
    /// OutsideAfter          :      (-----]
    /// ```
    ContinuousToPast,
}

impl OverlapRuleSet {
    /// Disambiguates an overlap position according to the rule set
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    ///
    /// Preferably use [`OverlapPosition::disambiguate_using_rule_set`] instead.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// # use periodical::intervals::ops::overlap::{DisambiguatedOverlapPosition, OverlapPosition, OverlapRuleSet};
    /// let pos = OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::StartEnd(
    ///     BoundInclusivity::Exclusive,
    ///     BoundInclusivity::Inclusive,
    /// ));
    ///
    /// assert_eq!(
    ///     OverlapRuleSet::Lenient.disambiguate(pos),
    ///     DisambiguatedOverlapPosition::EndsOnStart,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate(&self, overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
        type Bodrs = BoundOverlapDisambiguationRuleSet;

        match self {
            Self::Strict => overlap_position_disambiguation(overlap_position, Bodrs::Strict),
            Self::ContinuousToFuture => overlap_position_disambiguation(overlap_position, Bodrs::ContinuousToFuture),
            Self::ContinuousToPast => overlap_position_disambiguation(overlap_position, Bodrs::ContinuousToPast),
            Self::Lenient => overlap_position_disambiguation(overlap_position, Bodrs::Lenient),
            Self::VeryLenient => overlap_position_disambiguation(overlap_position, Bodrs::VeryLenient),
        }
    }
}

/// Disambiguates an [`OverlapPosition`] using the given [`BoundOverlapDisambiguationRuleSet`]
///
/// This method is primarily used by [`OverlapRuleSet::disambiguate`].
#[must_use]
pub fn overlap_position_disambiguation(
    overlap_position: OverlapPosition,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Dbo = DisambiguatedBoundOverlap;

    match overlap_position {
        Op::Outside => Dop::Outside,
        Op::OutsideBefore => Dop::OutsideBefore,
        Op::OutsideAfter => Dop::OutsideAfter,
        Op::EndsOnStart(ambiguity) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::CrossesStart,
                Dbo::Equal => Dop::EndsOnStart,
                Dbo::After => Dop::OutsideBefore,
            }
        },
        Op::StartsOnEnd(ambiguity) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::OutsideAfter,
                Dbo::Equal => Dop::StartsOnEnd,
                Dbo::After => Dop::CrossesEnd,
            }
        },
        Op::CrossesStart => Dop::CrossesStart,
        Op::CrossesEnd => Dop::CrossesEnd,
        Op::Inside => Dop::Inside,
        Op::InsideAndSameStart(None) => Dop::InsideAndSameStart,
        Op::InsideAndSameStart(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::Inside,
                Dbo::Equal => Dop::InsideAndSameStart,
                Dbo::After => Dop::CrossesStart,
            }
        },
        Op::Equal(None, None) => Dop::Equal,
        Op::Equal(Some(ambiguity), None) => overlap_position_bound_ambiguity_disambiguation_equal_half_bounded(
            ambiguity,
            bound_overlap_disambiguation_rule_set,
        ),
        Op::Equal(None, Some(_)) => {
            unreachable!(
                "When there is a bound ambiguity for an equal position for comparing two half-bounded intervals, \
                which produces a single bound ambiguity, the bound ambiguity is never stored in the second element \
                of the `OverlapPosition::Equal` variant"
            );
        },
        Op::Equal(Some(start_ambiguity), Some(end_ambiguity)) => {
            overlap_position_bound_ambiguity_disambiguation_equal_bounded(
                start_ambiguity,
                end_ambiguity,
                bound_overlap_disambiguation_rule_set,
            )
        },
        Op::InsideAndSameEnd(None) => Dop::InsideAndSameEnd,
        Op::InsideAndSameEnd(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::CrossesEnd,
                Dbo::Equal => Dop::InsideAndSameEnd,
                Dbo::After => Dop::Inside,
            }
        },
        Op::ContainsAndSameStart(None) => Dop::ContainsAndSameStart,
        Op::ContainsAndSameStart(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::CrossesEnd,
                Dbo::Equal => Dop::ContainsAndSameStart,
                Dbo::After => Dop::Contains,
            }
        },
        Op::ContainsAndSameEnd(None) => Dop::ContainsAndSameEnd,
        Op::ContainsAndSameEnd(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::Contains,
                Dbo::Equal => Dop::ContainsAndSameEnd,
                Dbo::After => Dop::CrossesStart,
            }
        },
        Op::Contains => Dop::Contains,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`] for the [`Equal`](OverlapPosition::Equal) position
/// of two half-bounded intervals
#[must_use]
pub fn overlap_position_bound_ambiguity_disambiguation_equal_half_bounded(
    ambiguity: BoundOverlapAmbiguity,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Dbo = DisambiguatedBoundOverlap;
    type Dop = DisambiguatedOverlapPosition;

    match ambiguity {
        BoundOverlapAmbiguity::BothStarts(..) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::InsideAndSameEnd,
                Dbo::Equal => Dop::Equal,
                Dbo::After => Dop::ContainsAndSameEnd,
            }
        },
        BoundOverlapAmbiguity::BothEnds(..) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::ContainsAndSameStart,
                Dbo::Equal => Dop::Equal,
                Dbo::After => Dop::InsideAndSameStart,
            }
        },
        BoundOverlapAmbiguity::StartEnd(..) | BoundOverlapAmbiguity::EndStart(..) => {
            unreachable!(
                "When there is a bound ambiguity for an equal position for comparing two half-bounded intervals, \
                which produces a single bound ambiguity, the bound ambiguity is always either BothStarts or \
                BothEnds, but never StartEnd nor EndStart"
            );
        },
    }
}

/// Disambiguates two [`BoundOverlapAmbiguity`] for the [`Equal`](OverlapPosition::Equal) position
/// of two bounded intervals
#[must_use]
pub fn overlap_position_bound_ambiguity_disambiguation_equal_bounded(
    start_ambiguity: BoundOverlapAmbiguity,
    end_ambiguity: BoundOverlapAmbiguity,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Dbo = DisambiguatedBoundOverlap;
    type Dop = DisambiguatedOverlapPosition;

    let disambiguated_start_bound = start_ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set);
    let disambiguated_end_bound = end_ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set);

    match (disambiguated_start_bound, disambiguated_end_bound) {
        (Dbo::Before, Dbo::Before) => Dop::CrossesEnd,
        (Dbo::Before, Dbo::Equal) => Dop::InsideAndSameEnd,
        (Dbo::Before, Dbo::After) => Dop::Inside,
        (Dbo::Equal, Dbo::Before) => Dop::ContainsAndSameStart,
        (Dbo::Equal, Dbo::Equal) => Dop::Equal,
        (Dbo::Equal, Dbo::After) => Dop::InsideAndSameStart,
        (Dbo::After, Dbo::Before) => Dop::Contains,
        (Dbo::After, Dbo::Equal) => Dop::ContainsAndSameEnd,
        (Dbo::After, Dbo::After) => Dop::CrossesStart,
    }
}

/// Overlap rules used as the reference for predefined decisions
pub const DEFAULT_OVERLAP_RULES: [OverlapRule; 1] = [OverlapRule::AllowAdjacency];

/// Rules for determining what counts as overlap
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum OverlapRule {
    /// Counts adjacent intervals as overlapping
    AllowAdjacency,
    /// Counts interval as overlapping if it is adjacent in the past
    ///
    /// Compared to the reference interval, the compared interval needs to be in the past and adjacent
    /// to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// needs to be [`EndsOnStart`](DisambiguatedOverlapPosition::EndsOnStart).
    AllowPastAdjacency,
    /// Counts interval as overlapping if it is adjacent in the future
    ///
    /// Compared to the reference interval, the compared interval needs to be in the future and adjacent
    /// to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// needs to be [`StartsOnEnd`](DisambiguatedOverlapPosition::StartsOnEnd).
    AllowFutureAdjacency,
    /// Doesn't count adjacent intervals as overlapping
    DenyAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent in the past
    ///
    /// Compared to the reference interval, the compared interval must not be in the past and adjacent
    /// to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// [`EndsOnStart`](DisambiguatedOverlapPosition::EndsOnStart) will deny overlap.
    DenyPastAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent in the future
    ///
    /// Compared to the reference interval, the compared interval must not be in the future and adjacent
    /// to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// [`StartsOnEnd`](DisambiguatedOverlapPosition::StartsOnEnd) will deny overlap.
    DenyFutureAdjacency,
}

impl OverlapRule {
    /// Returns the next state of the running overlap decision
    ///
    /// This method takes the running overlap decision and the [`DisambiguatedOverlapPosition`]
    /// and returns the next state of the running overlap decision.
    #[must_use]
    pub fn counts_as_overlap(&self, running: bool, disambiguated_pos: DisambiguatedOverlapPosition) -> bool {
        match self {
            Self::AllowAdjacency => allow_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::AllowPastAdjacency => allow_past_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::AllowFutureAdjacency => {
                allow_future_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos)
            },
            Self::DenyAdjacency => deny_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::DenyPastAdjacency => deny_past_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::DenyFutureAdjacency => {
                deny_future_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos)
            },
        }
    }
}

/// Checks all given rules and returns the final boolean regarding overlap
///
/// Iterates over the given rules and [fold](Iterator::fold) them with [`OverlapRule::counts_as_overlap`]
/// in order to get the final boolean regarding whether the intervals should be considered overlapping.
///
/// This method also contains the common logic of considering the following [`DisambiguatedOverlapPosition`]s
/// as being an overlap:
///
/// - [`CrossesStart`](DisambiguatedOverlapPosition::CrossesStart)
/// - [`CrossesEnd`](DisambiguatedOverlapPosition::CrossesEnd)
/// - [`Inside`](DisambiguatedOverlapPosition::Inside)
/// - [`InsideAndSameStart`](DisambiguatedOverlapPosition::InsideAndSameStart)
/// - [`InsideAndSameEnd`](DisambiguatedOverlapPosition::InsideAndSameEnd)
/// - [`Equal`](DisambiguatedOverlapPosition::Equal)
/// - [`ContainsAndSameStart`](DisambiguatedOverlapPosition::ContainsAndSameStart)
/// - [`ContainsAndSameEnd`](DisambiguatedOverlapPosition::ContainsAndSameEnd)
/// - [`Contains`](DisambiguatedOverlapPosition::Contains)
///
/// If conflicting rules are provided, for example [`AllowPastAdjacency`](OverlapRule::AllowPastAdjacency)
/// and [`DenyPastAdjacency`](OverlapRule::DenyPastAdjacency), the one appearing last is the one taking priority.
///
/// Don't use this method directly, use [`CanPositionOverlap::overlaps`] instead.
///
/// # Examples
///
/// ```
/// # use periodical::intervals::ops::overlap::{check_overlap_rules, DisambiguatedOverlapPosition, OverlapRule};
/// let disambiguated_pos = DisambiguatedOverlapPosition::EndsOnStart;
///
/// let deny_adjacency_diagnostic = check_overlap_rules(
///     disambiguated_pos,
///     &[OverlapRule::DenyAdjacency],
/// );
///
/// let allow_adjacency_diagnostic = check_overlap_rules(
///     disambiguated_pos,
///     &[OverlapRule::AllowAdjacency],
/// );
///
/// assert!(!deny_adjacency_diagnostic);
/// assert!(allow_adjacency_diagnostic);
/// ```
#[must_use]
pub fn check_overlap_rules<'a, RI>(disambiguated_overlap_position: DisambiguatedOverlapPosition, rules: RI) -> bool
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    let common = matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::CrossesStart
            | DisambiguatedOverlapPosition::CrossesEnd
            | DisambiguatedOverlapPosition::Inside
            | DisambiguatedOverlapPosition::InsideAndSameStart
            | DisambiguatedOverlapPosition::InsideAndSameEnd
            | DisambiguatedOverlapPosition::Equal
            | DisambiguatedOverlapPosition::ContainsAndSameStart
            | DisambiguatedOverlapPosition::ContainsAndSameEnd
            | DisambiguatedOverlapPosition::Contains,
    );

    rules.into_iter().fold(common, |is_overlapping, rule| {
        rule.counts_as_overlap(is_overlapping, disambiguated_overlap_position)
    })
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects
/// the ['allow adjacency' rule](OverlapRule::AllowAdjacency)
#[must_use]
pub fn allow_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running
        || matches!(
            disambiguated_pos,
            DisambiguatedOverlapPosition::EndsOnStart | DisambiguatedOverlapPosition::StartsOnEnd
        )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects
/// the ['allow past adjacency' rule](OverlapRule::AllowPastAdjacency)
#[must_use]
pub fn allow_past_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedOverlapPosition::EndsOnStart)
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects
/// the ['allow future adjacency' rule](OverlapRule::AllowFutureAdjacency)
#[must_use]
pub fn allow_future_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedOverlapPosition::StartsOnEnd)
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects
/// the ['deny adjacency' rule](OverlapRule::DenyAdjacency)
#[must_use]
pub fn deny_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running
        && !matches!(
            disambiguated_pos,
            DisambiguatedOverlapPosition::EndsOnStart | DisambiguatedOverlapPosition::StartsOnEnd,
        )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects
/// the ['deny past adjacency' rule](OverlapRule::DenyPastAdjacency)
#[must_use]
pub fn deny_past_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedOverlapPosition::EndsOnStart)
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects
/// the ['deny future adjacency' rule](OverlapRule::DenyFutureAdjacency)
#[must_use]
pub fn deny_future_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedOverlapPosition::StartsOnEnd)
}

/// Capacity to position an overlap with another interval
///
/// # Examples
///
/// ## Fetching the disambiguated overlap position
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
/// let compared_interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// let reference_interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
///         BoundInclusivity::Exclusive,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// assert_eq!(
///     compared_interval.disambiguated_overlap_position(&reference_interval, OverlapRuleSet::Lenient),
///     Ok(DisambiguatedOverlapPosition::EndsOnStart),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
///
/// ## Checking if an interval is overlapping
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::overlap::{CanPositionOverlap, OverlapRule, OverlapRuleSet};
/// let compared_interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// let reference_interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
///         BoundInclusivity::Exclusive,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// assert!(compared_interval.overlaps(
///         &reference_interval,
///         OverlapRuleSet::Lenient,
///         &[OverlapRule::AllowAdjacency],
/// ));
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait CanPositionOverlap<Rhs = Self> {
    /// Error type if the overlap positioning failed
    type Error;

    /// Returns the [`OverlapPosition`] of the given interval
    ///
    /// Evaluates the [`OverlapPosition`] of the compared, `self`, against the reference, `rhs`.
    /// It ignores the [inclusivities](crate::intervals::meta::BoundInclusivity) of the intervals
    /// and simply takes into account the position of the bounds.
    ///
    /// If two bounds are adjacent, a [`BoundOverlapAmbiguity`] is created
    /// and then stored in the right variant of [`OverlapPosition`].
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error>;

    /// Returns the [`DisambiguatedOverlapPosition`] of the given interval using a given rule set
    ///
    /// Uses [`OverlapRuleSet::disambiguate`] under the hood.
    ///
    /// See [`CanPositionOverlap::overlap_position`] for more details about overlap position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    fn disambiguated_overlap_position(
        &self,
        rhs: &Rhs,
        rule_set: OverlapRuleSet,
    ) -> Result<DisambiguatedOverlapPosition, Self::Error> {
        self.overlap_position(rhs)
            .map(|overlap_position| rule_set.disambiguate(overlap_position))
    }

    /// Returns whether the given interval overlaps the current one using predetermined rules
    ///
    /// Uses the [default rule set](OverlapRuleSet::default) with the [default rules](DEFAULT_OVERLAP_RULES).
    ///
    /// Those have been chosen because they are the closest to how we mathematically and humanly interpret overlaps.
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see [`CanPositionOverlap::overlaps`].
    ///
    /// If you want more granular control, see [`CanPositionOverlap::overlaps_using_disambiguated`].
    #[must_use]
    fn simple_overlaps(&self, rhs: &Rhs) -> bool {
        self.overlaps(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns whether the given other interval overlaps the current one
    /// using the given [overlap rules](`OverlapRule`)
    ///
    /// Uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position) under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method returns `false`.
    /// If it returns [`Ok`], then the given [`OverlapRule`]s are checked.
    ///
    /// This method returns `true` if all provided [`OverlapRule`]s are respected.
    /// This part of the process uses [`OverlapRule::counts_as_overlap`].
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for overlap,
    /// see [`simple_overlaps`](CanPositionOverlap::simple_overlaps).
    ///
    /// If you are looking for more control over what counts as overlap,
    /// see [`overlaps_using_disambiguated`](CanPositionOverlap::overlaps_using_disambiguated).
    ///
    /// If you want even more granular control over what counts as overlap,
    /// see [`overlaps_using`](CanPositionOverlap::overlaps_using).
    #[must_use]
    fn overlaps<'a, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a OverlapRule>,
    {
        self.disambiguated_overlap_position(rhs, rule_set)
            .map(|disambiguated_overlap_position| check_overlap_rules(disambiguated_overlap_position, rules))
            .unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using the given closure
    ///
    /// Uses [`overlap_position`](`CanPositionOverlap::overlap_position`) under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method returns `false`.
    /// If it returns [`Ok`], then the provided closure is in charge of determining whether the [`OverlapPosition`]
    /// given by [`overlap_position`](`CanPositionOverlap::overlap_position`) counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as an overlap but still want
    /// predetermined [`DisambiguatedOverlapPosition`]s, see [`CanPositionOverlap::overlaps_using_disambiguated`].
    ///
    /// If you are looking for predetermined decisions on what's considered as an overlap,
    /// see [`CanPositionOverlap::simple_overlaps`].
    #[must_use]
    fn overlaps_using<F>(&self, rhs: &Rhs, f: F) -> bool
    where
        F: FnOnce(OverlapPosition) -> bool,
    {
        self.overlap_position(rhs).map(f).unwrap_or(false)
    }

    /// Returns whether the given interval overlaps the current interval using the given closure
    /// with a disambiguated position
    ///
    /// Uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position) under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    /// If it returns [`Ok`], then the provided closure is in charge of determining whether
    /// the [`DisambiguatedOverlapPosition`]
    /// given by [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position)
    /// counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as an overlap,
    /// see [`CanPositionOverlap::overlaps_using`].
    ///
    /// If you are looking for predetermined decisions on what's considered as an overlap,
    /// see [`CanPositionOverlap::simple_overlaps`].
    #[must_use]
    fn overlaps_using_disambiguated<F>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedOverlapPosition) -> bool,
    {
        self.disambiguated_overlap_position(rhs, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

// Note: the impls below could be shorten by a lot when non-overlapping trait bounds (and overlapping ones?)
// become stable

impl<Rhs> CanPositionOverlap<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl CanPositionOverlap<AbsoluteBounds> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &AbsoluteBounds) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<EmptiableAbsoluteBounds> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &EmptiableAbsoluteBounds) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<AbsoluteInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &AbsoluteInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<BoundedAbsoluteInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &BoundedAbsoluteInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &HalfBoundedAbsoluteInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<UnboundedInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, _rhs: &UnboundedInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(OverlapPosition::Equal(None, None))
    }
}

impl CanPositionOverlap<EmptyInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, _rhs: &EmptyInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(OverlapPosition::Outside)
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Error = Infallible;

    fn overlap_position(&self, _rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(OverlapPosition::Outside)
    }
}

/// Positions the overlap between two [`AbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_abs_bounds(og: &AbsoluteBounds, other: &AbsoluteBounds) -> OverlapPosition {
    type Sb = AbsoluteStartBound;
    type Eb = AbsoluteEndBound;
    type Op = OverlapPosition;

    match ((og.start(), og.end()), (other.start(), other.end())) {
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::Equal(None, None),
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(..))) => Op::ContainsAndSameStart(None),
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::Finite(..), Eb::InfiniteFuture)) => Op::ContainsAndSameEnd(None),
        ((Sb::InfinitePast, Eb::InfiniteFuture), _) => Op::Contains,
        ((Sb::InfinitePast, Eb::Finite(..)), (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::InsideAndSameStart(None),
        ((Sb::Finite(..), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::InsideAndSameEnd(None),
        (_, (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::Inside,
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_end.time().cmp(&other_end.time()) {
                Ordering::Less => Op::InsideAndSameStart(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothEnds(
                        og_end.inclusivity(),
                        other_end.inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::ContainsAndSameStart(None),
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_start.time().cmp(&other_start.time()) {
                Ordering::Less => Op::ContainsAndSameEnd(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothStarts(
                        og_start.inclusivity(),
                        other_start.inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::InsideAndSameEnd(None),
            }
        },
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_end.time().cmp(&other_start.time()) {
                Ordering::Less => Op::OutsideBefore,
                Ordering::Equal => Op::EndsOnStart(BoundOverlapAmbiguity::EndStart(
                    og_end.inclusivity(),
                    other_start.inclusivity(),
                )),
                Ordering::Greater => Op::CrossesStart,
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_start.time().cmp(&other_end.time()) {
                Ordering::Less => Op::CrossesStart,
                Ordering::Equal => Op::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
                    og_start.inclusivity(),
                    other_end.inclusivity(),
                )),
                Ordering::Greater => Op::OutsideAfter,
            }
        },
        ((Sb::InfinitePast, Eb::Finite(ref_bound)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_abs_half_bounded_past_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref_bound), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_abs_half_bounded_future_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(ref_bound))) => {
            overlap_position_abs_bounded_half_bounded_past(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(ref_bound), Eb::InfiniteFuture)) => {
            overlap_position_abs_bounded_half_bounded_future(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_abs_bounded_pair(og_start, og_end, other_start, other_end)
        },
    }
}

/// Positions the overlap of a half-bounded interval going to the past against a bounded interval
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_abs_half_bounded_past_bounded(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            ref_bound.inclusivity(),
            other_start.inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::ContainsAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            ref_bound.inclusivity(),
            other_end.inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap of a half-bounded interval going to the future against a bounded interval
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_abs_half_bounded_future_bounded(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => OverlapPosition::ContainsAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            ref_bound.inclusivity(),
            other_start.inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            ref_bound.inclusivity(),
            other_end.inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval going to the past
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_abs_bounded_half_bounded_past(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.inclusivity(),
            ref_bound.inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::InsideAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            og_end.inclusivity(),
            ref_bound.inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval going to the future
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_abs_bounded_half_bounded_future(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => OverlapPosition::InsideAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            og_start.inclusivity(),
            ref_bound.inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.inclusivity(),
            ref_bound.inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two bounded intervals
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_abs_bounded_pair(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    let og_start_cmp = (
        og_start.time().cmp(&other_start.time()),
        og_start.time().cmp(&other_end.time()),
    );
    let og_end_cmp = (
        og_end.time().cmp(&other_start.time()),
        og_end.time().cmp(&other_end.time()),
    );

    match (og_start_cmp, og_end_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.inclusivity(),
            other_start.inclusivity(),
        )),
        ((_, Ordering::Equal), _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.inclusivity(),
            other_end.inclusivity(),
        )),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity()),
        )),
        ((Ordering::Greater, _), (_, Ordering::Equal)) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity()),
        )),
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(
                og_start.inclusivity(),
                other_start.inclusivity(),
            )),
            Some(BoundOverlapAmbiguity::BothEnds(
                og_end.inclusivity(),
                other_end.inclusivity(),
            )),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Equal)) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between two implementors of [`HasEmptiableAbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_emptiable_abs_bounds<T, U>(og: &T, other: &U) -> OverlapPosition
where
    T: HasEmptiableAbsoluteBounds,
    U: HasEmptiableAbsoluteBounds,
{
    match (og.emptiable_abs_bounds(), other.emptiable_abs_bounds()) {
        (_, EmptiableAbsoluteBounds::Empty) | (EmptiableAbsoluteBounds::Empty, _) => OverlapPosition::Outside,
        (EmptiableAbsoluteBounds::Bound(ref og_bounds), EmptiableAbsoluteBounds::Bound(ref other_bounds)) => {
            overlap_position_abs_bounds(og_bounds, other_bounds)
        },
    }
}

/// Positions the overlap between two [`RelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_rel_bounds(og: &RelativeBounds, other: &RelativeBounds) -> OverlapPosition {
    type Sb = RelativeStartBound;
    type Eb = RelativeEndBound;
    type Op = OverlapPosition;

    match ((og.start(), og.end()), (other.start(), other.end())) {
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::Equal(None, None),
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(..))) => Op::ContainsAndSameStart(None),
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::Finite(..), Eb::InfiniteFuture)) => Op::ContainsAndSameEnd(None),
        ((Sb::InfinitePast, Eb::InfiniteFuture), _) => Op::Contains,
        ((Sb::InfinitePast, Eb::Finite(..)), (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::InsideAndSameStart(None),
        ((Sb::Finite(..), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::InsideAndSameEnd(None),
        (_, (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::Inside,
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_end.offset().cmp(&other_end.offset()) {
                Ordering::Less => Op::InsideAndSameStart(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothEnds(
                        og_end.inclusivity(),
                        other_end.inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::ContainsAndSameStart(None),
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_start.offset().cmp(&other_start.offset()) {
                Ordering::Less => Op::ContainsAndSameEnd(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothStarts(
                        og_start.inclusivity(),
                        other_start.inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::InsideAndSameEnd(None),
            }
        },
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_end.offset().cmp(&other_start.offset()) {
                Ordering::Less => Op::OutsideBefore,
                Ordering::Equal => Op::EndsOnStart(BoundOverlapAmbiguity::EndStart(
                    og_end.inclusivity(),
                    other_start.inclusivity(),
                )),
                Ordering::Greater => Op::CrossesStart,
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_start.offset().cmp(&other_end.offset()) {
                Ordering::Less => Op::CrossesStart,
                Ordering::Equal => Op::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
                    og_start.inclusivity(),
                    other_end.inclusivity(),
                )),
                Ordering::Greater => Op::OutsideAfter,
            }
        },
        ((Sb::InfinitePast, Eb::Finite(ref_bound)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_rel_half_bounded_past_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref_bound), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_rel_half_bounded_future_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(ref_bound))) => {
            overlap_position_rel_bounded_half_bounded_past(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(ref_bound), Eb::InfiniteFuture)) => {
            overlap_position_rel_bounded_half_bounded_future(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_rel_bounded_pair(og_start, og_end, other_start, other_end)
        },
    }
}

/// Positions the overlap of a half-bounded interval going to the past against a bounded interval
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_rel_half_bounded_past_bounded(
    ref_bound: &RelativeFiniteBound,
    other_start: &RelativeFiniteBound,
    other_end: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&other_start.offset()),
        ref_bound.offset().cmp(&other_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            ref_bound.inclusivity(),
            other_start.inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::ContainsAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            ref_bound.inclusivity(),
            other_end.inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap of a half-bounded interval going to the future against a bounded interval
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_rel_half_bounded_future_bounded(
    ref_bound: &RelativeFiniteBound,
    other_start: &RelativeFiniteBound,
    other_end: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&other_start.offset()),
        ref_bound.offset().cmp(&other_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => OverlapPosition::ContainsAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            ref_bound.inclusivity(),
            other_start.inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            ref_bound.inclusivity(),
            other_end.inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval going to the past
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_rel_bounded_half_bounded_past(
    og_start: &RelativeFiniteBound,
    og_end: &RelativeFiniteBound,
    ref_bound: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&og_start.offset()),
        ref_bound.offset().cmp(&og_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.inclusivity(),
            ref_bound.inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::InsideAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            og_end.inclusivity(),
            ref_bound.inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval going to the future
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_rel_bounded_half_bounded_future(
    og_start: &RelativeFiniteBound,
    og_end: &RelativeFiniteBound,
    ref_bound: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&og_start.offset()),
        ref_bound.offset().cmp(&og_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => OverlapPosition::InsideAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            og_start.inclusivity(),
            ref_bound.inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.inclusivity(),
            ref_bound.inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two bounded intervals
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_rel_bounded_pair(
    og_start: &RelativeFiniteBound,
    og_end: &RelativeFiniteBound,
    other_start: &RelativeFiniteBound,
    other_end: &RelativeFiniteBound,
) -> OverlapPosition {
    let og_start_cmp = (
        og_start.offset().cmp(&other_start.offset()),
        og_start.offset().cmp(&other_end.offset()),
    );
    let og_end_cmp = (
        og_end.offset().cmp(&other_start.offset()),
        og_end.offset().cmp(&other_end.offset()),
    );

    match (og_start_cmp, og_end_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.inclusivity(),
            other_start.inclusivity(),
        )),
        ((_, Ordering::Equal), _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.inclusivity(),
            other_end.inclusivity(),
        )),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity()),
        )),
        ((Ordering::Greater, _), (_, Ordering::Equal)) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity()),
        )),
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(
                og_start.inclusivity(),
                other_start.inclusivity(),
            )),
            Some(BoundOverlapAmbiguity::BothEnds(
                og_end.inclusivity(),
                other_end.inclusivity(),
            )),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Equal)) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between two implementors of [`HasEmptiableRelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::overlap) for more info.
#[must_use]
pub fn overlap_position_emptiable_rel_bounds<T, U>(og: &T, other: &U) -> OverlapPosition
where
    T: HasEmptiableRelativeBounds,
    U: HasEmptiableRelativeBounds,
{
    match (og.emptiable_rel_bounds(), other.emptiable_rel_bounds()) {
        (_, EmptiableRelativeBounds::Empty) | (EmptiableRelativeBounds::Empty, _) => OverlapPosition::Outside,
        (EmptiableRelativeBounds::Bound(ref og_bounds), EmptiableRelativeBounds::Bound(ref other_bounds)) => {
            overlap_position_rel_bounds(og_bounds, other_bounds)
        },
    }
}

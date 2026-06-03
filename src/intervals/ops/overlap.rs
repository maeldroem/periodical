//! Interval overlap positioning
//!
//! Given two intervals, positions the overlap, represented by
//! [`OverlapPosition`].
//!
//! Like [`BoundOverlapAmbiguity`], since two intervals can be adjacent and
//! "meet" at a given point, it creates an ambiguity due to the
//! [`BoundInclusivity`](crate::intervals::meta::BoundInclusivity)
//! of the intervals.
//!
//! Using [`CanPositionOverlap`] will return an [`OverlapPosition`], which will
//! then need to be disambiguated in order to obtain a concrete diagnostic of
//! the overlap.
//!
//! You can disambiguate an [`OverlapPosition`] using an [`OverlapRuleSet`] or a
//! custom closure by using [`OverlapPosition::disambiguate_using`].
//!
//! A disambiguated [`OverlapPosition`] is represented by
//! [`DisambiguatedOverlapPosition`].
//!
//! Once disambiguated, the overlap position can be converted into a boolean
//! decision of whether the two intervals overlap according to your definition,
//! using [`OverlapRule`]s with [`CanPositionOverlap::overlaps`].
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::ops::overlap::CanPositionOverlap;
//! let first_interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let second_interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 12:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! assert!(first_interval.simple_overlaps(&second_interval));
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use std::cmp::Ordering;
use std::convert::Infallible;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    HalfBoundedAbsInterval,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, Interval};
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
    DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteEndBound,
    RelFiniteStartBound,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Overlap position
///
/// Defines where the compared interval was found relative to the reference
/// interval.
///
/// When [`overlap_position`](CanPositionOverlap::overlap_position) evaluates
/// the overlap position, it ignores the
/// [inclusivities](crate::intervals::meta::BoundInclusivity) of the intervals
/// and simply takes into account the position of the bounds.
///
/// If two bounds are adjacent, a [`BoundOverlapAmbiguity`] is created
/// and then stored in the right variant of [`OverlapPosition`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum OverlapPosition {
    /// Compared interval is before the reference interval
    OutsideBefore,
    /// Compared interval is after the reference interval
    OutsideAfter,
    /// Compared interval is outside the reference interval
    ///
    /// This result is only possible when dealing with empty intervals, as an
    /// empty interval does not have a position in time.
    Outside,
    /// Compared interval ends on the start of the reference interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the
    /// [`BoundOverlapAmbiguity`].
    EndsOnStart(BoundOverlapAmbiguity),
    /// Compared interval starts on the end of the reference interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the
    /// [`BoundOverlapAmbiguity`].
    StartsOnEnd(BoundOverlapAmbiguity),
    /// Compared interval crosses the start of the reference interval
    ///
    /// The compared interval ends within the reference interval,
    /// otherwise the overlap position would be
    /// [`Contains`](OverlapPosition::Contains).
    CrossesStart,
    /// Compared interval crosses the end of the reference interval
    ///
    /// The compared interval starts within the reference interval,
    /// otherwise the overlap position would be
    /// [`Contains`](OverlapPosition::Contains).
    CrossesEnd,
    /// Compared interval is inside the reference interval
    Inside,
    /// Compared interval is inside the reference interval and both have the
    /// same start
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the
    /// [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can
    /// result in such an overlap position with no finite bounds involved,
    /// hence the [`BoundOverlapAmbiguity`] being wrapped in an [`Option`].
    InsideAndSameStart(Option<BoundOverlapAmbiguity>),
    /// Compared interval is inside the reference interval and both have the
    /// same end
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the
    /// [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can
    /// result in such an overlap position with no finite bounds involved,
    /// hence the [`BoundOverlapAmbiguity`] being wrapped in an [`Option`].
    InsideAndSameEnd(Option<BoundOverlapAmbiguity>),
    /// Compared interval is equal to the reference interval
    ///
    /// Since two pairs of bounds are overlapping, this creates an ambiguity,
    /// hence the pair of [`BoundOverlapAmbiguity`].
    ///
    /// Since half-bounded intervals only have a single defined bound, the
    /// second ambiguity is wrapped in an [`Option`].
    /// Also, when you compare two unbounded intervals, neither have defined
    /// bounds, but still are equal, so both [`BoundOverlapAmbiguity`] are
    /// wrapped in [`Option`].
    ///
    /// # Invariants
    ///
    /// The second [`Option`] can never be [`Some`] if the first [`Option`] is
    /// [`None`].
    Equal(Option<BoundOverlapAmbiguity>, Option<BoundOverlapAmbiguity>),
    /// Compared interval contains the reference interval and both have the same
    /// start
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the
    /// [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can
    /// result in such an overlap position with no finite bounds involved,
    /// hence the [`BoundOverlapAmbiguity`] being wrapped in an [`Option`].
    ContainsAndSameStart(Option<BoundOverlapAmbiguity>),
    /// Compared interval contains the reference interval and both have the same
    /// end
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the
    /// [`BoundOverlapAmbiguity`].
    ///
    /// Since comparing an unbounded interval with a half-bounded interval can
    /// result in such an overlap position with no finite bounds involved,
    /// hence the [`BoundOverlapAmbiguity`] being wrapped in an [`Option`].
    ContainsAndSameEnd(Option<BoundOverlapAmbiguity>),
    /// Compared interval fully contains the reference interval
    Contains,
}

impl OverlapPosition {
    /// Strips information about bound ambiguities and conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and
    /// cannot be recovered after conversion.
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
    /// **Careful!** This method discards data about bound inclusivity and
    /// cannot be recovered after conversion.
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
/// Indicates where the overlap is situated compared to the reference interval
/// without any ambiguity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
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
    /// Two bounds possessing the same point in time need to be either inclusive
    /// or at least one of them needs to be exclusive (not both!) in order
    /// to be counted as equal.
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
    /// Two bounds possessing the same point in time are counted as equal,
    /// regardless of the inclusivity.
    VeryLenient,
    /// Continuous to future rule set
    ///
    /// Follows the same principles as [`OverlapRuleSet::Strict`], but adds an
    /// exception: if an exclusive end bound is adjacent to an inclusive
    /// start bound, it also counts as equal.
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
    /// Follows the same principles as [`OverlapRuleSet::Strict`], but adds an
    /// exception: if an exclusive start bound is adjacent to an inclusive
    /// end bound, it also counts as equal.
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
    /// **Careful!** This method discards data about bound inclusivity and
    /// cannot be recovered after conversion.
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

/// Disambiguates an [`OverlapPosition`] using the given
/// [`BoundOverlapDisambiguationRuleSet`]
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
        Op::EndsOnStart(ambiguity) => match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
            Dbo::Before => Dop::CrossesStart,
            Dbo::Equal => Dop::EndsOnStart,
            Dbo::After => Dop::OutsideBefore,
        },
        Op::StartsOnEnd(ambiguity) => match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
            Dbo::Before => Dop::OutsideAfter,
            Dbo::Equal => Dop::StartsOnEnd,
            Dbo::After => Dop::CrossesEnd,
        },
        Op::CrossesStart => Dop::CrossesStart,
        Op::CrossesEnd => Dop::CrossesEnd,
        Op::Inside => Dop::Inside,
        Op::InsideAndSameStart(None) => Dop::InsideAndSameStart,
        Op::InsideAndSameStart(Some(ambiguity)) => {
            match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
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
        Op::InsideAndSameEnd(Some(ambiguity)) => match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
            Dbo::Before => Dop::CrossesEnd,
            Dbo::Equal => Dop::InsideAndSameEnd,
            Dbo::After => Dop::Inside,
        },
        Op::ContainsAndSameStart(None) => Dop::ContainsAndSameStart,
        Op::ContainsAndSameStart(Some(ambiguity)) => {
            match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::CrossesEnd,
                Dbo::Equal => Dop::ContainsAndSameStart,
                Dbo::After => Dop::Contains,
            }
        },
        Op::ContainsAndSameEnd(None) => Dop::ContainsAndSameEnd,
        Op::ContainsAndSameEnd(Some(ambiguity)) => {
            match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::Contains,
                Dbo::Equal => Dop::ContainsAndSameEnd,
                Dbo::After => Dop::CrossesStart,
            }
        },
        Op::Contains => Dop::Contains,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`] for the
/// [`Equal`](OverlapPosition::Equal) position of two half-bounded intervals
#[must_use]
pub fn overlap_position_bound_ambiguity_disambiguation_equal_half_bounded(
    ambiguity: BoundOverlapAmbiguity,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Dbo = DisambiguatedBoundOverlap;
    type Dop = DisambiguatedOverlapPosition;

    match ambiguity {
        BoundOverlapAmbiguity::BothStarts(..) => match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
            Dbo::Before => Dop::InsideAndSameEnd,
            Dbo::Equal => Dop::Equal,
            Dbo::After => Dop::ContainsAndSameEnd,
        },
        BoundOverlapAmbiguity::BothEnds(..) => match ambiguity.disambiguate(bound_overlap_disambiguation_rule_set) {
            Dbo::Before => Dop::ContainsAndSameStart,
            Dbo::Equal => Dop::Equal,
            Dbo::After => Dop::InsideAndSameStart,
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

/// Disambiguates two [`BoundOverlapAmbiguity`] for the
/// [`Equal`](OverlapPosition::Equal) position of two bounded intervals
#[must_use]
pub fn overlap_position_bound_ambiguity_disambiguation_equal_bounded(
    start_ambiguity: BoundOverlapAmbiguity,
    end_ambiguity: BoundOverlapAmbiguity,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Dbo = DisambiguatedBoundOverlap;
    type Dop = DisambiguatedOverlapPosition;

    let disambiguated_start_bound = start_ambiguity.disambiguate(bound_overlap_disambiguation_rule_set);
    let disambiguated_end_bound = end_ambiguity.disambiguate(bound_overlap_disambiguation_rule_set);

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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum OverlapRule {
    /// Counts adjacent intervals as overlapping
    AllowAdjacency,
    /// Counts interval as overlapping if it is adjacent in the past
    ///
    /// Compared to the reference interval, the compared interval needs to be in
    /// the past and adjacent to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// needs to be [`EndsOnStart`](DisambiguatedOverlapPosition::EndsOnStart).
    AllowPastAdjacency,
    /// Counts interval as overlapping if it is adjacent in the future
    ///
    /// Compared to the reference interval, the compared interval needs to be in
    /// the future and adjacent to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// needs to be [`StartsOnEnd`](DisambiguatedOverlapPosition::StartsOnEnd).
    AllowFutureAdjacency,
    /// Doesn't count adjacent intervals as overlapping
    DenyAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent in the past
    ///
    /// Compared to the reference interval, the compared interval must not be in
    /// the past and adjacent to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// [`EndsOnStart`](DisambiguatedOverlapPosition::EndsOnStart) will deny
    /// overlap.
    DenyPastAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent in the future
    ///
    /// Compared to the reference interval, the compared interval must not be in
    /// the future and adjacent to the reference interval.
    /// In other words, the [`DisambiguatedOverlapPosition`]
    /// [`StartsOnEnd`](DisambiguatedOverlapPosition::StartsOnEnd) will deny
    /// overlap.
    DenyFutureAdjacency,
}

impl OverlapRule {
    /// Returns the next state of the running overlap decision
    ///
    /// This method takes the running overlap decision and the
    /// [`DisambiguatedOverlapPosition`] and returns the next state of the
    /// running overlap decision.
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
/// Iterates over the given rules and [fold](Iterator::fold) them with
/// [`OverlapRule::counts_as_overlap`] in order to get the final boolean
/// regarding whether the intervals should be considered overlapping.
///
/// This method also contains the common logic of considering the following
/// [`DisambiguatedOverlapPosition`]s as being an overlap:
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
/// If conflicting rules are provided, for example
/// [`AllowPastAdjacency`](OverlapRule::AllowPastAdjacency)
/// and [`DenyPastAdjacency`](OverlapRule::DenyPastAdjacency), the one appearing
/// last is the one taking priority.
///
/// Don't use this method directly, use [`CanPositionOverlap::overlaps`]
/// instead.
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
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
/// let compared_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let reference_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new_with_inclusivity(
///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         BoundInclusivity::Exclusive,
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     compared_interval.disambiguated_overlap_position(&reference_interval, OverlapRuleSet::Lenient),
///     Ok(DisambiguatedOverlapPosition::EndsOnStart),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Checking if an interval is overlapping
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::overlap::{CanPositionOverlap, OverlapRule, OverlapRuleSet};
/// let compared_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let reference_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new_with_inclusivity(
///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         BoundInclusivity::Exclusive,
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert!(compared_interval.overlaps(
///         &reference_interval,
///         OverlapRuleSet::Lenient,
///         &[OverlapRule::AllowAdjacency],
/// ));
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait CanPositionOverlap<Rhs = Self> {
    /// Error type if the overlap positioning failed
    type Error;

    /// Returns the [`OverlapPosition`] of the given interval
    ///
    /// Evaluates the [`OverlapPosition`] of the compared, `self`, against the
    /// reference, `rhs`. It ignores the
    /// [inclusivities](crate::intervals::meta::BoundInclusivity) of the
    /// intervals and simply takes into account the position of the bounds.
    ///
    /// If two bounds are adjacent, a [`BoundOverlapAmbiguity`] is created
    /// and then stored in the right variant of [`OverlapPosition`].
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// # use periodical::intervals::ops::overlap::{CanPositionOverlap, OverlapPosition, OverlapRuleSet};
    /// let compared_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let reference_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new_with_inclusivity(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     compared_interval.overlap_position(&reference_interval),
    ///     Ok(OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
    ///         BoundInclusivity::Inclusive,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error>;

    /// Returns the [`DisambiguatedOverlapPosition`] of the given interval using
    /// a given rule set
    ///
    /// Uses [`OverlapRuleSet::disambiguate`] under the hood.
    ///
    /// See [`CanPositionOverlap::overlap_position`] for more details about
    /// overlap position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
    /// let compared_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let reference_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new_with_inclusivity(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     compared_interval.disambiguated_overlap_position(&reference_interval, OverlapRuleSet::Lenient),
    ///     Ok(DisambiguatedOverlapPosition::EndsOnStart),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn disambiguated_overlap_position(
        &self,
        rhs: &Rhs,
        rule_set: OverlapRuleSet,
    ) -> Result<DisambiguatedOverlapPosition, Self::Error> {
        self.overlap_position(rhs)
            .map(|overlap_position| rule_set.disambiguate(overlap_position))
    }

    /// Returns whether the given interval overlaps the current one using
    /// predetermined rules
    ///
    /// Uses the [default rule set](OverlapRuleSet::default) with the [default rules](DEFAULT_OVERLAP_RULES).
    ///
    /// Those have been chosen because they are the closest to how we
    /// mathematically and humanly interpret overlaps.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::overlap:: CanPositionOverlap;
    /// let compared_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 11:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let reference_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert!(compared_interval.simple_overlaps(&reference_interval));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see
    /// [`CanPositionOverlap::overlaps`].
    ///
    /// If you want more granular control, see
    /// [`CanPositionOverlap::overlaps_using_disambiguated`].
    #[must_use]
    fn simple_overlaps(&self, rhs: &Rhs) -> bool {
        self.overlaps(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns whether the given other interval overlaps the current one
    /// using the given [overlap rules](`OverlapRule`)
    ///
    /// Uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position) under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method
    /// returns `false`. If it returns [`Ok`], then the given
    /// [`OverlapRule`]s are checked.
    ///
    /// This method returns `true` if all provided [`OverlapRule`]s are
    /// respected. This part of the process uses
    /// [`OverlapRule::counts_as_overlap`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::overlap::{CanPositionOverlap, OverlapRule, OverlapRuleSet};
    /// let compared_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let reference_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new_with_inclusivity(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert!(compared_interval.overlaps(
    ///         &reference_interval,
    ///         OverlapRuleSet::Lenient,
    ///         &[OverlapRule::AllowAdjacency],
    /// ));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
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
            .is_ok_and(|disambiguated_overlap_position| check_overlap_rules(disambiguated_overlap_position, rules))
    }

    /// Returns whether the given other interval overlaps the current interval
    /// using the given closure
    ///
    /// Uses [`overlap_position`](`CanPositionOverlap::overlap_position`) under
    /// the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method
    /// returns `false`. If it returns [`Ok`], then the provided closure is
    /// in charge of determining whether the [`OverlapPosition`]
    /// given by [`overlap_position`](`CanPositionOverlap::overlap_position`)
    /// counts as overlapping or not.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// # use periodical::intervals::ops::overlap::{CanPositionOverlap, OverlapPosition};
    /// let compared_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new_with_inclusivity(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let reference_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new_with_inclusivity(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let overlap_closure = |pos: OverlapPosition| -> bool {
    ///     matches!(
    ///         pos,
    ///         OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
    ///             BoundInclusivity::Exclusive,
    ///             BoundInclusivity::Exclusive,
    ///         )) | OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
    ///             BoundInclusivity::Exclusive,
    ///             BoundInclusivity::Exclusive,
    ///         )),
    ///     )
    /// };
    ///
    /// assert!(compared_interval.overlaps_using(&reference_interval, overlap_closure));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as an overlap but
    /// still want predetermined [`DisambiguatedOverlapPosition`]s, see
    /// [`CanPositionOverlap::overlaps_using_disambiguated`].
    ///
    /// If you are looking for predetermined decisions on what's considered as
    /// an overlap, see [`CanPositionOverlap::simple_overlaps`].
    #[must_use]
    fn overlaps_using<F>(&self, rhs: &Rhs, f: F) -> bool
    where
        F: FnOnce(OverlapPosition) -> bool,
    {
        self.overlap_position(rhs).is_ok_and(f)
    }

    /// Returns whether the given interval overlaps the current interval using
    /// the given closure with a disambiguated position
    ///
    /// Uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position) under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method
    /// returns false. If it returns [`Ok`], then the provided closure is in
    /// charge of determining whether the [`DisambiguatedOverlapPosition`]
    /// given by [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position)
    /// counts as overlapping or not.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// # use periodical::intervals::ops::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
    /// let compared_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new_with_inclusivity(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     ).to_end_bound(),
    /// );
    ///
    /// let reference_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new_with_inclusivity(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let overlap_closure = |pos: DisambiguatedOverlapPosition| -> bool {
    ///     matches!(
    ///         pos,
    ///         DisambiguatedOverlapPosition::EndsOnStart
    ///         | DisambiguatedOverlapPosition::StartsOnEnd
    ///     )
    /// };
    ///
    /// assert!(compared_interval.overlaps_using_disambiguated(
    ///     &reference_interval,
    ///     OverlapRuleSet::VeryLenient,
    ///     overlap_closure,
    /// ));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as
    /// an overlap, see [`CanPositionOverlap::overlaps_using`].
    ///
    /// If you are looking for predetermined decisions on what's considered as
    /// an overlap, see [`CanPositionOverlap::simple_overlaps`].
    #[must_use]
    fn overlaps_using_disambiguated<F>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedOverlapPosition) -> bool,
    {
        self.disambiguated_overlap_position(rhs, rule_set).is_ok_and(f)
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bound_pair(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bound_pair(self, rhs))
    }
}

impl CanPositionOverlap<AbsBoundPair> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &AbsBoundPair) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl CanPositionOverlap<EmptiableAbsBoundPair> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &EmptiableAbsBoundPair) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl CanPositionOverlap<AbsInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &AbsInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl CanPositionOverlap<BoundedAbsInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &BoundedAbsInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
    }
}

impl CanPositionOverlap<HalfBoundedAbsInterval> for UnboundedInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &HalfBoundedAbsInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bound_pair(self, rhs))
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

/// Positions the overlap between two [`AbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_abs_bound_pair(og: &AbsBoundPair, other: &AbsBoundPair) -> OverlapPosition {
    type Sb = AbsStartBound;
    type Eb = AbsEndBound;
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
            match og_end.pos().cmp(&other_end.pos()) {
                Ordering::Less => Op::InsideAndSameStart(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothEnds(
                        og_end.pos().inclusivity(),
                        other_end.pos().inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::ContainsAndSameStart(None),
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_start.pos().cmp(&other_start.pos()) {
                Ordering::Less => Op::ContainsAndSameEnd(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothStarts(
                        og_start.pos().inclusivity(),
                        other_start.pos().inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::InsideAndSameEnd(None),
            }
        },
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_end.pos().cmp(&other_start.pos()) {
                Ordering::Less => Op::OutsideBefore,
                Ordering::Equal => Op::EndsOnStart(BoundOverlapAmbiguity::EndStart(
                    og_end.pos().inclusivity(),
                    other_start.pos().inclusivity(),
                )),
                Ordering::Greater => Op::CrossesStart,
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_start.pos().cmp(&other_end.pos()) {
                Ordering::Less => Op::CrossesStart,
                Ordering::Equal => Op::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
                    og_start.pos().inclusivity(),
                    other_end.pos().inclusivity(),
                )),
                Ordering::Greater => Op::OutsideAfter,
            }
        },
        ((Sb::InfinitePast, Eb::Finite(ref ref_bound)), (Sb::Finite(ref other_start), Eb::Finite(ref other_end))) => {
            overlap_position_abs_half_bounded_past_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref ref_bound), Eb::InfiniteFuture), (Sb::Finite(ref other_start), Eb::Finite(ref other_end))) => {
            overlap_position_abs_half_bounded_future_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref og_start), Eb::Finite(ref og_end)), (Sb::InfinitePast, Eb::Finite(ref ref_bound))) => {
            overlap_position_abs_bounded_half_bounded_past(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(ref og_start), Eb::Finite(ref og_end)), (Sb::Finite(ref ref_bound), Eb::InfiniteFuture)) => {
            overlap_position_abs_bounded_half_bounded_future(og_start, og_end, ref_bound)
        },
        (
            (Sb::Finite(ref og_start), Eb::Finite(ref og_end)),
            (Sb::Finite(ref other_start), Eb::Finite(ref other_end)),
        ) => overlap_position_abs_bounded_pair(og_start, og_end, other_start, other_end),
    }
}

/// Positions the overlap of a half-bounded interval going to the past against a
/// bounded interval
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_abs_half_bounded_past_bounded(
    ref_bound: &AbsFiniteEndBound,
    other_start: &AbsFiniteStartBound,
    other_end: &AbsFiniteEndBound,
) -> OverlapPosition {
    match (
        ref_bound.pos().cmp(&other_start.pos()),
        ref_bound.pos().cmp(&other_end.pos()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            ref_bound.pos().inclusivity(),
            other_start.pos().inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::ContainsAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            ref_bound.pos().inclusivity(),
            other_end.pos().inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap of a half-bounded interval going to the future against
/// a bounded interval
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_abs_half_bounded_future_bounded(
    ref_bound: &AbsFiniteStartBound,
    other_start: &AbsFiniteStartBound,
    other_end: &AbsFiniteEndBound,
) -> OverlapPosition {
    match (
        ref_bound.pos().cmp(&other_start.pos()),
        ref_bound.pos().cmp(&other_end.pos()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => OverlapPosition::ContainsAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            ref_bound.pos().inclusivity(),
            other_start.pos().inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            ref_bound.pos().inclusivity(),
            other_end.pos().inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval
/// going to the past
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_abs_bounded_half_bounded_past(
    og_start: &AbsFiniteStartBound,
    og_end: &AbsFiniteEndBound,
    ref_bound: &AbsFiniteEndBound,
) -> OverlapPosition {
    match (ref_bound.pos().cmp(&og_start.pos()), ref_bound.pos().cmp(&og_end.pos())) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::InsideAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            og_end.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval
/// going to the future
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_abs_bounded_half_bounded_future(
    og_start: &AbsFiniteStartBound,
    og_end: &AbsFiniteEndBound,
    ref_bound: &AbsFiniteStartBound,
) -> OverlapPosition {
    match (ref_bound.pos().cmp(&og_start.pos()), ref_bound.pos().cmp(&og_end.pos())) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => OverlapPosition::InsideAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            og_start.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two bounded intervals
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_abs_bounded_pair(
    og_start: &AbsFiniteStartBound,
    og_end: &AbsFiniteEndBound,
    other_start: &AbsFiniteStartBound,
    other_end: &AbsFiniteEndBound,
) -> OverlapPosition {
    let og_start_cmp = (
        og_start.pos().cmp(&other_start.pos()),
        og_start.pos().cmp(&other_end.pos()),
    );
    let og_end_cmp = (og_end.pos().cmp(&other_start.pos()), og_end.pos().cmp(&other_end.pos()));

    match (og_start_cmp, og_end_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.pos().inclusivity(),
            other_start.pos().inclusivity(),
        )),
        ((_, Ordering::Equal), _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.pos().inclusivity(),
            other_end.pos().inclusivity(),
        )),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.pos().inclusivity(), other_start.pos().inclusivity()),
        )),
        ((Ordering::Greater, _), (_, Ordering::Equal)) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.pos().inclusivity(), other_end.pos().inclusivity()),
        )),
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(
                og_start.pos().inclusivity(),
                other_start.pos().inclusivity(),
            )),
            Some(BoundOverlapAmbiguity::BothEnds(
                og_end.pos().inclusivity(),
                other_end.pos().inclusivity(),
            )),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.pos().inclusivity(), other_start.pos().inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Equal)) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.pos().inclusivity(), other_end.pos().inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between two implementors of
/// [`HasEmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_emptiable_abs_bound_pair<T, U>(og: &T, other: &U) -> OverlapPosition
where
    T: HasEmptiableAbsBoundPair,
    U: HasEmptiableAbsBoundPair,
{
    match (og.emptiable_abs_bound_pair(), other.emptiable_abs_bound_pair()) {
        (_, EmptiableAbsBoundPair::Empty) | (EmptiableAbsBoundPair::Empty, _) => OverlapPosition::Outside,
        (EmptiableAbsBoundPair::Bound(ref og_bounds), EmptiableAbsBoundPair::Bound(ref other_bounds)) => {
            overlap_position_abs_bound_pair(og_bounds, other_bounds)
        },
    }
}

/// Positions the overlap between two [`RelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_rel_bound_pair(og: &RelBoundPair, other: &RelBoundPair) -> OverlapPosition {
    type Sb = RelStartBound;
    type Eb = RelEndBound;
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
            match og_end.pos().cmp(&other_end.pos()) {
                Ordering::Less => Op::InsideAndSameStart(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothEnds(
                        og_end.pos().inclusivity(),
                        other_end.pos().inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::ContainsAndSameStart(None),
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_start.pos().cmp(&other_start.pos()) {
                Ordering::Less => Op::ContainsAndSameEnd(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothStarts(
                        og_start.pos().inclusivity(),
                        other_start.pos().inclusivity(),
                    )),
                    None,
                ),
                Ordering::Greater => Op::InsideAndSameEnd(None),
            }
        },
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_end.pos().cmp(&other_start.pos()) {
                Ordering::Less => Op::OutsideBefore,
                Ordering::Equal => Op::EndsOnStart(BoundOverlapAmbiguity::EndStart(
                    og_end.pos().inclusivity(),
                    other_start.pos().inclusivity(),
                )),
                Ordering::Greater => Op::CrossesStart,
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_start.pos().cmp(&other_end.pos()) {
                Ordering::Less => Op::CrossesStart,
                Ordering::Equal => Op::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
                    og_start.pos().inclusivity(),
                    other_end.pos().inclusivity(),
                )),
                Ordering::Greater => Op::OutsideAfter,
            }
        },
        ((Sb::InfinitePast, Eb::Finite(ref ref_bound)), (Sb::Finite(ref other_start), Eb::Finite(ref other_end))) => {
            overlap_position_rel_half_bounded_past_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref ref_bound), Eb::InfiniteFuture), (Sb::Finite(ref other_start), Eb::Finite(ref other_end))) => {
            overlap_position_rel_half_bounded_future_bounded(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref og_start), Eb::Finite(ref og_end)), (Sb::InfinitePast, Eb::Finite(ref ref_bound))) => {
            overlap_position_rel_bounded_half_bounded_past(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(ref og_start), Eb::Finite(ref og_end)), (Sb::Finite(ref ref_bound), Eb::InfiniteFuture)) => {
            overlap_position_rel_bounded_half_bounded_future(og_start, og_end, ref_bound)
        },
        (
            (Sb::Finite(ref og_start), Eb::Finite(ref og_end)),
            (Sb::Finite(ref other_start), Eb::Finite(ref other_end)),
        ) => overlap_position_rel_bounded_pair(og_start, og_end, other_start, other_end),
    }
}

/// Positions the overlap of a half-bounded interval going to the past against a
/// bounded interval
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_rel_half_bounded_past_bounded(
    ref_bound: &RelFiniteEndBound,
    other_start: &RelFiniteStartBound,
    other_end: &RelFiniteEndBound,
) -> OverlapPosition {
    match (
        ref_bound.pos().cmp(&other_start.pos()),
        ref_bound.pos().cmp(&other_end.pos()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            ref_bound.pos().inclusivity(),
            other_start.pos().inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::ContainsAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            ref_bound.pos().inclusivity(),
            other_end.pos().inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap of a half-bounded interval going to the future against
/// a bounded interval
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_rel_half_bounded_future_bounded(
    ref_bound: &RelFiniteStartBound,
    other_start: &RelFiniteStartBound,
    other_end: &RelFiniteEndBound,
) -> OverlapPosition {
    match (
        ref_bound.pos().cmp(&other_start.pos()),
        ref_bound.pos().cmp(&other_end.pos()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => OverlapPosition::ContainsAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            ref_bound.pos().inclusivity(),
            other_start.pos().inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            ref_bound.pos().inclusivity(),
            other_end.pos().inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval
/// going to the past
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_rel_bounded_half_bounded_past(
    og_start: &RelFiniteStartBound,
    og_end: &RelFiniteEndBound,
    ref_bound: &RelFiniteEndBound,
) -> OverlapPosition {
    match (ref_bound.pos().cmp(&og_start.pos()), ref_bound.pos().cmp(&og_end.pos())) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::InsideAndSameEnd(Some(BoundOverlapAmbiguity::BothEnds(
            og_end.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        ))),
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap of a bounded interval against a half-bounded interval
/// going to the future
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_rel_bounded_half_bounded_future(
    og_start: &RelFiniteStartBound,
    og_end: &RelFiniteEndBound,
    ref_bound: &RelFiniteStartBound,
) -> OverlapPosition {
    match (ref_bound.pos().cmp(&og_start.pos()), ref_bound.pos().cmp(&og_end.pos())) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => OverlapPosition::InsideAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
            og_start.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        ))),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.pos().inclusivity(),
            ref_bound.pos().inclusivity(),
        )),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two bounded intervals
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_rel_bounded_pair(
    og_start: &RelFiniteStartBound,
    og_end: &RelFiniteEndBound,
    other_start: &RelFiniteStartBound,
    other_end: &RelFiniteEndBound,
) -> OverlapPosition {
    let og_start_cmp = (
        og_start.pos().cmp(&other_start.pos()),
        og_start.pos().cmp(&other_end.pos()),
    );
    let og_end_cmp = (og_end.pos().cmp(&other_start.pos()), og_end.pos().cmp(&other_end.pos()));

    match (og_start_cmp, og_end_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::EndStart(
            og_end.pos().inclusivity(),
            other_start.pos().inclusivity(),
        )),
        ((_, Ordering::Equal), _) => OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::StartEnd(
            og_start.pos().inclusivity(),
            other_end.pos().inclusivity(),
        )),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.pos().inclusivity(), other_start.pos().inclusivity()),
        )),
        ((Ordering::Greater, _), (_, Ordering::Equal)) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.pos().inclusivity(), other_end.pos().inclusivity()),
        )),
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(
                og_start.pos().inclusivity(),
                other_start.pos().inclusivity(),
            )),
            Some(BoundOverlapAmbiguity::BothEnds(
                og_end.pos().inclusivity(),
                other_end.pos().inclusivity(),
            )),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.pos().inclusivity(), other_start.pos().inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Equal)) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.pos().inclusivity(), other_end.pos().inclusivity()),
        )),
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between two implementors of
/// [`HasEmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn overlap_position_emptiable_rel_bound_pair<T, U>(og: &T, other: &U) -> OverlapPosition
where
    T: HasEmptiableRelBoundPair,
    U: HasEmptiableRelBoundPair,
{
    match (og.emptiable_rel_bound_pair(), other.emptiable_rel_bound_pair()) {
        (_, EmptiableRelBoundPair::Empty) | (EmptiableRelBoundPair::Empty, _) => OverlapPosition::Outside,
        (EmptiableRelBoundPair::Bound(ref og_bounds), EmptiableRelBoundPair::Bound(ref other_bounds)) => {
            overlap_position_rel_bound_pair(og_bounds, other_bounds)
        },
    }
}

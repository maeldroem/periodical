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

use std::cmp::Ordering;
use std::convert::Infallible;

use chrono::{DateTime, Duration, DurationRound, RoundingError, Utc};

use crate::intervals::interval::{
    AbsoluteFiniteBound, EmptiableAbsoluteBounds, HasEmptiableAbsoluteBounds, swap_absolute_bounds,
};
use crate::intervals::meta::HasBoundInclusivity;
use crate::ops::{DifferenceResult, IntersectionResult, SymmetricDifferenceResult, UnionResult};

use super::interval::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptyInterval, HasAbsoluteBounds,
};
use super::meta::BoundInclusivity;

/// Time precision used for comparisons
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Precision {
    /// Rounds the compared times to the given duration (e.g. if the duration is 1 second, the times will be rounded to the nearest second)
    ToNearest(Duration),
    /// Floors the compared times to the given duration (e.g. if the duration is 5 minutes, the times will be floored to the 5-minutes part they are in)
    ToPast(Duration),
    /// Ceils the compared times to the given duration
    ToFuture(Duration),
}

impl Precision {
    /// Uses the given precision to precise the given time
    ///
    /// # Errors
    ///
    /// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
    /// if the given duration used is too big, negative or zero, etc.
    ///
    /// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
    pub fn precise_time(&self, time: DateTime<Utc>) -> Result<DateTime<Utc>, RoundingError> {
        match self {
            Self::ToNearest(duration) => time.duration_round(*duration),
            Self::ToPast(duration) => time.duration_trunc(*duration),
            Self::ToFuture(duration) => time.duration_round_up(*duration),
        }
    }
}

/// Trait to try to re-precise absolute bounds
pub trait PreciseAbsoluteBounds {
    /// Output of methods precising the bounds
    type PrecisedBoundsOutput;

    /// Output of methods precising the start bound
    type PrecisedStartBoundOutput;

    /// Output of methods precising the end bound
    type PrecisedEndBoundOutput;

    /// Precises the start and end bound with different precisions for both of them
    #[must_use]
    fn precise_bounds_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedBoundsOutput;

    /// Precises the start and end bound with the given precision
    #[must_use]
    fn precise_bounds(&self, precision: Precision) -> Self::PrecisedBoundsOutput {
        self.precise_bounds_with_different_precisions(precision, precision)
    }

    /// Precises the start bound with the given precision
    #[must_use]
    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput;

    /// Precises the end bound with the given precision
    #[must_use]
    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput;
}

impl PreciseAbsoluteBounds for AbsoluteBounds {
    type PrecisedBoundsOutput = Result<Self, RoundingError>;
    type PrecisedStartBoundOutput = Result<AbsoluteStartBound, RoundingError>;
    type PrecisedEndBoundOutput = Result<AbsoluteEndBound, RoundingError>;

    fn precise_bounds_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedBoundsOutput {
        precise_abs_bounds(self, precision_start, precision_end)
    }

    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput {
        precise_abs_start_bound(self.start(), precision)
    }

    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput {
        precise_abs_end_bound(self.end(), precision)
    }
}

impl PreciseAbsoluteBounds for EmptiableAbsoluteBounds {
    type PrecisedBoundsOutput = Result<Self, RoundingError>;
    type PrecisedStartBoundOutput = Result<Option<AbsoluteStartBound>, RoundingError>;
    type PrecisedEndBoundOutput = Result<Option<AbsoluteEndBound>, RoundingError>;

    fn precise_bounds_with_different_precisions(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Self::PrecisedBoundsOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(EmptiableAbsoluteBounds::Bound(precise_abs_bounds(
                abs_bounds,
                start_precision,
                end_precision,
            )?));
        }

        Ok(EmptiableAbsoluteBounds::Empty)
    }

    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(Some(precise_abs_start_bound(abs_bounds.start(), precision)?));
        }

        Ok(None)
    }

    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(Some(precise_abs_end_bound(abs_bounds.end(), precision)?));
        }

        Ok(None)
    }
}

impl PreciseAbsoluteBounds for AbsoluteInterval {
    type PrecisedBoundsOutput = Result<Self, RoundingError>;
    type PrecisedStartBoundOutput = Result<Option<AbsoluteStartBound>, RoundingError>;
    type PrecisedEndBoundOutput = Result<Option<AbsoluteEndBound>, RoundingError>;

    fn precise_bounds_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedBoundsOutput {
        if let EmptiableAbsoluteBounds::Bound(ref abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(AbsoluteInterval::from(precise_abs_bounds(
                abs_bounds,
                precision_start,
                precision_end,
            )?));
        }

        Ok(AbsoluteInterval::Empty(EmptyInterval))
    }

    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(Some(precise_abs_start_bound(abs_bounds.start(), precision)?));
        }

        Ok(None)
    }

    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(Some(precise_abs_end_bound(abs_bounds.end(), precision)?));
        }

        Ok(None)
    }
}

/// Precises [`AbsoluteBounds`] with the given [`Precision`]s
///
/// # Errors
///
/// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
/// if the given duration used is too big, negative or zero, etc.
///
/// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
pub fn precise_abs_bounds(
    bounds: &AbsoluteBounds,
    precision_start: Precision,
    precision_end: Precision,
) -> Result<AbsoluteBounds, RoundingError> {
    Ok(AbsoluteBounds::new(
        precise_abs_start_bound(bounds.start(), precision_start)?,
        precise_abs_end_bound(bounds.end(), precision_end)?,
    ))
}

/// Precises an [`AbsoluteStartBound`] with the given [`Precision`]
///
/// # Errors
///
/// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
/// if the given duration used is too big, negative or zero, etc.
///
/// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
pub fn precise_abs_start_bound(
    bound: &AbsoluteStartBound,
    precision: Precision,
) -> Result<AbsoluteStartBound, RoundingError> {
    match bound {
        AbsoluteStartBound::InfinitePast => Ok(*bound),
        AbsoluteStartBound::Finite(finite_bound) => {
            Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                precision.precise_time(finite_bound.time())?,
                finite_bound.inclusivity(),
            )))
        },
    }
}

/// Precises an [`AbsoluteEndBound`] with the given [`Precision`]
///
/// # Errors
///
/// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
/// if the given duration used is too big, negative or zero, etc.
///
/// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
pub fn precise_abs_end_bound(
    bound: &AbsoluteEndBound,
    precision: Precision,
) -> Result<AbsoluteEndBound, RoundingError> {
    match bound {
        AbsoluteEndBound::InfiniteFuture => Ok(*bound),
        AbsoluteEndBound::Finite(finite_bound) => {
            Ok(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                precision.precise_time(finite_bound.time())?,
                finite_bound.inclusivity(),
            )))
        },
    }
}

/// Where the given time was found relative to a time interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimeContainmentPosition {
    /// The given time was found before the time interval's beginning
    OutsideBefore,
    /// The given time was found after the time interval's end
    OutsideAfter,
    /// The given time was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given time was found exactly on the start of the time interval
    ///
    /// The contained bound inclusivity indicates the bound inclusivity of the start bound.
    ///
    /// See [`Interval::containment_position`] for more details.
    OnStart(BoundInclusivity),
    /// The given time was found exactly on the end of the time interval
    ///
    /// The contained bound inclusivity indicates the bound inclusivity of the end bound.
    ///
    /// See [`Interval::containment_position`] for more details.
    OnEnd(BoundInclusivity),
    /// The given time was found within the time interval
    Inside,
}

impl TimeContainmentPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple(self) -> DisambiguatedTimeContainmentPosition {
        match self {
            Self::OutsideBefore => DisambiguatedTimeContainmentPosition::OutsideBefore,
            Self::OutsideAfter => DisambiguatedTimeContainmentPosition::OutsideAfter,
            Self::Outside => DisambiguatedTimeContainmentPosition::Outside,
            Self::OnStart(_) => DisambiguatedTimeContainmentPosition::OnStart,
            Self::OnEnd(_) => DisambiguatedTimeContainmentPosition::OnEnd,
            Self::Inside => DisambiguatedTimeContainmentPosition::Inside,
        }
    }

    /// Uses a rule set to transform the containment position into a simple but opinionated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple_using_rule_set(self, rule_set: TimeContainmentRuleSet) -> DisambiguatedTimeContainmentPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`TimeContainmentPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DisambiguatedTimeContainmentPosition {
    /// See [`OutsideBefore`](TimeContainmentPosition::OutsideBefore)
    OutsideBefore,
    /// See [`OutsideAfter`](TimeContainmentPosition::OutsideAfter)
    OutsideAfter,
    /// See [`Outside`](TimeContainmentPosition::Outside)
    Outside,
    /// See [`OnStart`](TimeContainmentPosition::OnStart)
    OnStart,
    /// See [`OnEnd`](TimeContainmentPosition::OnEnd)
    OnEnd,
    /// See [`Inside`](TimeContainmentPosition::Inside)
    Inside,
}

/// Different rule sets for determining whether different [`TimeContainmentPosition`]s are considered as containing or not.
///
/// See [`contains`](CanPositionTimeContainment::contains) for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum TimeContainmentRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds, so the time needs to fall on an inclusive bound in order to be counted
    /// as contained.
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// If the time falls on an exclusive bound, it is still counted as contained.
    Lenient,
}

impl TimeContainmentRuleSet {
    /// Disambiguates a containment position according to the rule set
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate(&self, containment_position: TimeContainmentPosition) -> DisambiguatedTimeContainmentPosition {
        match self {
            Self::Strict => strict_containment_rule_set_disambiguation(containment_position),
            Self::Lenient => lenient_containment_rule_set_disambiguation(containment_position),
        }
    }
}

/// Disambiguates a [`TimeContainmentPosition`] using [the strict rule set](TimeContainmentRuleSet::Strict)
#[must_use]
pub fn strict_containment_rule_set_disambiguation(
    containment_position: TimeContainmentPosition,
) -> DisambiguatedTimeContainmentPosition {
    match containment_position {
        TimeContainmentPosition::OutsideBefore | TimeContainmentPosition::OnStart(BoundInclusivity::Exclusive) => {
            DisambiguatedTimeContainmentPosition::OutsideBefore
        },
        TimeContainmentPosition::OutsideAfter | TimeContainmentPosition::OnEnd(BoundInclusivity::Exclusive) => {
            DisambiguatedTimeContainmentPosition::OutsideAfter
        },
        TimeContainmentPosition::Outside => DisambiguatedTimeContainmentPosition::Outside,
        TimeContainmentPosition::OnStart(BoundInclusivity::Inclusive) => DisambiguatedTimeContainmentPosition::OnStart,
        TimeContainmentPosition::OnEnd(BoundInclusivity::Inclusive) => DisambiguatedTimeContainmentPosition::OnEnd,
        TimeContainmentPosition::Inside => DisambiguatedTimeContainmentPosition::Inside,
    }
}

/// Disambiguates a [`TimeContainmentPosition`] using [the lenient rule set](TimeContainmentRuleSet::Lenient)
#[must_use]
pub fn lenient_containment_rule_set_disambiguation(
    containment_position: TimeContainmentPosition,
) -> DisambiguatedTimeContainmentPosition {
    match containment_position {
        TimeContainmentPosition::OutsideBefore => DisambiguatedTimeContainmentPosition::OutsideBefore,
        TimeContainmentPosition::OutsideAfter => DisambiguatedTimeContainmentPosition::OutsideAfter,
        TimeContainmentPosition::Outside => DisambiguatedTimeContainmentPosition::Outside,
        TimeContainmentPosition::OnStart(_) => DisambiguatedTimeContainmentPosition::OnStart,
        TimeContainmentPosition::OnEnd(_) => DisambiguatedTimeContainmentPosition::OnEnd,
        TimeContainmentPosition::Inside => DisambiguatedTimeContainmentPosition::Inside,
    }
}

/// Time containment rules used as the reference for the predefined decisions
pub const DEFAULT_TIME_CONTAINMENT_RULES: [TimeContainmentRule; 0] = [];

/// All rules for containment by converting a [`DisambiguatedTimeContainmentPosition`] into a [`bool`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimeContainmentRule {
    /// Doesn't count as contained when the time is on the start of the interval
    DenyOnStart,
    /// Doesn't count as contained when the time is on the end of the interval
    DenyOnEnd,
    /// Doesn't count as contained when the time is on either end of the interval
    DenyOnBounds,
}

impl TimeContainmentRule {
    /// Returns whether the given [`SimpleContainmentPosition`] counts as contained
    #[must_use]
    pub fn counts_as_contained(&self, simple_containment_position: DisambiguatedTimeContainmentPosition) -> bool {
        match self {
            Self::DenyOnStart => deny_on_start_containment_rule_counts_as_contained(simple_containment_position),
            Self::DenyOnEnd => deny_on_end_containment_rule_counts_as_contained(simple_containment_position),
            Self::DenyOnBounds => deny_on_bounds_containment_rule_counts_as_contained(simple_containment_position),
        }
    }
}

/// Checks whether the given [`DisambiguatedTimeContainmentPosition`] respects [the 'deny on start' rule](TimeContainmentRule::DenyOnStart)
#[must_use]
pub fn deny_on_start_containment_rule_counts_as_contained(
    simple_containment_position: DisambiguatedTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        DisambiguatedTimeContainmentPosition::OutsideBefore
            | DisambiguatedTimeContainmentPosition::OutsideAfter
            | DisambiguatedTimeContainmentPosition::Outside
            | DisambiguatedTimeContainmentPosition::OnStart
    )
}

/// Checks whether the given [`DisambiguatedTimeContainmentPosition`] respects [the 'deny on end' rule](TimeContainmentRule::DenyOnEnd)
#[must_use]
pub fn deny_on_end_containment_rule_counts_as_contained(
    simple_containment_position: DisambiguatedTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        DisambiguatedTimeContainmentPosition::OutsideBefore
            | DisambiguatedTimeContainmentPosition::OutsideAfter
            | DisambiguatedTimeContainmentPosition::Outside
            | DisambiguatedTimeContainmentPosition::OnEnd
    )
}

/// Checks whether the given [`DisambiguatedTimeContainmentPosition`] respects [the 'deny on bounds' rule](TimeContainmentRule::DenyOnBounds)
#[must_use]
pub fn deny_on_bounds_containment_rule_counts_as_contained(
    simple_containment_position: DisambiguatedTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        DisambiguatedTimeContainmentPosition::OutsideBefore
            | DisambiguatedTimeContainmentPosition::OutsideAfter
            | DisambiguatedTimeContainmentPosition::Outside
            | DisambiguatedTimeContainmentPosition::OnStart
            | DisambiguatedTimeContainmentPosition::OnEnd
    )
}

/// Where the current time interval was found relative to the other time interval
///
/// See [`overlap_position`](CanPositionOverlap::overlap_position) for more information
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapPosition {
    /// The current time interval was found before the given other time interval
    OutsideBefore,
    /// The current time interval was found after the given other time interval
    OutsideAfter,
    /// The current time interval was found outside the given other time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The current time interval was found ending on the beginning of the given other time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    OnStart(BoundInclusivity, BoundInclusivity),
    /// The current time interval was found starting on the end of the given other time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    OnEnd(BoundInclusivity, BoundInclusivity),
    /// The current time interval was found beginning outside the given other time interval but ending inside
    CrossesStart,
    /// The current time interval was found beginning inside the given other time interval but ending outside
    CrossesEnd,
    /// The current time interval was found completely inside the given other time interval
    Inside,
    /// The current time interval was found beginning on the start of the given other time interval and ending inside
    /// that time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    InsideAndSameStart(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning inside the given other time interval and ending at the end of
    /// that time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    InsideAndSameEnd(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning and ending at the same times as the given other time interval
    ///
    /// The contained bound inclusivities define the reference interval's start and end inclusivities (first tuple),
    /// and the compared interval's start and end inclusivities (second tuple).
    ///
    /// Since half-open intervals only have a single defined bound, the second element of each tuple is an [`Option`].
    /// Also, when you compare two open intervals, they don't have defined bounds but still are equal, so all elements
    /// are [`Option`]s in the end.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    Equal(
        (Option<BoundInclusivity>, Option<BoundInclusivity>),
        (Option<BoundInclusivity>, Option<BoundInclusivity>),
    ),
    /// The current time interval was found beginning on the same point as the given other time interval and ending
    /// after that time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    ContainsAndSameStart(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning before the given other time interval and ending at the same time
    /// as that time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    ContainsAndSameEnd(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning before the given other time interval's start
    /// and ending after that time interval's end
    Contains,
}

impl OverlapPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple(self) -> DisambiguatedOverlapPosition {
        match self {
            OverlapPosition::OutsideBefore => DisambiguatedOverlapPosition::OutsideBefore,
            OverlapPosition::OutsideAfter => DisambiguatedOverlapPosition::OutsideAfter,
            OverlapPosition::Outside => DisambiguatedOverlapPosition::Outside,
            OverlapPosition::OnStart(..) => DisambiguatedOverlapPosition::OnStart,
            OverlapPosition::OnEnd(..) => DisambiguatedOverlapPosition::OnEnd,
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

    /// Uses a rule set to transform the overlap position into a simple but opinionated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple_using_rule_set(self, rule_set: OverlapRuleSet) -> DisambiguatedOverlapPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`OverlapPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DisambiguatedOverlapPosition {
    /// See [`OverlapPosition::OutsideBefore`]
    OutsideBefore,
    /// See [`OverlapPosition::OutsideAfter`]
    OutsideAfter,
    /// See [`OverlapPosition::Outside`]
    Outside,
    /// See [`OverlapPosition::OnStart`]
    OnStart,
    /// See [`OverlapPosition::OnEnd`]
    OnEnd,
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

/// Different rule sets for determining whether different [`OverlapPosition`]s are considered as overlapping or not.
///
/// See [`Interval::overlaps_using_rule_set`] for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum OverlapRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds. Here's a table of interactions for ambiguous cases:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:                 [-------]
    /// OutsideBefore       [------)       :
    /// OutsideAfter               :       (-----]
    /// InsideAndSameEnd           (-------]
    /// InsideAndSameStart         [-------)
    /// Inside                     (-------)
    /// CrossesStart            [----------)
    /// CrossesEnd                 (----------]
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
    /// Continuous to future rule set
    ///
    /// Like the [strict rule set](OverlapRuleSet::Strict), but counts as [`OnStart`](OverlapPosition::OnStart) when
    /// the reference interval's inclusive start bound meets the compared interval's exclusive end bound, and counts as
    /// [`OnEnd`](OverlapPosition::OnEnd) when the reference interval's exclusive end bound meets the compared
    /// interval's inclusive start bound. Here's a table to illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            [------)
    /// OnStart          [----)      :
    /// OnEnd                 :      [-----]
    /// ```
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Like the [strict rule set](OverlapRuleSet::Strict), but counts as [`OnStart`](OverlapPosition::OnStart) when
    /// the reference interval's exclusive start bound meets the compared interval's inclusive end bound, and counts as
    /// [`OnEnd`](OverlapPosition::OnEnd) when the reference interval's inclusive end bound meets the compared
    /// interval's exclusive start bound. Here's a table to illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            (------]
    /// OnStart          [----]      :
    /// OnEnd                 :      (-----]
    /// ```
    ContinuousToPast,
    /// Lenient rule set
    ///
    /// Allows interactions that would count as not overlapping (or not overlapping _as much_) under the strict rule set
    /// but doesn't allow cases where two exclusive bounds of opposite source (start/end) meet. Here's a table to
    /// illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:                [------]
    /// OnStart             [-----)      :
    /// OnEnd                     :      (-----]
    /// Equal                     (------]
    /// Equal                     [------)
    /// Equal                     (------)
    /// InsideAndSameStart        (---]  :
    /// InsideAndSameEnd          :  [---)
    /// ContainsAndSameStart      (----------]
    /// ContainsAndSameEnd    [----------)
    ///
    /// Reference:                (------)
    /// OnStart             [-----]      :
    /// OnEnd                     :      [-----]
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
    /// Same as the [lenient rule set](OverlapRuleSet::Lenient), but allows cases where two exclusive bounds of
    /// opposite source (start/end) meet.
    VeryLenient,
}

impl OverlapRuleSet {
    /// Disambiguates an overlap position according to the rule set
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate(&self, overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
        match self {
            Self::Strict => strict_overlap_rule_set_disambiguation(overlap_position),
            Self::ContinuousToFuture => continuous_to_future_overlap_rule_set_disambiguation(overlap_position),
            Self::ContinuousToPast => continuous_to_past_overlap_rule_set_disambiguation(overlap_position),
            Self::Lenient => lenient_overlap_rule_set_disambiguation(overlap_position),
            Self::VeryLenient => very_lenient_overlap_rule_set_disambiguation(overlap_position),
        }
    }
}

/// Disambiguates an [`OverlapPosition`] using [the strict rule set](OverlapRuleSet::Strict)
#[must_use]
pub fn strict_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::Outside => Dop::Outside,
        Op::OnStart(Bi::Inclusive, Bi::Inclusive) => Dop::OnStart,
        Op::OnStart(..) | Op::OutsideBefore => Dop::OutsideBefore,
        Op::OnEnd(Bi::Inclusive, Bi::Inclusive) => Dop::OnEnd,
        Op::OnEnd(..) | Op::OutsideAfter => Dop::OutsideAfter,
        Op::CrossesStart
        | Op::InsideAndSameStart(Some(Bi::Exclusive), Some(Bi::Inclusive))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Inclusive)), (Some(Bi::Inclusive), Some(Bi::Exclusive)))
        | Op::ContainsAndSameEnd(Some(Bi::Inclusive), Some(Bi::Exclusive)) => Dop::CrossesStart,
        Op::CrossesEnd
        | Op::Equal((Some(Bi::Inclusive), Some(Bi::Exclusive)), (Some(Bi::Exclusive), Some(Bi::Inclusive)))
        | Op::ContainsAndSameStart(Some(Bi::Inclusive), Some(Bi::Exclusive)) => Dop::CrossesEnd,
        Op::Inside
        | Op::InsideAndSameStart(Some(Bi::Inclusive), Some(Bi::Exclusive))
        | Op::Equal((Some(Bi::Inclusive), Some(Bi::Inclusive)), (Some(Bi::Exclusive), Some(Bi::Exclusive))) => {
            Dop::Inside
        },
        Op::InsideAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::InsideAndSameStart,
        Op::InsideAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::InsideAndSameEnd,
        Op::Equal((incl_ref_from, incl_ref_to), (incl_comp_from, incl_comp_to))
            if incl_ref_from == incl_comp_from && incl_ref_to == incl_comp_to =>
        {
            Dop::Equal
        },
        Op::Equal((Some(Bi::Inclusive), Some(Bi::Inclusive)), (Some(Bi::Inclusive), Some(Bi::Exclusive)))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Inclusive)), (Some(Bi::Exclusive), Some(Bi::Exclusive))) => {
            Dop::InsideAndSameStart
        },
        Op::Equal((Some(Bi::Inclusive), Some(Bi::Inclusive)), (Some(Bi::Exclusive), Some(Bi::Inclusive)))
        | Op::Equal((Some(Bi::Inclusive), Some(Bi::Exclusive)), (Some(Bi::Exclusive), Some(Bi::Exclusive))) => {
            Dop::InsideAndSameEnd
        },
        Op::Equal((Some(Bi::Inclusive), Some(Bi::Exclusive)), (Some(Bi::Inclusive), Some(Bi::Inclusive)))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Exclusive)), (Some(Bi::Exclusive), Some(Bi::Inclusive))) => {
            Dop::ContainsAndSameStart
        },
        Op::Equal((Some(Bi::Exclusive), Some(Bi::Inclusive)), (Some(Bi::Inclusive), Some(Bi::Inclusive)))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Exclusive)), (Some(Bi::Inclusive), Some(Bi::Exclusive))) => {
            Dop::ContainsAndSameEnd
        },
        Op::Equal((Some(Bi::Exclusive), Some(Bi::Exclusive)), (Some(Bi::Inclusive), Some(Bi::Inclusive)))
        | Op::ContainsAndSameStart(Some(Bi::Exclusive), Some(Bi::Inclusive))
        | Op::ContainsAndSameEnd(Some(Bi::Exclusive), Some(Bi::Inclusive))
        | Op::Contains => Dop::Contains,
        Op::ContainsAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::ContainsAndSameStart,
        Op::ContainsAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::ContainsAndSameEnd,
        Op::InsideAndSameStart(None, Some(_)) | Op::InsideAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        Op::InsideAndSameEnd(None, Some(_)) | Op::InsideAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        Op::ContainsAndSameStart(None, Some(_)) | Op::ContainsAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        Op::ContainsAndSameEnd(None, Some(_)) | Op::ContainsAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        Op::InsideAndSameStart(..)
        | Op::InsideAndSameEnd(..)
        | Op::Equal(..)
        | Op::ContainsAndSameStart(..)
        | Op::ContainsAndSameEnd(..) => unreachable!("Already handled dynamically"),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the 'continuous to future' rule set](OverlapRuleSet::ContinuousToFuture)
#[must_use]
pub fn continuous_to_future_overlap_rule_set_disambiguation(
    overlap_position: OverlapPosition,
) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::OnStart(Bi::Inclusive, _) => Dop::OnStart,
        Op::OnStart(..) => Dop::OutsideBefore,
        Op::OnEnd(_, Bi::Inclusive) => Dop::OnEnd,
        Op::OnEnd(..) => Dop::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the 'continuous to past' rule set](OverlapRuleSet::ContinuousToPast)
#[must_use]
pub fn continuous_to_past_overlap_rule_set_disambiguation(
    overlap_position: OverlapPosition,
) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::OnStart(_, Bi::Inclusive) => Dop::OnStart,
        Op::OnStart(..) => Dop::OutsideBefore,
        Op::OnEnd(Bi::Inclusive, _) => Dop::OnEnd,
        Op::OnEnd(..) => Dop::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the lenient rule set](OverlapRuleSet::Lenient)
#[must_use]
pub fn lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::OutsideBefore | Op::OnStart(Bi::Exclusive, Bi::Exclusive) => Dop::OutsideBefore,
        Op::OutsideAfter | Op::OnEnd(Bi::Exclusive, Bi::Exclusive) => Dop::OutsideAfter,
        Op::Outside => Dop::Outside,
        Op::OnStart(..) => Dop::OnStart,
        Op::OnEnd(..) => Dop::OnEnd,
        Op::CrossesStart => Dop::CrossesStart,
        Op::CrossesEnd => Dop::CrossesEnd,
        Op::Inside => Dop::Inside,
        Op::InsideAndSameStart(..) => Dop::InsideAndSameStart,
        Op::InsideAndSameEnd(..) => Dop::InsideAndSameEnd,
        Op::Equal(..) => Dop::Equal,
        Op::Contains => Dop::Contains,
        Op::ContainsAndSameStart(..) => Dop::ContainsAndSameStart,
        Op::ContainsAndSameEnd(..) => Dop::ContainsAndSameEnd,
    }
}

/// Disambiguates an [`OverlapPosition`] using [the very lenient rule set](OverlapRuleSet::VeryLenient)
#[must_use]
pub fn very_lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
    overlap_position.to_simple()
}

/// Default overlap rules
pub const DEFAULT_OVERLAP_RULES: [OverlapRule; 1] = [OverlapRule::DenyAdjacency];

/// All rules for overlapping by converting a [`DisambiguatedOverlapPosition`] into a [`bool`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapRule {
    /// Counts adjacent / "touching" intervals as overlapping
    AllowAdjacency,
    /// Doesn't count adjacent / "touching" intervals as overlapping
    DenyAdjacency,
    /// Counts interval as overlapping if it is adjacent only in the past compared to the reference interval
    AllowPastAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent only in the past compared to the reference interval
    ///
    /// Same as [`OverlapRule::AllowFutureAdjacency`]
    DenyPastAdjacency,
    /// Counts interval as overlapping if it is adjacent only in the future compared to the reference interval
    AllowFutureAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent only in the future compared to the reference interval
    ///
    /// Same as [`OverlapRule::AllowPastAdjacency`]
    DenyFutureAdjacency,
}

impl OverlapRule {
    /// Returns whether the given [`DisambiguatedOverlapPosition`] counts as overlap
    #[must_use]
    pub fn counts_as_overlap(&self, disambiguated_overlap_position: DisambiguatedOverlapPosition) -> bool {
        match self {
            Self::AllowAdjacency => allow_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position),
            Self::DenyAdjacency => deny_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position),
            Self::AllowPastAdjacency | Self::DenyFutureAdjacency => {
                allow_past_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position)
            },
            Self::AllowFutureAdjacency | Self::DenyPastAdjacency => {
                allow_future_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position)
            },
        }
    }
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow adjacency' rule](OverlapRule::AllowAdjacency)
#[must_use]
pub fn allow_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
    )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'deny adjacency' rule](OverlapRule::DenyAdjacency)
#[must_use]
pub fn deny_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
            | DisambiguatedOverlapPosition::OnStart
            | DisambiguatedOverlapPosition::OnEnd
    )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow past adjacency' rule](OverlapRule::AllowPastAdjacency)
#[must_use]
pub fn allow_past_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
            | DisambiguatedOverlapPosition::OnEnd
    )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow future adjacency' rule](OverlapRule::AllowFutureAdjacency)
#[must_use]
pub fn allow_future_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
            | DisambiguatedOverlapPosition::OnStart
    )
}

/// Capacity to position where a given time is contained in an interval
pub trait CanPositionTimeContainment {
    /// Error type if the time containment positioning failed
    type Error;

    /// Returns the containment position of the given time
    ///
    /// # Bound inclusivity
    ///
    /// When checking the containment position, the reference interval's bound inclusivities are considered
    /// as inclusive. Then, on cases where the result could be ambiguous (e.g. if the time ends up on the reference
    /// interval's start but the inclusivity of this bound is exclusive, does it qualify
    /// as [`TimeContainmentPosition::OnStart`]?), we simply include the inclusivity of the concerned bound and let the
    /// receiver make the call on whether it counts or not.
    ///
    /// This way, we can guarantee maximum flexibility of this process.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionTimeContainment::Error).
    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error>;

    /// Returns the disambiguated containment position of the given time using a given [containment rule set](TimeContainmentRuleSet)
    ///
    /// See [`CanPositionTimeContainment::time_containment_position`] for more details about containment position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionTimeContainment::Error).
    fn disambiguated_time_containment_position(
        &self,
        time: DateTime<Utc>,
        rule_set: TimeContainmentRuleSet,
    ) -> Result<DisambiguatedTimeContainmentPosition, Self::Error> {
        self.time_containment_position(time)
            .map(|containment_position| rule_set.disambiguate(containment_position))
    }

    /// Returns whether the given time is contained in the interval using predetermined rules
    ///
    /// Uses the [default rule set](TimeContainmentRuleSet::default) with default rules.
    ///
    /// The rule set has been chosen because they are the closest to how we mathematically
    /// and humanly interpret containment.
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see [`contains`](CanPositionTimeContainment::contains).
    ///
    /// If you want even more granular control, see [`contains_using_simple`](CanPositionTimeContainment::contains_using_simple).
    #[must_use]
    fn simple_contains(&self, time: DateTime<Utc>) -> bool {
        self.contains(time, TimeContainmentRuleSet::default(), &DEFAULT_TIME_CONTAINMENT_RULES)
    }

    /// Returns whether the given time is contained in the interval using the given [containment rules](`TimeContainmentRule`)
    ///
    /// This method uses [`disambiguated_time_containment_position`](CanPositionTimeContainment::disambiguated_time_containment_position).
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the [`TimeContainmentRule`]s are checked. This method returns true only if all provided
    /// [`TimeContainmentRule`]s are respected (i.e. returned true when calling [`TimeContainmentRule::counts_as_contained`]).
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for containment, see [`simple_contains`](CanPositionTimeContainment::simple_contains).
    ///
    /// If you are looking for more control over what counts as contained, see [`contains_using_simple`](CanPositionTimeContainment::contains_using_simple).
    ///
    /// If you want extremely granular control over what counts as contained, see [`contains_using`](CanPositionTimeContainment::contains_using).
    #[must_use]
    fn contains<'a, RI>(&self, time: DateTime<Utc>, rule_set: TimeContainmentRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a TimeContainmentRule>,
    {
        self.disambiguated_time_containment_position(time, rule_set)
            .map(|simple_containment_position| {
                rules
                    .into_iter()
                    .all(|rule| rule.counts_as_contained(simple_containment_position))
            })
            .unwrap_or(false)
    }

    /// Returns whether the given time is contained in the interval using a custom function
    ///
    /// This method uses [`time_containment_position`](CanPositionTimeContainment::time_containment_position).
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`TimeContainmentPosition`]
    /// given by [`time_containment_position`](CanPositionTimeContainment::time_containment_position) counts as
    /// the passed time being contained in the interval.
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as containment but still want
    /// predetermined [`DisambiguatedTimeContainmentPosition`]s, see [`contains_using_simple`](CanPositionTimeContainment::contains_using_simple).
    ///
    /// If you are looking for predetermined decisions on what's considered as contained, see [`contains`](CanPositionTimeContainment::contains).
    #[must_use]
    fn contains_using<F>(&self, time: DateTime<Utc>, f: F) -> bool
    where
        F: FnOnce(TimeContainmentPosition) -> bool,
    {
        self.time_containment_position(time).map(f).unwrap_or(false)
    }

    /// Returns whether the given time is contained in the interval using a custom function
    ///
    /// This method uses [`disambiguated_time_containment_position`](CanPositionTimeContainment::disambiguated_time_containment_position).
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`DisambiguatedTimeContainmentPosition`]
    /// given by [`disambiguated_time_containment_position`](CanPositionTimeContainment::disambiguated_time_containment_position) counts as contained or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as contained, see [`contains_using`](CanPositionTimeContainment::contains_using).
    ///
    /// If you are looking for predetermined decisions on what's considered as contained, see [`simple_contains`](CanPositionTimeContainment::simple_contains).
    #[must_use]
    fn contains_using_simple<F>(&self, time: DateTime<Utc>, rule_set: TimeContainmentRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedTimeContainmentPosition) -> bool,
    {
        self.disambiguated_time_containment_position(time, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

impl<T> CanPositionTimeContainment for T
where
    T: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        let EmptiableAbsoluteBounds::Bound(bounds) = self.emptiable_abs_bounds() else {
            return Ok(TimeContainmentPosition::Outside);
        };

        Ok(time_containment_position_abs_bounds(&bounds, time))
    }
}

/// Returns the [`TimeContainmentPosition`] of the given time within the given [`AbsoluteBounds`]
#[must_use]
pub fn time_containment_position_abs_bounds(bounds: &AbsoluteBounds, time: DateTime<Utc>) -> TimeContainmentPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;
    type ContPos = TimeContainmentPosition;

    match (bounds.abs_start(), bounds.abs_end()) {
        (StartB::InfinitePast, EndB::InfiniteFuture) => ContPos::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_bound)) => match time.cmp(&finite_bound.time()) {
            Ordering::Less => ContPos::Inside,
            Ordering::Equal => ContPos::OnEnd(finite_bound.inclusivity()),
            Ordering::Greater => ContPos::OutsideAfter,
        },
        (StartB::Finite(finite_bound), EndB::InfiniteFuture) => match time.cmp(&finite_bound.time()) {
            Ordering::Less => ContPos::OutsideBefore,
            Ordering::Equal => ContPos::OnStart(finite_bound.inclusivity()),
            Ordering::Greater => ContPos::Inside,
        },
        (StartB::Finite(start_bound), EndB::Finite(end_bound)) => {
            match (time.cmp(&start_bound.time()), time.cmp(&end_bound.time())) {
                (Ordering::Less, _) => ContPos::OutsideBefore,
                (Ordering::Equal, _) => ContPos::OnStart(start_bound.inclusivity()),
                (_, Ordering::Less) => ContPos::Inside,
                (_, Ordering::Equal) => ContPos::OnEnd(end_bound.inclusivity()),
                (_, Ordering::Greater) => ContPos::OutsideAfter,
            }
        },
    }
}

/// Capacity to position an overlap from a given [`HasEmptiableAbsoluteBounds`] implementor
pub trait CanPositionOverlap<Rhs = Self> {
    /// Error type if the overlap positioning failed
    type Error;

    /// Returns the overlap position of the given interval
    ///
    /// The current interval is compared to the other interval, that means that if you, for example, compare
    /// a closed absolute interval (instance) with an open interval (given interval), you will get
    /// [`OverlapPosition::Inside`] as the closed absolute interval _is contained_ by an open interval.
    ///
    /// An empty interval is always outside, even if compared against an open interval, as an empty interval is a
    /// concept-value (like infinity) rather than an actual value.
    ///
    /// # Bound inclusivity
    ///
    /// When checking the overlap position, the all bound inclusivities are considered as inclusive.
    /// Then, on cases where the result could be ambiguous (e.g. if the compared interval's start ends up on
    /// the reference interval's start but the reference's inclusivity of this bound is exclusive, or maybe both
    /// intervals' concerned bound are exclusive, does it qualify as [`OverlapPosition::OnStart`]?),
    /// we simply include the inclusivity of the concerned bound and let the receiver make the call on whether
    /// it counts or not.
    ///
    /// This way, we can guarantee maximum flexibility of this process.
    ///
    /// Ambiguous overlap positions contains the reference interval concerned bound's inclusivity first,
    /// then the compared interval concerned bound's inclusivity second.
    ///
    /// The only exception to that is [`OverlapPosition::Equal`], where its first tuple is the bound inclusivities for
    /// the reference interval, and its second tuple is the bound inclusivities for the compared interval.
    ///
    /// Since half-open and open intervals are also subject to the overlap position check, most ambiguous overlap
    /// positions have one or all of their elements as [`Option`]s. Those elements are set to [`None`] only when
    /// there is no bound to speak of. The order of the elements remains the same though: first the reference, then
    /// the compared.
    ///
    /// In the case of a pair of half-open intervals being compared, since they only have one bound, the second element
    /// of each tuple will be [`None`].
    /// In the case of a pair of open intervals being compared, since they have no bounds but still are equal, all
    /// elements will be [`None`].
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    fn overlap_position(&self, other: &Rhs) -> Result<OverlapPosition, Self::Error>;

    /// Returns the disambiguated overlap position of the given interval using a given rule set
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

    /// Returns whether the given other interval overlaps the current one using predetermined rules
    ///
    /// Uses the [default rule set](OverlapRuleSet::default) with the default rules,
    ///
    /// Those have been chosen because they are the closest to how we mathematically and humanly interpret overlaps.
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see [`CanPositionOverlap::overlaps`].
    ///
    /// If you want even more granular control, see [`CanPositionOverlap::overlaps_using_simple`].
    #[must_use]
    fn simple_overlaps(&self, other: &Rhs) -> bool {
        self.overlaps(other, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns whether the given other interval overlaps the current one using the given [overlap rules](`OverlapRule`)
    ///
    /// This method uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position). If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the [`OverlapRule`]s are checked. This method returns true only if all provided
    /// [`OverlapRule`]s are respected (i.e. returned true when calling [`OverlapRule::counts_as_overlap`]).
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for overlap, see [`simple_overlaps`](CanPositionOverlap::simple_overlaps).
    ///
    /// If you are looking for more control over what counts as overlap, see [`overlaps_using_simple`](CanPositionOverlap::overlaps_using_simple).
    ///
    /// If you want extremely granular control over what counts as overlap, see [`overlaps_using`](CanPositionOverlap::overlaps_using).
    #[must_use]
    fn overlaps<'a, RI>(&self, other: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a OverlapRule>,
    {
        self.disambiguated_overlap_position(other, rule_set)
            .map(|disambiguated_overlap_position| {
                rules
                    .into_iter()
                    .all(|rule| rule.counts_as_overlap(disambiguated_overlap_position))
            })
            .unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using a custom function
    ///
    /// This method uses [`CanPositionOverlap::overlap_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`OverlapPosition`]
    /// given by [`CanPositionOverlap::overlap_position`] counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as overlapping but still want
    /// predetermined [`DisambiguatedOverlapPosition`]s, see [`CanPositionOverlap::overlaps_using_simple`].
    ///
    /// If you are looking for predetermined decisions on what's considered as overlapping, see [`CanPositionOverlap::overlaps`].
    #[must_use]
    fn overlaps_using<F>(&self, other: &Rhs, f: F) -> bool
    where
        F: FnOnce(OverlapPosition) -> bool,
    {
        self.overlap_position(other).map(f).unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using a custom function
    ///
    /// This method uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position). If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`DisambiguatedOverlapPosition`]
    /// given by [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position) counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as overlapping, see [`CanPositionOverlap::overlaps_using`].
    ///
    /// If you are looking for predetermined decisions on what's considered as overlapping, see [`CanPositionOverlap::overlaps`].
    #[must_use]
    fn overlaps_using_simple<F>(&self, other: &Rhs, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedOverlapPosition) -> bool,
    {
        self.disambiguated_overlap_position(other, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

impl<T, Rhs> CanPositionOverlap<Rhs> for T
where
    Rhs: HasEmptiableAbsoluteBounds,
    T: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, other: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &other.emptiable_abs_bounds(),
        ))
    }
}

/// Positions the overlap between two implementors of [`HasEmptiableAbsoluteBounds`]
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

/// Positions the overlap between two [`AbsoluteBounds`]
#[must_use]
pub fn overlap_position_abs_bounds(og: &AbsoluteBounds, other: &AbsoluteBounds) -> OverlapPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;
    type OP = OverlapPosition;

    match ((og.start(), og.end()), (other.start(), other.end())) {
        ((StartB::InfinitePast, EndB::InfiniteFuture), (StartB::InfinitePast, EndB::InfiniteFuture)) => {
            OP::Equal((None, None), (None, None))
        },
        ((StartB::InfinitePast, EndB::InfiniteFuture), (StartB::InfinitePast, EndB::Finite(..))) => {
            OP::ContainsAndSameStart(None, None)
        },
        ((StartB::InfinitePast, EndB::InfiniteFuture), (StartB::Finite(..), EndB::InfiniteFuture)) => {
            OP::ContainsAndSameEnd(None, None)
        },
        ((StartB::InfinitePast, EndB::InfiniteFuture), _) => OP::Contains,
        ((StartB::InfinitePast, EndB::Finite(..)), (StartB::InfinitePast, EndB::InfiniteFuture)) => {
            OP::InsideAndSameStart(None, None)
        },
        ((StartB::Finite(..), EndB::InfiniteFuture), (StartB::InfinitePast, EndB::InfiniteFuture)) => {
            OP::InsideAndSameEnd(None, None)
        },
        (_, (StartB::InfinitePast, EndB::InfiniteFuture)) => OP::Inside,
        ((StartB::InfinitePast, EndB::Finite(og_end)), (StartB::InfinitePast, EndB::Finite(other_end))) => {
            match og_end.time().cmp(&other_end.time()) {
                Ordering::Less => OP::InsideAndSameStart(None, None),
                Ordering::Equal => OP::Equal(
                    (None, Some(og_end.inclusivity())),
                    (None, Some(other_end.inclusivity())),
                ),
                Ordering::Greater => OP::ContainsAndSameStart(None, None),
            }
        },
        ((StartB::Finite(og_start), EndB::InfiniteFuture), (StartB::Finite(other_start), EndB::InfiniteFuture)) => {
            match og_start.time().cmp(&other_start.time()) {
                Ordering::Less => OP::ContainsAndSameEnd(None, None),
                Ordering::Equal => OP::Equal(
                    (Some(og_start.inclusivity()), None),
                    (Some(other_start.inclusivity()), None),
                ),
                Ordering::Greater => OP::InsideAndSameEnd(None, None),
            }
        },
        ((StartB::InfinitePast, EndB::Finite(og_end)), (StartB::Finite(other_start), EndB::InfiniteFuture)) => {
            match og_end.time().cmp(&other_start.time()) {
                Ordering::Less => OP::OutsideBefore,
                Ordering::Equal => OP::OnStart(og_end.inclusivity(), other_start.inclusivity()),
                Ordering::Greater => OP::CrossesStart,
            }
        },
        ((StartB::Finite(og_start), EndB::InfiniteFuture), (StartB::InfinitePast, EndB::Finite(other_end))) => {
            match og_start.time().cmp(&other_end.time()) {
                Ordering::Less => OP::CrossesStart,
                Ordering::Equal => OP::OnEnd(og_start.inclusivity(), other_end.inclusivity()),
                Ordering::Greater => OP::OutsideAfter,
            }
        },
        ((StartB::InfinitePast, EndB::Finite(ref_bound)), (StartB::Finite(other_start), EndB::Finite(other_end))) => {
            overlap_position_half_open_past_closed(ref_bound, other_start, other_end)
        },
        ((StartB::Finite(ref_bound), EndB::InfiniteFuture), (StartB::Finite(other_start), EndB::Finite(other_end))) => {
            overlap_position_half_open_future_closed(ref_bound, other_start, other_end)
        },
        ((StartB::Finite(og_start), EndB::Finite(og_end)), (StartB::InfinitePast, EndB::Finite(ref_bound))) => {
            overlap_position_closed_half_open_past(og_start, og_end, ref_bound)
        },
        ((StartB::Finite(og_start), EndB::Finite(og_end)), (StartB::Finite(ref_bound), EndB::InfiniteFuture)) => {
            overlap_position_closed_half_open_future(og_start, og_end, ref_bound)
        },
        ((StartB::Finite(og_start), EndB::Finite(og_end)), (StartB::Finite(other_start), EndB::Finite(other_end))) => {
            overlap_position_closed_pair(og_start, og_end, other_start, other_end)
        },
    }
}

/// Positions the overlap between a half-open interval going to the past and a closed interval
#[must_use]
pub fn overlap_position_half_open_past_closed(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::OnStart(ref_bound.inclusivity(), other_start.inclusivity()),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => {
            OverlapPosition::ContainsAndSameEnd(Some(ref_bound.inclusivity()), Some(other_end.inclusivity()))
        },
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between a half-open interval going to the future and a closed interval
#[must_use]
pub fn overlap_position_half_open_future_closed(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => {
            OverlapPosition::ContainsAndSameStart(Some(ref_bound.inclusivity()), Some(other_start.inclusivity()))
        },
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::OnEnd(ref_bound.inclusivity(), other_end.inclusivity()),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the past
#[must_use]
pub fn overlap_position_closed_half_open_past(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::OnEnd(og_start.inclusivity(), ref_bound.inclusivity()),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => {
            OverlapPosition::InsideAndSameEnd(Some(og_end.inclusivity()), Some(ref_bound.inclusivity()))
        },
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the future
#[must_use]
pub fn overlap_position_closed_half_open_future(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => {
            OverlapPosition::InsideAndSameStart(Some(og_start.inclusivity()), Some(ref_bound.inclusivity()))
        },
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::OnStart(og_end.inclusivity(), ref_bound.inclusivity()),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two closed intervals
#[must_use]
pub fn overlap_position_closed_pair(
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
        (_, (Ordering::Equal, _)) => OverlapPosition::OnStart(og_end.inclusivity(), other_start.inclusivity()),
        ((_, Ordering::Equal), _) => OverlapPosition::OnEnd(og_start.inclusivity(), other_end.inclusivity()),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => {
            OverlapPosition::InsideAndSameStart(Some(og_start.inclusivity()), Some(other_start.inclusivity()))
        },
        ((Ordering::Greater, _), (_, Ordering::Equal)) => {
            OverlapPosition::InsideAndSameEnd(Some(og_end.inclusivity()), Some(other_end.inclusivity()))
        },
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            (Some(og_start.inclusivity()), Some(og_end.inclusivity())),
            (Some(other_start.inclusivity()), Some(other_end.inclusivity())),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => {
            OverlapPosition::ContainsAndSameStart(Some(og_start.inclusivity()), Some(other_start.inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Equal)) => {
            OverlapPosition::ContainsAndSameEnd(Some(og_end.inclusivity()), Some(other_end.inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

/// Capacity to extend an interval with another
pub trait Extensible<Rhs = Self> {
    /// Output type
    type Output;

    /// Creates an extended interval from the current one and given one
    ///
    /// Instead of uniting two intervals, this method takes the lowest point of both intervals' lower bound and the
    /// highest point of both intervals' upper bound, then creates an interval that spans those two points.
    ///
    /// Regarding bound inclusivity, for each point we will get the bound inclusivity of the interval from which
    /// the point was taken. If they were equal, we choose the most inclusive bound.
    ///
    /// If both intervals are empty, the method just returns an empty interval.
    ///
    /// If one of the intervals is empty, the method just return a clone of the other non-empty interval.
    #[must_use]
    fn extend(&self, rhs: &Rhs) -> Self::Output;
}

impl<Rhs> Extensible<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        AbsoluteInterval::from(self.emptiable_abs_bounds().extend(&rhs.emptiable_abs_bounds()))
    }
}

/// Extends two [`AbsoluteBounds`]
#[must_use]
pub fn extend_abs_bounds(og_bounds: &AbsoluteBounds, other_bounds: &AbsoluteBounds) -> AbsoluteBounds {
    let new_start_bound = match (og_bounds.abs_start(), other_bounds.abs_start()) {
        (bound @ AbsoluteStartBound::InfinitePast, _) | (_, bound @ AbsoluteStartBound::InfinitePast) => bound,
        (og_bound @ AbsoluteStartBound::Finite(..), other_bound @ AbsoluteStartBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    let new_end_bound = match (og_bounds.abs_end(), other_bounds.abs_end()) {
        (bound @ AbsoluteEndBound::InfiniteFuture, _) | (_, bound @ AbsoluteEndBound::InfiniteFuture) => bound,
        (og_bound @ AbsoluteEndBound::Finite(..), other_bound @ AbsoluteEndBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    AbsoluteBounds::new(new_start_bound, new_end_bound)
}

/// Extends an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn extend_abs_bounds_with_emptiable_abs_bounds(
    og_bounds: &AbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> AbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    extend_abs_bounds(og_bounds, other_non_empty_bounds)
}

/// Extends two [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn extend_emptiable_abs_bounds(
    og_bounds: &EmptiableAbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> EmptiableAbsoluteBounds {
    match (og_bounds, other_bounds) {
        (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Empty) => EmptiableAbsoluteBounds::Empty,
        (EmptiableAbsoluteBounds::Empty, bound @ EmptiableAbsoluteBounds::Bound(..))
        | (bound @ EmptiableAbsoluteBounds::Bound(..), EmptiableAbsoluteBounds::Empty) => bound.clone(),
        (EmptiableAbsoluteBounds::Bound(og_bounds), EmptiableAbsoluteBounds::Bound(other_bounds)) => {
            EmptiableAbsoluteBounds::Bound(og_bounds.extend(other_bounds))
        },
    }
}

/// Capacity to abridge an interval with another, think of it as the inverse of [`Extensible`]
pub trait Abridgable<Rhs = Self> {
    /// Output type
    type Output;

    /// Creates an abridged interval from the current one and given one
    ///
    /// Instead of intersecting two intervals, this method takes the highest point of both intervals' lower bound
    /// and the lowest point of both intervals' upper bound, then create an interval that spans those two points.
    ///
    /// Regarding bound inclusivity, for each point we will get the bound inclusivity of the interval from which
    /// the point was taken. If they were equal, we choose the most exclusive bound.
    ///
    /// If the intervals don't strictly overlap, the method returns the interval that spans the gap between the two
    /// intervals. This sort of gap interval will have opposite bound inclusivities from the points it was created from.
    ///
    /// If both intervals are empty, the method just returns an empty interval.
    ///
    /// If one of the intervals is empty, the method just returns a clone of the other non-empty interval.
    #[must_use]
    fn abridge(&self, rhs: &Rhs) -> Self::Output;
}

impl<Rhs> Abridgable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::from(self.emptiable_abs_bounds().abridge(&rhs.emptiable_abs_bounds()))
    }
}

/// Abridges two [`AbsoluteBounds`]
#[must_use]
pub fn abridge_abs_bounds(og_bounds: &AbsoluteBounds, other_bounds: &AbsoluteBounds) -> AbsoluteBounds {
    let mut highest_start = match (og_bounds.abs_start(), other_bounds.abs_start()) {
        (AbsoluteStartBound::InfinitePast, bound @ AbsoluteStartBound::Finite(..))
        | (
            bound @ (AbsoluteStartBound::Finite(..) | AbsoluteStartBound::InfinitePast),
            AbsoluteStartBound::InfinitePast,
        ) => bound,
        (og_bound @ AbsoluteStartBound::Finite(..), other_bound @ AbsoluteStartBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    let mut lowest_end = match (og_bounds.abs_end(), other_bounds.abs_end()) {
        (AbsoluteEndBound::InfiniteFuture, bound @ AbsoluteEndBound::Finite(..))
        | (
            bound @ (AbsoluteEndBound::Finite(..) | AbsoluteEndBound::InfiniteFuture),
            AbsoluteEndBound::InfiniteFuture,
        ) => bound,
        (og_bound @ AbsoluteEndBound::Finite(..), other_bound @ AbsoluteEndBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    if highest_start > lowest_end {
        swap_absolute_bounds(&mut highest_start, &mut lowest_end);

        if let AbsoluteStartBound::Finite(ref mut finite_start) = highest_start {
            finite_start.set_inclusivity(finite_start.inclusivity().opposite());
        }

        if let AbsoluteEndBound::Finite(ref mut finite_end) = lowest_end {
            finite_end.set_inclusivity(finite_end.inclusivity().opposite());
        }
    }

    AbsoluteBounds::unchecked_new(highest_start, lowest_end)
}

/// Abridges an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn abridge_abs_bounds_with_emptiable_abs_bounds(
    og_bounds: &AbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> AbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    abridge_abs_bounds(og_bounds, other_non_empty_bounds)
}

/// Abridges two [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn abridge_emptiable_abs_bounds(
    og_bounds: &EmptiableAbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> EmptiableAbsoluteBounds {
    match (og_bounds, other_bounds) {
        (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Empty) => EmptiableAbsoluteBounds::Empty,
        (EmptiableAbsoluteBounds::Empty, bound @ EmptiableAbsoluteBounds::Bound(..))
        | (bound @ EmptiableAbsoluteBounds::Bound(..), EmptiableAbsoluteBounds::Empty) => bound.clone(),
        (EmptiableAbsoluteBounds::Bound(og_bounds), EmptiableAbsoluteBounds::Bound(other_bounds)) => {
            EmptiableAbsoluteBounds::Bound(og_bounds.abridge(other_bounds))
        },
    }
}

// TODO: Since both traits below are called to make a generic set difference, think of a way to prevent having
// to unnecessarily check for overlap position (`is_qualified` method? call both anyways?)
// Also think about how this is gonna be used for symmetric difference, would it work as expected?

/// Cut types, used by [`Cuttable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum CutType {
    /// Where the cut was made, both bound inclusivities will be inclusive
    #[default]
    InclusiveBoth,
    /// Where the cut was made, the future bound inclusivity will be exclusive, while the past one will be inclusive
    ExclusiveFuture,
    /// Where the cut was made, the past bound inclusivity will be exclusive, while the future one will be inclusive
    ExclusivePast,
    /// Where the cut was made, both bound inclusivities will be exclusive
    ExclusiveBoth,
}

impl CutType {
    /// Returns the bound inclusivity for the past side after the cut was made
    #[must_use]
    pub fn past_bound_inclusivity(&self) -> BoundInclusivity {
        match self {
            Self::InclusiveBoth | Self::ExclusiveFuture => BoundInclusivity::Inclusive,
            Self::ExclusivePast | Self::ExclusiveBoth => BoundInclusivity::Exclusive,
        }
    }

    /// Returns the bound inclusivity for the future side after the cut was made
    #[must_use]
    pub fn future_bound_inclusivity(&self) -> BoundInclusivity {
        match self {
            Self::InclusiveBoth | Self::ExclusivePast => BoundInclusivity::Inclusive,
            Self::ExclusiveBoth | Self::ExclusiveFuture => BoundInclusivity::Exclusive,
        }
    }
}

/// Result of a cut
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CutResult<T> {
    /// The cutting point was outside the given interval, or the cut itself was unsuccessful
    Uncut,
    /// The cut was successful, contains the cut two parts
    Cut(T, T),
}

impl<T> CutResult<T> {
    /// Whether the [`CutResult`] is of the [`Uncut`](CutResult::Uncut) variant
    pub fn is_uncut(&self) -> bool {
        matches!(self, CutResult::Uncut)
    }

    /// Whether the [`CutResult`] is of the [`Cut`](CutResult::Cut) variant
    pub fn is_cut(&self) -> bool {
        matches!(self, CutResult::Cut(..))
    }

    /// Maps the contents of the [`Cut`](CutResult::Cut) variant
    pub fn map_cut<F, U>(self, mut f: F) -> CutResult<U>
    where
        F: FnMut(T, T) -> (U, U),
    {
        match self {
            Self::Uncut => CutResult::Uncut,
            Self::Cut(c1, c2) => {
                let mapped_cut = (f)(c1, c2);
                CutResult::Cut(mapped_cut.0, mapped_cut.1)
            },
        }
    }
}

/// Capacity to cut at specific time(s)
///
/// If you are looking for removing a given interval from another, see [`TODO TODO TODO`]
pub trait Cuttable {
    /// Output type
    type Output;

    /// Cuts the interval
    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output>;
}

impl Cuttable for AbsoluteBounds {
    type Output = Self;

    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bounds(self, at, cut_type)
    }
}

impl Cuttable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bounds(self, at, cut_type)
    }
}

impl Cuttable for AbsoluteInterval {
    type Output = Self;

    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at, cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

/// Cuts an [`AbsoluteBounds`]
#[must_use]
pub fn cut_abs_bounds(bounds: &AbsoluteBounds, at: DateTime<Utc>, cut_type: CutType) -> CutResult<AbsoluteBounds> {
    if !bounds.simple_contains(at) {
        return CutResult::Uncut;
    }

    let mut past_split = bounds.clone();
    let mut future_split = bounds.clone();

    past_split.set_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    )));

    future_split.set_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    )));

    CutResult::Cut(past_split, future_split)
}

/// Cuts an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn cut_emptiable_abs_bounds(
    bounds: &EmptiableAbsoluteBounds,
    at: DateTime<Utc>,
    cut_type: CutType,
) -> CutResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(non_empty_bounds) = bounds else {
        // Empty bounds can't be cut
        return CutResult::Uncut;
    };

    cut_abs_bounds(non_empty_bounds, at, cut_type)
        .map_cut(|c1, c2| (EmptiableAbsoluteBounds::from(c1), EmptiableAbsoluteBounds::from(c2)))
}

/// Capacity to grow an interval up to a given bound
pub trait Growable {
    /// Output type
    type Output;

    /// Grows the start of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the start bound is more in the past than the original one.
    /// Of course, it only happens if the passed new start bound is actually more in the past than the original one.
    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output;

    /// Grows the end of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the end bound is more in the future than the original one.
    /// Of course, it only happens if the passed new end bound is actually more in the future than the original one.
    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output;
}

impl Growable for AbsoluteBounds {
    type Output = Self;

    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output {
        grow_start_abs_bounds(self, at)
    }

    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output {
        grow_end_abs_bounds(self, at)
    }
}

impl Growable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output {
        grow_start_emptiable_abs_bounds(self, at)
    }

    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output {
        grow_end_emptiable_abs_bounds(self, at)
    }
}

impl Growable for AbsoluteInterval {
    type Output = Self;

    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(grow_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }

    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(grow_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }
}

/// Makes the start of the passed [`AbsoluteBounds`] grow up to the given bound if it is lesser than the original
#[must_use]
pub fn grow_start_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteStartBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.abs_start().min(at));
    new_bounds
}

/// Makes the end of the passed [`AbsoluteBounds`] grow up to the given bound if it is greater than the original
#[must_use]
pub fn grow_end_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteEndBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.abs_end().max(at));
    new_bounds
}

/// Makes the start of the passed [`EmptiableAbsoluteBounds`] grow up to the given bound if it is lesser than the original
#[must_use]
pub fn grow_start_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteStartBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(grow_start_abs_bounds(bounds, at))
}

/// Makes the end of the passed [`EmptiableAbsoluteBounds`] grow up to the given bound if it is greater than the original
#[must_use]
pub fn grow_end_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteEndBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(grow_end_abs_bounds(bounds, at))
}

/// Capacity to shrink an interval up to a given time
pub trait Shrinkable {
    /// Output type
    type Output;

    /// Shrinks the start bound up to the given time
    ///
    /// If the given bound is already after the interval's end,
    /// nothing happens and it just returns a clone of the interval
    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output;

    /// Shrinks the end bound up to the given time
    ///
    /// If the given bound is already before the interval's start,
    /// nothing happens and it just returns a clone of the interval
    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output;
}

impl Shrinkable for AbsoluteBounds {
    type Output = Self;

    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output {
        shrink_start_abs_bounds(self, at)
    }

    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output {
        shrink_end_abs_bounds(self, at)
    }
}

impl Shrinkable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output {
        shrink_start_emptiable_abs_bounds(self, at)
    }

    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output {
        shrink_end_emptiable_abs_bounds(self, at)
    }
}

impl Shrinkable for AbsoluteInterval {
    type Output = Self;

    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }

    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }
}

/// Shrinks the start bound of the given [`AbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_start_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteStartBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    let max_start = new_bounds.abs_start().max(at);

    match max_start.partial_cmp(&new_bounds.abs_end()) {
        // Would create an invalid interval, so we just return a clone of the original bounds
        None | Some(Ordering::Greater) => {},
        Some(Ordering::Equal | Ordering::Less) => {
            new_bounds.set_start(max_start);
        },
    }

    new_bounds
}

/// Shrinks the end bound of the given [`AbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_end_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteEndBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    let min_end = new_bounds.abs_end().min(at);

    match new_bounds.abs_start().partial_cmp(&min_end) {
        // Would create an invalid interval, so we just return a clone of the original bounds
        None | Some(Ordering::Greater) => {},
        Some(Ordering::Equal | Ordering::Less) => {
            new_bounds.set_end(min_end);
        },
    }

    new_bounds
}

/// Shrinks the start bound of the given [`EmptiableAbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_start_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteStartBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(shrink_start_abs_bounds(bounds, at))
}

/// Shrinks the end bound of the given [`EmptiableAbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_end_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteEndBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(shrink_end_abs_bounds(bounds, at))
}

/// Result of an overlap/gap removal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapOrGapRemovalResult<T> {
    /// The operation was successful and resulted into a single element (an empty interval counts as one too)
    Single(T),
    /// The operation was successful and resulted into two split elements
    Split(T, T),
}

impl<T> OverlapOrGapRemovalResult<T> {
    /// Whether the [`OverlapOrGapRemovalResult`] is of the [`Single`](OverlapOrGapRemovalResult::Single) variant
    #[must_use]
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Whether the [`OverlapOrGapRemovalResult`] is of the [`Split`](OverlapOrGapRemovalResult::Split) variant
    #[must_use]
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Maps the contents of the [`Single`](OverlapOrGapRemovalResult::Single)
    /// and [`Split`](OverlapOrGapRemovalResult::Split) variants
    ///
    /// Uses a closure that describes the transformation from `T` to `U`, used for each element in the enum.
    #[must_use]
    pub fn map<F, U>(self, mut f: F) -> OverlapOrGapRemovalResult<U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Self::Single(s) => OverlapOrGapRemovalResult::Single((f)(s)),
            Self::Split(s1, s2) => OverlapOrGapRemovalResult::Split((f)(s1), (f)(s2)),
        }
    }
}

/// Capacity to remove any overlap or gap between two intervals
pub trait RemovableOverlapOrGap<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns a result that contains a version (or multiple versions, if split) of `self` without overlap or gap
    #[must_use]
    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output>;
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = EmptiableAbsoluteBounds;

    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds(), rule_set)
            .map(AbsoluteInterval::from)
    }
}

/// Removes any overlap or gap between two [`AbsoluteBounds`]
#[must_use]
pub fn remove_overlap_or_gap_abs_bounds(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, rule_set);

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OutsideBefore`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.grow_end(new_end_bound)))
        },
        Dop::OutsideAfter => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OutsideAfter`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.grow_start(new_start_bound)))
        },
        Dop::OnStart | Dop::OnEnd => {
            // No gaps nor overlaps already
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.clone()))
        },
        Dop::CrossesStart => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `CrossesStart`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.shrink_end(new_end_bound)))
        },
        Dop::CrossesEnd => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `CrossesEnd`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.shrink_start(new_start_bound)))
        },
        Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd | Dop::Equal => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty)
        },
        Dop::ContainsAndSameStart => OverlapOrGapRemovalResult::Single(remove_overlap_or_gap_cut_end(a, b)),
        Dop::ContainsAndSameEnd => OverlapOrGapRemovalResult::Single(remove_overlap_or_gap_cut_start(a, b)),
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            remove_overlap_or_gap_cut_start(a, b),
            remove_overlap_or_gap_cut_end(a, b),
        ),
    }
}

fn remove_overlap_or_gap_cut_start(a: &AbsoluteBounds, b: &AbsoluteBounds) -> EmptiableAbsoluteBounds {
    let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
        unreachable!(
            "If the start of the compared bounds is `InfiniteStart`, \
            then it is impossible that the overlap was `ContainsAndSameEnd`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::InclusiveBoth,
        BoundInclusivity::Exclusive => CutType::ExclusiveBoth,
    };

    match a.cut_at(finite_bound.time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` start at the same time as `b` does, but b is exclusive on this point whereas
            // `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsoluteFiniteBound::new(finite_bound.time());

            EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::from(point),
                AbsoluteEndBound::from(point),
            ))
        },
        CutResult::Cut(new_a, _) => EmptiableAbsoluteBounds::from(new_a),
    }
}

fn remove_overlap_or_gap_cut_end(a: &AbsoluteBounds, b: &AbsoluteBounds) -> EmptiableAbsoluteBounds {
    let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
        unreachable!(
            "If the end of the compared bounds is `InfiniteFuture`, \
            then it is impossible that the overlap was `ContainsAndSameStart`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::InclusiveBoth,
        BoundInclusivity::Exclusive => CutType::ExclusiveBoth,
    };

    match a.cut_at(finite_bound.time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` ends at the same time as `b` does, but b is exclusive on this point whereas
            // `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsoluteFiniteBound::new(finite_bound.time());

            EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::from(point),
                AbsoluteEndBound::from(point),
            ))
        },
        CutResult::Cut(_, new_a) => EmptiableAbsoluteBounds::from(new_a),
    }
}

/// Removes any overlap or gap between an [`AbsoluteBounds`] and an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(b_abs_bounds) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.clone()));
    };

    remove_overlap_or_gap_abs_bounds(a, b_abs_bounds, rule_set)
}

/// Removes any overlap or gap between two [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn remove_overlap_or_gap_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    if let (EmptiableAbsoluteBounds::Bound(a_abs_bounds), EmptiableAbsoluteBounds::Bound(b_abs_bounds)) = (a, b) {
        return remove_overlap_or_gap_abs_bounds(a_abs_bounds, b_abs_bounds, rule_set);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

/// Errors that can be produced when using [`GapFillable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GapFillError {
    Overlap,
}

/// Capacity to fill the gap between two intervals if they don't strictly overlap
pub trait GapFillable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns a result that contains a version of `self` that no longer has a strict gap with the given `rhs`
    ///
    /// # Errors
    ///
    /// If the two intervals are not overlapping, it should result in [`GapFillError::Overlap`].
    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError>;
}

impl<Rhs> GapFillable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
#[must_use]
pub fn fill_gap_abs_bounds(a: &AbsoluteBounds, b: &AbsoluteBounds) -> Result<AbsoluteBounds, GapFillError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OutsideBefore`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            Ok(a.grow_end(new_end_bound))
        },
        Dop::OutsideAfter => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OutsideAfter`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            Ok(a.grow_start(new_start_bound))
        },
        _ => Err(GapFillError::Overlap),
    }
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
#[must_use]
pub fn fill_gap_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<AbsoluteBounds, GapFillError> {
    let EmptiableAbsoluteBounds::Bound(b_abs_bounds) = b else {
        return Ok(a.clone());
    };

    fill_gap_abs_bounds(a, b_abs_bounds)
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
#[must_use]
pub fn fill_gap_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<EmptiableAbsoluteBounds, GapFillError> {
    let EmptiableAbsoluteBounds::Bound(a_abs_bounds) = a else {
        return Ok(a.clone());
    };

    fill_gap_abs_bounds_with_emptiable_abs_bounds(a_abs_bounds, b).map(EmptiableAbsoluteBounds::from)
}

/// Result of an overlap removal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapRemovalResult<T> {
    Single(T),
    Split(T, T),
    NoOverlap,
}

/// Capacity to remove overlap between two intervals that strictly overlap
pub trait OverlapRemovable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns a result that contains a version of `self` that no longer has a strict overlap with the given `rhs`
    #[must_use]
    fn remove_overlap() -> OverlapRemovalResult<Self::Output>;
}

// TODO: Change interval iters so that they use the following traits

/// Capacity to unite an interval with another
pub trait Unitable<Rhs = Self> {
    /// Output type
    type Output;

    /// Unites two intervals using the given rules
    #[must_use]
    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    /// Unites two intervals using default overlap rules
    #[must_use]
    fn simple_unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        self.unite(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Unites two intervals using the given closure
    #[must_use]
    fn unite_with<F>(&self, rhs: &Rhs, mut f: F) -> UnionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> UnionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        unite_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        unite_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        unite_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &rhs.emptiable_abs_bounds(),
            rule_set,
            rules,
        )
        .map_united(AbsoluteInterval::from)
    }
}

/// Unites two [`AbsoluteBounds`] using the given rules
pub fn unite_abs_bounds<'a, RI>(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> UnionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableAbsoluteBounds`] using the given rules
pub fn unite_emptiable_abs_bounds<'a, RI>(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> UnionResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`] using the given rules
pub fn unite_abs_bounds_with_emptiable_abs_bounds<'a, RI>(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> UnionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Capacity to unite an interval with another
pub trait Intersectable<Rhs = Self> {
    /// Output type
    type Output;

    /// Intersects two intervals using the given rules
    #[must_use]
    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    /// Intersects two intervals using default overlap rules
    #[must_use]
    fn simple_intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        self.intersect(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Intersects two intervals using the given closure
    #[must_use]
    fn intersect_with<F>(&self, rhs: &Rhs, mut f: F) -> IntersectionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> IntersectionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        intersect_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        intersect_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        intersect_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &rhs.emptiable_abs_bounds(),
            rule_set,
            rules,
        )
        .map_intersected(AbsoluteInterval::from)
    }
}

/// Intersects two [`AbsoluteBounds`] using the given rules
pub fn intersect_abs_bounds<'ri, RI>(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> IntersectionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects two [`EmptiableAbsoluteBounds`] using the given rules
pub fn intersect_emptiable_abs_bounds<'ri, RI>(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> IntersectionResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`] using the given rules
pub fn intersect_abs_bounds_with_emptiable_abs_bounds<'ri, RI>(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> IntersectionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Capacity to differentiate an interval with another (as in set difference)
pub trait Differentiable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns the set difference of `self` with `other` using the given rules
    ///
    /// The caller, self, is the one that is differentiated by the given other: same operand order as the mathematical
    /// expression for a set difference.
    #[must_use]
    fn differentiate<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> DifferenceResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    /// Returns the set difference of `self` with `other` using default overlap rules
    #[must_use]
    fn simple_differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        self.differentiate(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns the set difference of `self` with `other` using the given closure
    #[must_use]
    fn differentiate_with<F>(&self, rhs: &Rhs, mut f: F) -> DifferenceResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> DifferenceResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

/// Differentiates an [`AbsoluteBounds`] with another one
#[must_use]
pub fn differentiate_abs_bounds<'ri, RI>(
    og_bounds: &AbsoluteBounds,
    other_bounds: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Differentiates an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn differentiate_abs_bounds_with_emptiable_bounds<'ri, RI>(
    og_bounds: &AbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Differentiates an [`EmptiableAbsoluteBounds`] with another one
#[must_use]
pub fn differentiate_emptiable_abs_bounds<'ri, RI>(
    og_bounds: &EmptiableAbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Capacity to symmetrically differentiate (a.k.a. XOR) an interval with another
pub trait SymmetricallyDifferentiable<Rhs = Self>: Differentiable<Rhs, Output = Self::DiffSelfWithRhs> + Sized
where
    Rhs: Differentiable<Self, Output = Self::DiffRhsWithSelf>,
{
    /// Difference of Self with Rhs
    type DiffSelfWithRhs;

    /// Difference of Rhs with Self
    type DiffRhsWithSelf;

    /// Returns the symmetrical difference between two sets of bounds using the given rules
    ///
    /// Simply uses the [`Differentiable`] trait on both Self with Rhs, and Rhs with Self.
    #[must_use]
    fn symmetrically_differentiate<'ri, RI>(
        &self,
        rhs: &Rhs,
        rule_set: OverlapRuleSet,
        rules: RI,
    ) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs>
    // FIX
    where
        RI: IntoIterator<Item = &'ri OverlapRule> + Clone,
    {
        todo!()
        // let diff_self_with_rhs = self.differentiate(rhs, rule_set, rules.clone());
        // let diff_rhs_with_self = rhs.differentiate(self, rule_set, rules.clone());

        // match (diff_self_with_rhs, diff_rhs_with_self) {
        //     (DifferenceResult::Difference(diff_self_with_rhs), DifferenceResult::Difference(diff_rhs_with_self)) => {
        //         SymmetricDifferenceResult::SymmetricDifference(diff_self_with_rhs, diff_rhs_with_self)
        //     },
        //     _ => SymmetricDifferenceResult::Separate,
        // }
    }

    /// Returns the symmetrical difference between two sets of bounds using default overlap rules
    #[must_use]
    fn simple_symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs> /* FIX */
    {
        self.symmetrically_differentiate(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns the symmetrical difference between two sets of bounds using the given closure
    #[must_use]
    fn symmetrically_differentiate_with<F>(
        &self,
        rhs: &Rhs,
        mut f: F,
    ) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs>
    // FIX
    where
        F: FnMut(&Self, &Rhs) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs>, // FIX
    {
        (f)(self, rhs)
    }
}

/// Symmetrically differentiates two [`AbsoluteBounds`] using the given rules
pub fn symmetrically_differentiate_abs_bounds<'ri, RI>(
    a: AbsoluteBounds,
    b: AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> SymmetricDifferenceResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Symmetrically differentiates two [`EmptiableAbsoluteBounds`] using the given rules
pub fn symmetrically_differentiate_emptiable_abs_bounds<'ri, RI>(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Symmetrically differentiates two [`AbsoluteInterval`]s using the given rules
pub fn symmetrically_differentiate_abs_intervals<'ri, RI>(
    a: &AbsoluteInterval,
    b: &AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> SymmetricDifferenceResult<AbsoluteInterval>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

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

use crate::intervals::ClosedAbsoluteInterval;
use crate::intervals::interval::{
    AbsoluteFiniteBound, EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval, HasEmptiableAbsoluteBounds, OpenInterval,
    swap_absolute_bounds,
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
    pub fn to_simple(self) -> SimpleTimeContainmentPosition {
        match self {
            Self::OutsideBefore => SimpleTimeContainmentPosition::OutsideBefore,
            Self::OutsideAfter => SimpleTimeContainmentPosition::OutsideAfter,
            Self::Outside => SimpleTimeContainmentPosition::Outside,
            Self::OnStart(_) => SimpleTimeContainmentPosition::OnStart,
            Self::OnEnd(_) => SimpleTimeContainmentPosition::OnEnd,
            Self::Inside => SimpleTimeContainmentPosition::Inside,
        }
    }

    /// Uses a rule set to transform the containment position into a simple but opinionated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple_using_rule_set(self, rule_set: TimeContainmentRuleSet) -> SimpleTimeContainmentPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`TimeContainmentPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimpleTimeContainmentPosition {
    /// See [`ContainmentPosition::OutsideBefore`]
    OutsideBefore,
    /// See [`ContainmentPosition::OutsideAfter`]
    OutsideAfter,
    /// See [`ContainmentPosition::Outside`]
    Outside,
    /// See [`ContainmentPosition::OnStart`]
    OnStart,
    /// See [`ContainmentPosition::OnEnd`]
    OnEnd,
    /// See [`ContainmentPosition::Inside`]
    Inside,
}

/// Different rule sets for determining whether different [`TimeContainmentPosition`]s are considered as containing or not.
///
/// See [`CanPositionTimeContainment::contains`] for more.
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
    pub fn disambiguate(&self, containment_position: TimeContainmentPosition) -> SimpleTimeContainmentPosition {
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
) -> SimpleTimeContainmentPosition {
    match containment_position {
        TimeContainmentPosition::OutsideBefore | TimeContainmentPosition::OnStart(BoundInclusivity::Exclusive) => {
            SimpleTimeContainmentPosition::OutsideBefore
        },
        TimeContainmentPosition::OutsideAfter | TimeContainmentPosition::OnEnd(BoundInclusivity::Exclusive) => {
            SimpleTimeContainmentPosition::OutsideAfter
        },
        TimeContainmentPosition::Outside => SimpleTimeContainmentPosition::Outside,
        TimeContainmentPosition::OnStart(BoundInclusivity::Inclusive) => SimpleTimeContainmentPosition::OnStart,
        TimeContainmentPosition::OnEnd(BoundInclusivity::Inclusive) => SimpleTimeContainmentPosition::OnEnd,
        TimeContainmentPosition::Inside => SimpleTimeContainmentPosition::Inside,
    }
}

/// Disambiguates a [`TimeContainmentPosition`] using [the lenient rule set](TimeContainmentRuleSet::Lenient)
#[must_use]
pub fn lenient_containment_rule_set_disambiguation(
    containment_position: TimeContainmentPosition,
) -> SimpleTimeContainmentPosition {
    match containment_position {
        TimeContainmentPosition::OutsideBefore => SimpleTimeContainmentPosition::OutsideBefore,
        TimeContainmentPosition::OutsideAfter => SimpleTimeContainmentPosition::OutsideAfter,
        TimeContainmentPosition::Outside => SimpleTimeContainmentPosition::Outside,
        TimeContainmentPosition::OnStart(_) => SimpleTimeContainmentPosition::OnStart,
        TimeContainmentPosition::OnEnd(_) => SimpleTimeContainmentPosition::OnEnd,
        TimeContainmentPosition::Inside => SimpleTimeContainmentPosition::Inside,
    }
}

/// Time containment rules used as the reference for the predefined decisions
pub const DEFAULT_TIME_CONTAINMENT_RULES: [TimeContainmentRule; 0] = [];

/// All rules for containment by converting a [`SimpleTimeContainmentPosition`] into a [`bool`]
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
    pub fn counts_as_contained(&self, simple_containment_position: SimpleTimeContainmentPosition) -> bool {
        match self {
            Self::DenyOnStart => deny_on_start_containment_rule_counts_as_contained(simple_containment_position),
            Self::DenyOnEnd => deny_on_end_containment_rule_counts_as_contained(simple_containment_position),
            Self::DenyOnBounds => deny_on_bounds_containment_rule_counts_as_contained(simple_containment_position),
        }
    }
}

/// Checks whether the given [`SimpleTimeContainmentPosition`] respects [the 'deny on start' rule](TimeContainmentRule::DenyOnStart)
#[must_use]
pub fn deny_on_start_containment_rule_counts_as_contained(
    simple_containment_position: SimpleTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        SimpleTimeContainmentPosition::OutsideBefore
            | SimpleTimeContainmentPosition::OutsideAfter
            | SimpleTimeContainmentPosition::Outside
            | SimpleTimeContainmentPosition::OnStart
    )
}

/// Checks whether the given [`SimpleTimeContainmentPosition`] respects [the 'deny on end' rule](TimeContainmentRule::DenyOnEnd)
#[must_use]
pub fn deny_on_end_containment_rule_counts_as_contained(
    simple_containment_position: SimpleTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        SimpleTimeContainmentPosition::OutsideBefore
            | SimpleTimeContainmentPosition::OutsideAfter
            | SimpleTimeContainmentPosition::Outside
            | SimpleTimeContainmentPosition::OnEnd
    )
}

/// Checks whether the given [`SimpleTimeContainmentPosition`] respects [the 'deny on bounds' rule](TimeContainmentRule::DenyOnBounds)
#[must_use]
pub fn deny_on_bounds_containment_rule_counts_as_contained(
    simple_containment_position: SimpleTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        SimpleTimeContainmentPosition::OutsideBefore
            | SimpleTimeContainmentPosition::OutsideAfter
            | SimpleTimeContainmentPosition::Outside
            | SimpleTimeContainmentPosition::OnStart
            | SimpleTimeContainmentPosition::OnEnd
    )
}

/// Where the current time interval was found relative to the other time interval
///
/// See [`CanPositionOverlap::overlap_position`] for more information
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
    /// See [`Interval::overlap_position`] for more details.
    OnStart(BoundInclusivity, BoundInclusivity),
    /// The current time interval was found starting on the end of the given other time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// See [`Interval::overlap_position`] for more details.
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
    /// See [`Interval::overlap_position`] for more details.
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
    /// See [`Interval::overlap_position`] for more details.
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
    /// See [`Interval::overlap_position`] for more details.
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
    /// See [`Interval::overlap_position`] for more details.
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
    /// See [`Interval::overlap_position`] for more details.
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
    pub fn to_simple(self) -> SimpleOverlapPosition {
        match self {
            OverlapPosition::OutsideBefore => SimpleOverlapPosition::OutsideBefore,
            OverlapPosition::OutsideAfter => SimpleOverlapPosition::OutsideAfter,
            OverlapPosition::Outside => SimpleOverlapPosition::Outside,
            OverlapPosition::OnStart(..) => SimpleOverlapPosition::OnStart,
            OverlapPosition::OnEnd(..) => SimpleOverlapPosition::OnEnd,
            OverlapPosition::CrossesStart => SimpleOverlapPosition::CrossesStart,
            OverlapPosition::CrossesEnd => SimpleOverlapPosition::CrossesEnd,
            OverlapPosition::Inside => SimpleOverlapPosition::Inside,
            OverlapPosition::InsideAndSameStart(..) => SimpleOverlapPosition::InsideAndSameStart,
            OverlapPosition::InsideAndSameEnd(..) => SimpleOverlapPosition::InsideAndSameEnd,
            OverlapPosition::Equal(..) => SimpleOverlapPosition::Equal,
            OverlapPosition::ContainsAndSameStart(..) => SimpleOverlapPosition::ContainsAndSameStart,
            OverlapPosition::ContainsAndSameEnd(..) => SimpleOverlapPosition::ContainsAndSameEnd,
            OverlapPosition::Contains => SimpleOverlapPosition::Contains,
        }
    }

    /// Uses a rule set to transform the overlap position into a simple but opinionated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple_using_rule_set(self, rule_set: OverlapRuleSet) -> SimpleOverlapPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`OverlapPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimpleOverlapPosition {
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
    pub fn disambiguate(&self, overlap_position: OverlapPosition) -> SimpleOverlapPosition {
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
pub fn strict_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::Outside => SimpleOP::Outside,
        OP::OnStart(BI::Inclusive, BI::Inclusive) => SimpleOP::OnStart,
        OP::OnStart(..) | OP::OutsideBefore => SimpleOP::OutsideBefore,
        OP::OnEnd(BI::Inclusive, BI::Inclusive) => SimpleOP::OnEnd,
        OP::OnEnd(..) | OP::OutsideAfter => SimpleOP::OutsideAfter,
        OP::CrossesStart
        | OP::InsideAndSameStart(Some(BI::Exclusive), Some(BI::Inclusive))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Inclusive)), (Some(BI::Inclusive), Some(BI::Exclusive)))
        | OP::ContainsAndSameEnd(Some(BI::Inclusive), Some(BI::Exclusive)) => SimpleOP::CrossesStart,
        OP::CrossesEnd
        | OP::Equal((Some(BI::Inclusive), Some(BI::Exclusive)), (Some(BI::Exclusive), Some(BI::Inclusive)))
        | OP::ContainsAndSameStart(Some(BI::Inclusive), Some(BI::Exclusive)) => SimpleOP::CrossesEnd,
        OP::Inside
        | OP::InsideAndSameStart(Some(BI::Inclusive), Some(BI::Exclusive))
        | OP::Equal((Some(BI::Inclusive), Some(BI::Inclusive)), (Some(BI::Exclusive), Some(BI::Exclusive))) => {
            SimpleOP::Inside
        },
        OP::InsideAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::InsideAndSameStart,
        OP::InsideAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::InsideAndSameEnd,
        OP::Equal((incl_ref_from, incl_ref_to), (incl_comp_from, incl_comp_to))
            if incl_ref_from == incl_comp_from && incl_ref_to == incl_comp_to =>
        {
            SimpleOP::Equal
        },
        OP::Equal((Some(BI::Inclusive), Some(BI::Inclusive)), (Some(BI::Inclusive), Some(BI::Exclusive)))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Inclusive)), (Some(BI::Exclusive), Some(BI::Exclusive))) => {
            SimpleOP::InsideAndSameStart
        },
        OP::Equal((Some(BI::Inclusive), Some(BI::Inclusive)), (Some(BI::Exclusive), Some(BI::Inclusive)))
        | OP::Equal((Some(BI::Inclusive), Some(BI::Exclusive)), (Some(BI::Exclusive), Some(BI::Exclusive))) => {
            SimpleOP::InsideAndSameEnd
        },
        OP::Equal((Some(BI::Inclusive), Some(BI::Exclusive)), (Some(BI::Inclusive), Some(BI::Inclusive)))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Exclusive)), (Some(BI::Exclusive), Some(BI::Inclusive))) => {
            SimpleOP::ContainsAndSameStart
        },
        OP::Equal((Some(BI::Exclusive), Some(BI::Inclusive)), (Some(BI::Inclusive), Some(BI::Inclusive)))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Exclusive)), (Some(BI::Inclusive), Some(BI::Exclusive))) => {
            SimpleOP::ContainsAndSameEnd
        },
        OP::Equal((Some(BI::Exclusive), Some(BI::Exclusive)), (Some(BI::Inclusive), Some(BI::Inclusive)))
        | OP::ContainsAndSameStart(Some(BI::Exclusive), Some(BI::Inclusive))
        | OP::ContainsAndSameEnd(Some(BI::Exclusive), Some(BI::Inclusive))
        | OP::Contains => SimpleOP::Contains,
        OP::ContainsAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::ContainsAndSameStart,
        OP::ContainsAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::ContainsAndSameEnd,
        OP::InsideAndSameStart(None, Some(_)) | OP::InsideAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        OP::InsideAndSameEnd(None, Some(_)) | OP::InsideAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        OP::ContainsAndSameStart(None, Some(_)) | OP::ContainsAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        OP::ContainsAndSameEnd(None, Some(_)) | OP::ContainsAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        OP::InsideAndSameStart(..)
        | OP::InsideAndSameEnd(..)
        | OP::Equal(..)
        | OP::ContainsAndSameStart(..)
        | OP::ContainsAndSameEnd(..) => unreachable!("Already handled dynamically"),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the 'continuous to future' rule set](OverlapRuleSet::ContinuousToFuture)
#[must_use]
pub fn continuous_to_future_overlap_rule_set_disambiguation(
    overlap_position: OverlapPosition,
) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::OnStart(BI::Inclusive, _) => SimpleOP::OnStart,
        OP::OnStart(..) => SimpleOP::OutsideBefore,
        OP::OnEnd(_, BI::Inclusive) => SimpleOP::OnEnd,
        OP::OnEnd(..) => SimpleOP::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the 'continuous to past' rule set](OverlapRuleSet::ContinuousToPast)
#[must_use]
pub fn continuous_to_past_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::OnStart(_, BI::Inclusive) => SimpleOP::OnStart,
        OP::OnStart(..) => SimpleOP::OutsideBefore,
        OP::OnEnd(BI::Inclusive, _) => SimpleOP::OnEnd,
        OP::OnEnd(..) => SimpleOP::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the lenient rule set](OverlapRuleSet::Lenient)
#[must_use]
pub fn lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::OutsideBefore | OP::OnStart(BI::Exclusive, BI::Exclusive) => SimpleOP::OutsideBefore,
        OP::OutsideAfter | OP::OnEnd(BI::Exclusive, BI::Exclusive) => SimpleOP::OutsideAfter,
        OP::Outside => SimpleOP::Outside,
        OP::OnStart(..) => SimpleOP::OnStart,
        OP::OnEnd(..) => SimpleOP::OnEnd,
        OP::CrossesStart => SimpleOP::CrossesStart,
        OP::CrossesEnd => SimpleOP::CrossesEnd,
        OP::Inside => SimpleOP::Inside,
        OP::InsideAndSameStart(..) => SimpleOP::InsideAndSameStart,
        OP::InsideAndSameEnd(..) => SimpleOP::InsideAndSameEnd,
        OP::Equal(..) => SimpleOP::Equal,
        OP::Contains => SimpleOP::Contains,
        OP::ContainsAndSameStart(..) => SimpleOP::ContainsAndSameStart,
        OP::ContainsAndSameEnd(..) => SimpleOP::ContainsAndSameEnd,
    }
}

/// Disambiguates an [`OverlapPosition`] using [the very lenient rule set](OverlapRuleSet::VeryLenient)
#[must_use]
pub fn very_lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    overlap_position.to_simple()
}

/// Default overlap rules
pub const DEFAULT_OVERLAP_RULES: [OverlapRule; 1] = [OverlapRule::DenyAdjacency];

/// All rules for overlapping by converting a [`SimpleOverlapPosition`] into a [`bool`]
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
    /// Returns whether the given [`SimpleOverlapPosition`] counts as overlap
    #[must_use]
    pub fn counts_as_overlap(&self, simple_overlap_position: SimpleOverlapPosition) -> bool {
        match self {
            Self::AllowAdjacency => allow_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position),
            Self::DenyAdjacency => deny_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position),
            Self::AllowPastAdjacency | Self::DenyFutureAdjacency => {
                allow_past_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position)
            },
            Self::AllowFutureAdjacency | Self::DenyPastAdjacency => {
                allow_future_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position)
            },
        }
    }
}

/// Checks whether the given [`SimpleOverlapPosition`] respects [the 'allow adjacency' rule](OverlapRule::AllowAdjacency)
#[must_use]
pub fn allow_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore | SimpleOverlapPosition::OutsideAfter | SimpleOverlapPosition::Outside
    )
}

/// Checks whether the given [`SimpleOverlapPosition`] respects [the 'deny adjacency' rule](OverlapRule::DenyAdjacency)
#[must_use]
pub fn deny_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore
            | SimpleOverlapPosition::OutsideAfter
            | SimpleOverlapPosition::Outside
            | SimpleOverlapPosition::OnStart
            | SimpleOverlapPosition::OnEnd
    )
}

/// Checks whether the given [`SimpleOverlapPosition`] respects [the 'allow past adjacency' rule](OverlapRule::AllowPastAdjacency)
#[must_use]
pub fn allow_past_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore
            | SimpleOverlapPosition::OutsideAfter
            | SimpleOverlapPosition::Outside
            | SimpleOverlapPosition::OnEnd
    )
}

/// Checks whether the given [`SimpleOverlapPosition`] respects [the 'allow future adjacency' rule](OverlapRule::AllowFutureAdjacency)
#[must_use]
pub fn allow_future_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore
            | SimpleOverlapPosition::OutsideAfter
            | SimpleOverlapPosition::Outside
            | SimpleOverlapPosition::OnStart
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

    /// Returns the simple containment position of the given time using a given [containment rule set](TimeContainmentRuleSet)
    ///
    /// See [`CanPositionTimeContainment::time_containment_position`] for more details about containment position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionTimeContainment::Error).
    fn simple_time_containment_position(
        &self,
        time: DateTime<Utc>,
        rule_set: TimeContainmentRuleSet,
    ) -> Result<SimpleTimeContainmentPosition, Self::Error> {
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
    /// If you are looking to choose the rule set and the rules, see [`CanPositionTimeContainment::contains`].
    ///
    /// If you want even more granular control, see [`CanPositionTimeContainment::contains_using_simple`].
    #[must_use]
    fn simple_contains(&self, time: DateTime<Utc>) -> bool {
        self.contains(time, TimeContainmentRuleSet::default(), &DEFAULT_TIME_CONTAINMENT_RULES)
    }

    /// Returns whether the given time is contained in the interval using the given [containment rules](`TimeContainmentRule`)
    ///
    /// This method uses [`CanPositionTimeContainment::simple_time_containment_position`].
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the [`TimeContainmentRule`]s are checked. This method returns true only if all provided
    /// [`TimeContainmentRule`]s are respected (i.e. returned true when calling [`TimeContainmentRule::counts_as_contained`]).
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for containment, see [`CanPositionTimeContainment::simple_contains`].
    ///
    /// If you are looking for more control over what counts as contained, see [`CanPositionTimeContainment::contains_using_simple`].
    ///
    /// If you want extremely granular control over what counts as contained, see [`CanPositionTimeContainment::contains_using`].
    #[must_use]
    fn contains<'a, RI>(&self, time: DateTime<Utc>, rule_set: TimeContainmentRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a TimeContainmentRule>,
    {
        self.simple_time_containment_position(time, rule_set)
            .map(|simple_containment_position| {
                rules
                    .into_iter()
                    .all(|rule| rule.counts_as_contained(simple_containment_position))
            })
            .unwrap_or(false)
    }

    /// Returns whether the given time is contained in the interval using a custom function
    ///
    /// This method uses [`CanPositionTimeContainment::time_containment_position`].
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`TimeContainmentPosition`]
    /// given by [`CanPositionTimeContainment::time_containment_position`] counts as the passed time being contained
    /// in the interval.
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as containment but still want
    /// predetermined [`SimpleTimeContainmentPosition`]s, see [`CanPositionTimeContainment::contains_using_simple`].
    ///
    /// If you are looking for predetermined decisions on what's considered as contained, see [`CanPositionTimeContainment::contains`].
    #[must_use]
    fn contains_using<F>(&self, time: DateTime<Utc>, f: F) -> bool
    where
        F: FnOnce(TimeContainmentPosition) -> bool,
    {
        self.time_containment_position(time).map(f).unwrap_or(false)
    }

    /// Returns whether the given time is contained in the interval using a custom function
    ///
    /// This method uses [`CanPositionTimeContainment::simple_time_containment_position`].
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`SimpleTimeContainmentPosition`]
    /// given by [`CanPositionTimeContainment::simple_time_containment_position`] counts as contained or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as contained, see [`CanPositionTimeContainment::contains_using`].
    ///
    /// If you are looking for predetermined decisions on what's considered as contained, see [`CanPositionTimeContainment::simple_contains`].
    #[must_use]
    fn contains_using_simple<F>(&self, time: DateTime<Utc>, rule_set: TimeContainmentRuleSet, f: F) -> bool
    where
        F: FnOnce(SimpleTimeContainmentPosition) -> bool,
    {
        self.simple_time_containment_position(time, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

impl CanPositionTimeContainment for AbsoluteBounds {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(time_containment_position_abs_bounds(self, time))
    }
}

impl CanPositionTimeContainment for EmptiableAbsoluteBounds {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        let EmptiableAbsoluteBounds::Bound(bounds) = self else {
            return Ok(TimeContainmentPosition::Outside);
        };

        Ok(time_containment_position_abs_bounds(bounds, time))
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

impl CanPositionTimeContainment for AbsoluteInterval {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        self.emptiable_abs_bounds().time_containment_position(time)
    }
}

impl CanPositionTimeContainment for ClosedAbsoluteInterval {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        self.abs_bounds().time_containment_position(time)
    }
}

impl CanPositionTimeContainment for HalfOpenAbsoluteInterval {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        self.abs_bounds().time_containment_position(time)
    }
}

impl CanPositionTimeContainment for OpenInterval {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        self.abs_bounds().time_containment_position(time)
    }
}

impl CanPositionTimeContainment for EmptyInterval {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        self.emptiable_abs_bounds().time_containment_position(time)
    }
}

/// Capacity to position an overlap from a given [`HasEmptiableAbsoluteBounds`] implementor
pub trait CanPositionOverlap<Rhs = Self>
where
    Rhs: HasEmptiableAbsoluteBounds,
{
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

    /// Returns the simple overlap position of the given interval using a given rule set
    ///
    /// See [`CanPositionOverlap::overlap_position`] for more details about overlap position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    fn simple_overlap_position(
        &self,
        other: &Rhs,
        rule_set: OverlapRuleSet,
    ) -> Result<SimpleOverlapPosition, Self::Error> {
        self.overlap_position(other)
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
    /// This method uses [`Interval::simple_overlap_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the [`OverlapRule`]s are checked. This method returns true only if all provided
    /// [`OverlapRule`]s are respected (i.e. returned true when calling [`OverlapRule::counts_as_overlap`]).
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for overlap, see [`CanPositionOverlap::simple_overlaps`].
    ///
    /// If you are looking for more control over what counts as overlap, see [`CanPositionOverlap::overlaps_using_simple`].
    ///
    /// If you want extremely granular control over what counts as overlap, see [`CanPositionOverlap::overlaps_using`].
    #[must_use]
    fn overlaps<'a, RI>(&self, other: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a OverlapRule>,
    {
        self.simple_overlap_position(other, rule_set)
            .map(|simple_overlap_position| {
                rules
                    .into_iter()
                    .all(|rule| rule.counts_as_overlap(simple_overlap_position))
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
    /// predetermined [`SimpleOverlapPosition`]s, see [`CanPositionOverlap::overlaps_using_simple`].
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
    /// This method uses [`CanPositionOverlap::simple_overlap_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`SimpleOverlapPosition`]
    /// given by [`CanPositionOverlap::simple_overlap_position`] counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as overlapping, see [`CanPositionOverlap::overlaps_using`].
    ///
    /// If you are looking for predetermined decisions on what's considered as overlapping, see [`CanPositionOverlap::overlaps`].
    #[must_use]
    fn overlaps_using_simple<F>(&self, other: &Rhs, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(SimpleOverlapPosition) -> bool,
    {
        self.simple_overlap_position(other, rule_set).map(f).unwrap_or(false)
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
    fn extend(&self, other: &Rhs) -> Self::Output;
}

impl<Rhs> Extensible<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, other: &Rhs) -> Self::Output {
        extend_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &other.emptiable_abs_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, other: &Rhs) -> Self::Output {
        extend_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &other.emptiable_abs_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, other: &Rhs) -> Self::Output {
        AbsoluteInterval::from(self.emptiable_abs_bounds().extend(&other.emptiable_abs_bounds()))
    }
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
    fn abridge(&self, other: &Rhs) -> Self::Output;
}

impl<Rhs> Abridgable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, other: &Rhs) -> Self::Output {
        abridge_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &other.emptiable_abs_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, other: &Rhs) -> Self::Output {
        abridge_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &other.emptiable_abs_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, other: &Rhs) -> Self::Output {
        Self::from(self.emptiable_abs_bounds().abridge(&other.emptiable_abs_bounds()))
    }
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

// !!!!!!!!!!!!!!!!!!!!!!!
// TODO: Refactors those functions using bounds so that we can combine atomic data and then convert
// rather than hardcoding functions like those

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

// pub fn unite_abs_bounds_with_emptiable_abs_bounds<'a, 'b, RI>(
//     a: &'a AbsoluteBounds,
//     b: &'a EmptiableAbsoluteBounds,
//     rule_set: OverlapRuleSet,
//     rules: &'b RI,
// ) -> UnionResult<AbsoluteBounds, &'a AbsoluteBounds,>

/// Unites two [`AbsoluteInterval`]s using the given rules
pub fn unite_abs_intervals<'a, RI>(
    a: &AbsoluteInterval,
    b: &AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> UnionResult<AbsoluteInterval>
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
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

/// Intersects two [`AbsoluteBoundsOrEmpty`] using the given rules
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

/// Intersects two [`AbsoluteInterval`]s using the given rules
pub fn intersect_abs_intervals<'ri, RI>(
    a: &AbsoluteInterval,
    b: &AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> IntersectionResult<AbsoluteInterval>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Differentiates two [`AbsoluteBounds`] using the given rules
pub fn differentiate_abs_bounds<'ri, RI>(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Differentiates two [`AbsoluteBoundsOrEmpty`] using the given rules
pub fn differentiate_emptiable_abs_bounds<'ri, RI>(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Differentiates two [`AbsoluteInterval`]s using the given rules
pub fn differentiate_abs_intervals<'ri, RI>(
    a: &AbsoluteInterval,
    b: &AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<AbsoluteInterval>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
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

/// Symmetrically differentiates two [`AbsoluteBoundsOrEmpty`] using the given rules
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

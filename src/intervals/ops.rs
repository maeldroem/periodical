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

use chrono::{DateTime, Duration, DurationRound, RoundingError, Utc};

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
    pub fn try_precise_time(&self, time: DateTime<Utc>) -> Result<DateTime<Utc>, RoundingError> {
        match self {
            Self::ToNearest(duration) => time.duration_round(*duration),
            Self::ToPast(duration) => time.duration_trunc(*duration),
            Self::ToFuture(duration) => time.duration_round_up(*duration),
        }
    }
}

/// Trait to try to re-precise absolute bounds
pub trait TryPreciseAbsoluteBounds {
    /// Precises the start bound with the given precision
    ///
    /// # Errors
    ///
    /// If the rounding failed, usually if the [`Duration`] contained within the [`Precision`] is not usable during
    /// rounding, which can happen if it is negative, or if it's too long.
    fn try_precise_start_bound(&self, precision: Precision) -> Result<Option<AbsoluteStartBound>, RoundingError>;

    /// Precises the end bound with the given precision
    ///
    /// # Errors
    ///
    /// If the rounding failed, usually if the [`Duration`] contained within the [`Precision`] is not usable during
    /// rounding, which can happen if it is negative, or if it's too long.
    fn try_precise_end_bound(&self, precision: Precision) -> Result<Option<AbsoluteEndBound>, RoundingError>;

    /// Precises the start and end bound with the given precision
    ///
    /// # Errors
    ///
    /// If the rounding failed, usually if the [`Duration`] contained within the [`Precision`] is not usable during
    /// rounding, which can happen if it is negative, or if it's too long.
    fn try_precise_bounds(&self, precision: Precision) -> Result<AbsoluteBounds, RoundingError> {
        self.try_precise_bounds_with_different_precision(precision, precision)
    }

    /// Precises the start and end bound with different precisions for both of them
    ///
    /// # Errors
    ///
    /// If the rounding failed, usually if the [`Duration`] contained within the [`Precision`] is not usable during
    /// rounding, which can happen if it is negative, or if it's too long.
    fn try_precise_bounds_with_different_precision(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Result<AbsoluteBounds, RoundingError> {
        let start = self.try_precise_start_bound(precision_start)?;
        let end = self.try_precise_end_bound(precision_end)?;

        Ok(match (start, end) {
            (None, _) | (_, None) => AbsoluteBounds::new_empty(),
            (Some(start), Some(end)) => AbsoluteBounds::new(start, end),
        })
    }
}

impl<T: HasAbsoluteBounds> TryPreciseAbsoluteBounds for T {
    fn try_precise_start_bound(&self, precision: Precision) -> Result<Option<AbsoluteStartBound>, RoundingError> {
        match self.abs_start() {
            None => Ok(None),
            Some(AbsoluteStartBound::InfinitePast) => Ok(Some(AbsoluteStartBound::InfinitePast)),
            Some(AbsoluteStartBound::Finite(time, inclusivity)) => {
                let precised_time = precision.try_precise_time(time)?;

                Ok(Some(AbsoluteStartBound::Finite(precised_time, inclusivity)))
            },
        }
    }

    fn try_precise_end_bound(&self, precision: Precision) -> Result<Option<AbsoluteEndBound>, RoundingError> {
        match self.abs_end() {
            None => Ok(None),
            Some(AbsoluteEndBound::InfiniteFuture) => Ok(Some(AbsoluteEndBound::InfiniteFuture)),
            Some(AbsoluteEndBound::Finite(time, inclusivity)) => {
                let precised_time = precision.try_precise_time(time)?;

                Ok(Some(AbsoluteEndBound::Finite(precised_time, inclusivity)))
            },
        }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimeContainmentRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds, so the time needs to fall on an inclusive bound in order to be counted
    /// as contained.
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

fn strict_containment_rule_set_disambiguation(
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

fn lenient_containment_rule_set_disambiguation(
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
pub const SIMPLE_TIME_CONTAINMENT_RULES: [TimeContainmentRule; 0] = [];

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

fn deny_on_start_containment_rule_counts_as_contained(
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

fn deny_on_end_containment_rule_counts_as_contained(
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

fn deny_on_bounds_containment_rule_counts_as_contained(
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

fn strict_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
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

fn continuous_to_future_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
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

fn continuous_to_past_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
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

fn lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
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

fn very_lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    overlap_position.to_simple()
}

pub const SIMPLE_OVERLAP_RULES: [OverlapRule; 1] = [OverlapRule::DenyAdjacency];

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

fn allow_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore | SimpleOverlapPosition::OutsideAfter | SimpleOverlapPosition::Outside
    )
}

fn deny_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore
            | SimpleOverlapPosition::OutsideAfter
            | SimpleOverlapPosition::Outside
            | SimpleOverlapPosition::OnStart
            | SimpleOverlapPosition::OnEnd
    )
}

fn allow_past_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore
            | SimpleOverlapPosition::OutsideAfter
            | SimpleOverlapPosition::Outside
            | SimpleOverlapPosition::OnEnd
    )
}

fn allow_future_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
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
    /// Uses the [`Strict` rule set](TimeContainmentRuleSet::Strict) with no additional rules.
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
        self.contains(time, TimeContainmentRuleSet::Strict, &SIMPLE_TIME_CONTAINMENT_RULES)
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
    fn contains<'a, RI>(&self, time: DateTime<Utc>, rule_set: TimeContainmentRuleSet, rules: &'a RI) -> bool
    where
        &'a RI: IntoIterator<Item = &'a TimeContainmentRule>,
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

impl<T: HasAbsoluteBounds> CanPositionTimeContainment for T {
    type Error = ();

    fn time_containment_position(&self, time: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        type StartB = AbsoluteStartBound;
        type EndB = AbsoluteEndBound;
        type ContPos = TimeContainmentPosition;

        let bounds = self.abs_bounds();

        if bounds.is_empty() {
            return Ok(ContPos::Outside);
        }

        let containment_position = match (bounds.abs_start().unwrap(), bounds.abs_end().unwrap()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => ContPos::Inside,
            (StartB::InfinitePast, EndB::Finite(ref end_time, inclusivity)) => match time.cmp(end_time) {
                Ordering::Less => ContPos::Inside,
                Ordering::Equal => ContPos::OnEnd(inclusivity),
                Ordering::Greater => ContPos::OutsideAfter,
            },
            (StartB::Finite(ref start_time, inclusivity), EndB::InfiniteFuture) => match time.cmp(start_time) {
                Ordering::Less => ContPos::OutsideBefore,
                Ordering::Equal => ContPos::OnStart(inclusivity),
                Ordering::Greater => ContPos::Inside,
            },
            (StartB::Finite(ref start_time, start_inclusivity), EndB::Finite(ref end_time, end_inclusivity)) => {
                match (time.cmp(start_time), time.cmp(end_time)) {
                    (Ordering::Less, _) => ContPos::OutsideBefore,
                    (Ordering::Equal, _) => ContPos::OnStart(start_inclusivity),
                    (_, Ordering::Less) => ContPos::Inside,
                    (_, Ordering::Equal) => ContPos::OnEnd(end_inclusivity),
                    (_, Ordering::Greater) => ContPos::OutsideAfter,
                }
            },
        };

        Ok(containment_position)
    }
}

/// Capacity to position an overlap between two intervals
pub trait CanPositionOverlap {
    /// Error type if the overlap positioning failed
    type Error;

    /// Returns the overlap position of the given interval
    ///
    /// The current interval is compared to the other interval, that means that if you, for example, compare
    /// a closed absolute interval (instance) with an open interval (given interval), you will get
    /// [`OverlapPosition::Inside`] as the closed absolute interval _is contained_ by an open interval.
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
    fn overlap_position(&self, other: &Self) -> Result<OverlapPosition, Self::Error>;

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
        other: &Self,
        rule_set: OverlapRuleSet,
    ) -> Result<SimpleOverlapPosition, Self::Error> {
        self.overlap_position(other)
            .map(|overlap_position| rule_set.disambiguate(overlap_position))
    }

    /// Returns whether the given other interval overlaps the current one using predetermined rules
    ///
    /// Uses the [`Strict` rule set](OverlapRuleSet::Strict) with the following additional rules:
    ///
    /// - [`DenyAdjacency`](OverlapRule::DenyAdjacency)
    ///
    /// Those have been chosen because they are the closest to how we mathematically and humanly interpret overlaps.
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see [`CanPositionOverlap::overlaps`].
    ///
    /// If you want even more granular control, see [`CanPositionOverlap::overlaps_using_simple`].
    #[must_use]
    fn simple_overlaps(&self, other: &Self) -> bool {
        self.overlaps(other, OverlapRuleSet::Strict, &SIMPLE_OVERLAP_RULES)
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
    fn overlaps<'a, RI>(&self, other: &Self, rule_set: OverlapRuleSet, rules: &'a RI) -> bool
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
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
    fn overlaps_using<F>(&self, other: &Self, f: F) -> bool
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
    fn overlaps_using_simple<F>(&self, other: &Self, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(SimpleOverlapPosition) -> bool,
    {
        self.simple_overlap_position(other, rule_set).map(f).unwrap_or(false)
    }
}

impl<T: HasAbsoluteBounds> CanPositionOverlap for T {
    type Error = ();

    fn overlap_position(&self, other: &Self) -> Result<OverlapPosition, Self::Error> {
        if self.is_empty() || other.is_empty() {
            return Ok(OverlapPosition::Outside);
        }

        let self_start = self.abs_start().unwrap();
        let self_end = self.abs_end().unwrap();
        let other_start = other.abs_start().unwrap();
        let other_end = other.abs_end().unwrap();

        let overlap_position = overlap_position_bounds((self_start, self_end), (other_start, other_end));

        Ok(overlap_position)
    }
}

// Can't really make this function shorter
#[allow(clippy::too_many_lines)]
fn overlap_position_bounds(
    og: (AbsoluteStartBound, AbsoluteEndBound),
    other: (AbsoluteStartBound, AbsoluteEndBound),
) -> OverlapPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;
    type OP = OverlapPosition;

    match (og, other) {
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
        (
            (StartB::InfinitePast, EndB::Finite(ref og_time, og_inclusivity)),
            (StartB::InfinitePast, EndB::Finite(ref other_time, other_inclusivity)),
        ) => match og_time.cmp(other_time) {
            Ordering::Less => OP::InsideAndSameStart(None, None),
            Ordering::Equal => OP::Equal((None, Some(og_inclusivity)), (None, Some(other_inclusivity))),
            Ordering::Greater => OP::ContainsAndSameStart(None, None),
        },
        (
            (StartB::Finite(ref og_time, og_inclusivity), EndB::InfiniteFuture),
            (StartB::Finite(ref other_time, other_inclusivity), EndB::InfiniteFuture),
        ) => match og_time.cmp(other_time) {
            Ordering::Less => OP::ContainsAndSameEnd(None, None),
            Ordering::Equal => OP::Equal((Some(og_inclusivity), None), (Some(other_inclusivity), None)),
            Ordering::Greater => OP::InsideAndSameEnd(None, None),
        },
        (
            (StartB::InfinitePast, EndB::Finite(ref og_time, og_inclusivity)),
            (StartB::Finite(ref other_time, other_inclusivity), EndB::InfiniteFuture),
        ) => match og_time.cmp(other_time) {
            Ordering::Less => OP::OutsideBefore,
            Ordering::Equal => OP::OnStart(og_inclusivity, other_inclusivity),
            Ordering::Greater => OP::CrossesStart,
        },
        (
            (StartB::Finite(ref og_time, og_inclusivity), EndB::InfiniteFuture),
            (StartB::InfinitePast, EndB::Finite(ref other_time, other_inclusivity)),
        ) => match og_time.cmp(other_time) {
            Ordering::Less => OP::CrossesStart,
            Ordering::Equal => OP::OnEnd(og_inclusivity, other_inclusivity),
            Ordering::Greater => OP::OutsideAfter,
        },
        (
            (StartB::InfinitePast, EndB::Finite(ref ref_time, ref_inclusivity)),
            (
                StartB::Finite(ref other_start_time, other_start_inclusivity),
                EndB::Finite(ref other_end_time, other_end_inclusivity),
            ),
        ) => overlap_position_half_open_past_closed(
            (ref_time, ref_inclusivity),
            (other_start_time, other_start_inclusivity),
            (other_end_time, other_end_inclusivity),
        ),
        (
            (StartB::Finite(ref ref_time, ref_inclusivity), EndB::InfiniteFuture),
            (
                StartB::Finite(ref other_start_time, other_start_inclusivity),
                EndB::Finite(ref other_end_time, other_end_inclusivity),
            ),
        ) => overlap_position_half_open_future_closed(
            (ref_time, ref_inclusivity),
            (other_start_time, other_start_inclusivity),
            (other_end_time, other_end_inclusivity),
        ),
        (
            (
                StartB::Finite(ref og_start_time, og_start_inclusivity),
                EndB::Finite(ref og_end_time, og_end_inclusivity),
            ),
            (StartB::InfinitePast, EndB::Finite(ref ref_time, ref_inclusivity)),
        ) => overlap_position_closed_half_open_past(
            (og_start_time, og_start_inclusivity),
            (og_end_time, og_end_inclusivity),
            (ref_time, ref_inclusivity),
        ),
        (
            (
                StartB::Finite(ref og_start_time, og_start_inclusivity),
                EndB::Finite(ref og_end_time, og_end_inclusivity),
            ),
            (StartB::Finite(ref ref_time, ref_inclusivity), EndB::InfiniteFuture),
        ) => overlap_position_closed_half_open_future(
            (og_start_time, og_start_inclusivity),
            (og_end_time, og_end_inclusivity),
            (ref_time, ref_inclusivity),
        ),
        (
            (
                StartB::Finite(ref og_start_time, og_start_inclusivity),
                EndB::Finite(ref og_end_time, og_end_inclusivity),
            ),
            (
                StartB::Finite(ref other_start_time, other_start_inclusivity),
                EndB::Finite(ref other_end_time, other_end_inclusivity),
            ),
        ) => overlap_position_closed_pair(
            (og_start_time, og_start_inclusivity),
            (og_end_time, og_end_inclusivity),
            (other_start_time, other_start_inclusivity),
            (other_end_time, other_end_inclusivity),
        ),
    }
}

fn overlap_position_half_open_past_closed(
    ref_bound: (&DateTime<Utc>, BoundInclusivity),
    other_start: (&DateTime<Utc>, BoundInclusivity),
    other_end: (&DateTime<Utc>, BoundInclusivity),
) -> OverlapPosition {
    match (ref_bound.0.cmp(other_start.0), ref_bound.0.cmp(other_end.0)) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::OnStart(ref_bound.1, other_start.1),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::ContainsAndSameEnd(Some(ref_bound.1), Some(other_end.1)),
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

fn overlap_position_half_open_future_closed(
    ref_bound: (&DateTime<Utc>, BoundInclusivity),
    other_start: (&DateTime<Utc>, BoundInclusivity),
    other_end: (&DateTime<Utc>, BoundInclusivity),
) -> OverlapPosition {
    match (ref_bound.0.cmp(other_start.0), ref_bound.0.cmp(other_end.0)) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => OverlapPosition::ContainsAndSameStart(Some(ref_bound.1), Some(other_start.1)),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::OnEnd(ref_bound.1, other_end.1),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

fn overlap_position_closed_half_open_past(
    og_start: (&DateTime<Utc>, BoundInclusivity),
    og_end: (&DateTime<Utc>, BoundInclusivity),
    ref_bound: (&DateTime<Utc>, BoundInclusivity),
) -> OverlapPosition {
    match (ref_bound.0.cmp(og_start.0), ref_bound.0.cmp(og_end.0)) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::OnEnd(og_start.1, ref_bound.1),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::InsideAndSameEnd(Some(og_end.1), Some(ref_bound.1)),
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

fn overlap_position_closed_half_open_future(
    og_start: (&DateTime<Utc>, BoundInclusivity),
    og_end: (&DateTime<Utc>, BoundInclusivity),
    ref_bound: (&DateTime<Utc>, BoundInclusivity),
) -> OverlapPosition {
    match (ref_bound.0.cmp(og_start.0), ref_bound.0.cmp(og_end.0)) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => OverlapPosition::InsideAndSameStart(Some(og_start.1), Some(ref_bound.1)),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::OnStart(og_end.1, ref_bound.1),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

fn overlap_position_closed_pair(
    og_start: (&DateTime<Utc>, BoundInclusivity),
    og_end: (&DateTime<Utc>, BoundInclusivity),
    other_start: (&DateTime<Utc>, BoundInclusivity),
    other_end: (&DateTime<Utc>, BoundInclusivity),
) -> OverlapPosition {
    let og_start_cmp = (og_start.0.cmp(other_start.0), og_start.0.cmp(other_end.0));
    let og_end_cmp = (og_end.0.cmp(other_start.0), og_end.0.cmp(other_end.0));

    match (og_start_cmp, og_end_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::OnStart(og_end.1, other_start.1),
        ((_, Ordering::Equal), _) => OverlapPosition::OnEnd(og_start.1, other_end.1),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => {
            OverlapPosition::InsideAndSameStart(Some(og_start.1), Some(other_start.1))
        },
        ((Ordering::Greater, _), (_, Ordering::Equal)) => {
            OverlapPosition::InsideAndSameEnd(Some(og_end.1), Some(other_end.1))
        },
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            (Some(og_start.1), Some(og_end.1)),
            (Some(other_start.1), Some(other_end.1)),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => {
            OverlapPosition::ContainsAndSameStart(Some(og_start.1), Some(other_start.1))
        },
        ((Ordering::Less, _), (_, Ordering::Equal)) => {
            OverlapPosition::ContainsAndSameEnd(Some(og_end.1), Some(other_end.1))
        },
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

pub trait Extensible {
    /// Error type if the interval extension failed
    type Error;

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
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](Extensible::Error).
    fn extend(&self, other: &Self) -> Result<AbsoluteInterval, Self::Error>;
}

impl<T: HasAbsoluteBounds> Extensible for T {
    type Error = ();

    fn extend(&self, other: &Self) -> Result<AbsoluteInterval, Self::Error>
    where
        Self: Sized,
    {
        let is_self_empty = self.is_empty();
        let is_other_empty = other.is_empty();

        if is_self_empty && is_other_empty {
            return Ok(AbsoluteInterval::Empty(EmptyInterval));
        }

        if is_self_empty {
            return Ok(AbsoluteInterval::from(other.abs_bounds()));
        }

        if is_other_empty {
            return Ok(AbsoluteInterval::from(self.abs_bounds()));
        }

        let new_start_bound = match (self.abs_start().unwrap(), other.abs_start().unwrap()) {
            (bound @ AbsoluteStartBound::InfinitePast, _) | (_, bound @ AbsoluteStartBound::InfinitePast) => bound,
            (og_bound @ AbsoluteStartBound::Finite(..), other_bound @ AbsoluteStartBound::Finite(..)) => {
                if og_bound <= other_bound { og_bound } else { other_bound }
            },
        };

        let new_end_bound = match (self.abs_end().unwrap(), other.abs_end().unwrap()) {
            (bound @ AbsoluteEndBound::InfiniteFuture, _) | (_, bound @ AbsoluteEndBound::InfiniteFuture) => bound,
            (og_bound @ AbsoluteEndBound::Finite(..), other_bound @ AbsoluteEndBound::Finite(..)) => {
                if og_bound >= other_bound { og_bound } else { other_bound }
            },
        };

        Ok(AbsoluteInterval::from(AbsoluteBounds::new(
            new_start_bound,
            new_end_bound,
        )))
    }
}

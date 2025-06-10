use std::cmp::Ordering;

use chrono::{DateTime, Duration, Utc};

use crate::intervals::Interval;
use crate::intervals::interval::{ClosedAbsoluteInterval, HalfOpenAbsoluteInterval};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};

/// Time precision used for comparisons
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Precision {
    /// Rounds the compared times to the given duration (e.g. if the duration is 1 second, the times will be rounded to the nearest second)
    ToNearest(Duration),
    /// Floors the compared times to the given duration (e.g. if the duration is 5 minutes, the times will be floored to the 5-minutes part they are in)
    ToPast(Duration),
    /// Ceils the compared times to the given duration
    ToFuture(Duration),
}

/// Where the given time was found relative to a time interval
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContainmentPosition {
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

/// Errors that can happen when computing the containment position of some time inside an interval
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContainmentPositionError {
    /// The interval is relative, therefore we can't determine the containment position of the given time
    RelativeInterval,
    /// The interval was malformed, therefore we can't determine the containment position of the given time safely
    MalformedInterval,
}

/// Different rule sets for determining whether different [`ContainmentPosition`]s are considered as containing or not.
///
/// See [`Interval::contains_using_rule_set`] for more.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContainmentRuleSet {
    // TODO
}

/// Where the other time interval was found relative to the current time interval
///
/// See [`Interval::overlap_position`] for more information
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapPosition {
    /// The given other time interval was found before the time interval
    OutsideBefore,
    /// The given other time interval was found after the time interval
    OutsideAfter,
    /// The given other time interval was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given other time interval was found ending on the beginning of the time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// See [`Interval::overlap_position`] for more details.
    OnStart(BoundInclusivity, BoundInclusivity),
    /// The given other time interval was found starting on the end of the time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// See [`Interval::overlap_position`] for more details.
    OnEnd(BoundInclusivity, BoundInclusivity),
    /// The given other time interval was found beginning outside the time interval but ending inside
    CrossesStart,
    /// The given other time interval was found beginning inside the time interval but ending outside
    CrossesEnd,
    /// The given other time interval was found completely inside the time interval
    Inside,
    /// The given other time interval was found beginning on the start of the time interval and ending inside
    /// the time interval
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
    /// The given other time interval was found beginning inside the time interval and ending at the end of
    /// the time interval
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
    /// The given other time interval was found beginning and ending at the same times as the time interval
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
    /// The given other time interval was found beginning on the same point as the time interval and ending after
    /// the time interval
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
    /// The given other time interval was found beginning before the time interval and ending at the same time as
    /// the time interval
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
    /// The given other time interval was found beginning before the time interval's start and ending after the time interval's end
    Contains,
}

/// Errors that can happen when computing the overlap position of two intervals
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapPositionError {
    /// One interval was relative, therefore we can't determine the overlap position of the given time
    RelativeInterval,
    /// One interval was malformed, therefore we can't determine the overlap position of the given time safely
    MalformedInterval,
}

/// Different rule sets for determining whether different [`OverlapPosition`]s are considered as overlapping or not.
///
/// See [`Interval::overlaps_using_rule_set`] for more.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapRuleSet {
    // TODO
}

impl Interval {
    /// Returns the containment position of the given time
    ///
    /// # Bound inclusivity
    ///
    /// When checking the containment position, the reference interval's bound inclusivities are considered
    /// as inclusive. Then, on cases where the result could be ambiguous (e.g. if the time ends up on the reference
    /// interval's start but the inclusivity of this bound is exclusive, does it qualify
    /// as [`ContainmentPosition::OnStart`]?), we simply include the inclusivity of the concerned bound and let the
    /// receiver make the call on whether it counts or not.
    ///
    /// This way, we can guarantee maximum flexibility of this process.
    ///
    /// # Errors
    ///
    /// If the interval the operation is done on is relative, the methods returns [`ContainmentPositionError::RelativeInterval`]
    pub fn containment_position(&self, time: DateTime<Utc>) -> Result<ContainmentPosition, ContainmentPositionError> {
        match self {
            Self::ClosedRelative(_) | Self::HalfOpenRelative(_) => Err(ContainmentPositionError::RelativeInterval),
            Self::ClosedAbsolute(interval) => containment_position_closed(interval, time),
            Self::HalfOpenAbsolute(interval) => Ok(containment_position_half_open(interval, time)),
            Self::Empty(_) => Ok(ContainmentPosition::Outside),
            Self::Open(_) => Ok(ContainmentPosition::Inside),
        }
    }

    /// Returns whether a certain time is contained in the interval
    ///
    /// This method uses [`Interval::containment_position`]. If this aforementionned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`ContainmentPosition`]
    /// given by [`Interval::containment_position`] counts as the passed time being contained in the interval.
    ///
    /// If instead you want predetermined decisions on whether some positions count as contained or not,
    /// check out [`Interval::contains_using_rule_set`].
    #[must_use]
    pub fn contains<F>(&self, time: DateTime<Utc>, f: F) -> bool
    where
        F: FnOnce(ContainmentPosition) -> bool,
    {
        self.containment_position(time).map(f).unwrap_or(false)
    }

    /// TODO
    #[must_use]
    pub fn contains_using_rule_set(&self, time: DateTime<Utc>, rule_set: ContainmentRuleSet) -> bool {
        todo!();
    }

    /// Returns the overlap position of the given interval
    ///
    /// The other interval is compared to the current interval, that means that if you, for example, compare
    /// a closed absolute interval (instance) with an open interval (given interval), you will get
    /// [`OverlapPosition::Contains`] as the open interval _contains_ any closed absolute interval.
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
    /// - Returns [`OverlapPositionError::RelativeInterval`] if the current or given interval is relative.
    /// - Returns [`OverlapPositionError::MalformedInterval`] if the current or given interval is malformed in any way
    ///   (e.g. the start time is after the end time)
    pub fn overlap_position(&self, other: &Self) -> Result<OverlapPosition, OverlapPositionError> {
        match (self, other) {
            (Self::ClosedRelative(_) | Self::HalfOpenRelative(_), _)
            | (_, Self::ClosedRelative(_) | Self::HalfOpenRelative(_)) => Err(OverlapPositionError::RelativeInterval),
            (Self::ClosedAbsolute(interval), Self::ClosedAbsolute(other_interval)) => {
                overlap_position_closed_pair(interval, other_interval)
            },
            (Self::ClosedAbsolute(interval), Self::HalfOpenAbsolute(other_interval)) => {
                overlap_position_closed_half_open(interval, other_interval)
            },
            (Self::HalfOpenAbsolute(interval), Self::ClosedAbsolute(other_interval)) => {
                overlap_position_half_open_closed(interval, other_interval)
            },
            (Self::HalfOpenAbsolute(interval), Self::HalfOpenAbsolute(other_interval)) => {
                Ok(overlap_position_half_open_pair(interval, other_interval))
            },
            // empty intervals are not comparable through time as they don't have a specific time frame
            (Self::Empty(_), _) | (_, Self::Empty(_)) => Ok(OverlapPosition::Outside),
            (Self::Open(_), Self::Open(_)) => Ok(OverlapPosition::Equal((None, None), (None, None))),
            (Self::Open(_), Self::HalfOpenAbsolute(half_open_interval)) => {
                match half_open_interval.opening_direction() {
                    OpeningDirection::ToPast => Ok(OverlapPosition::InsideAndSameStart(None, None)),
                    OpeningDirection::ToFuture => Ok(OverlapPosition::InsideAndSameEnd(None, None)),
                }
            },
            (Self::Open(_), Self::ClosedAbsolute(_)) => Ok(OverlapPosition::Inside),
            (Self::HalfOpenAbsolute(half_open_interval), Self::Open(_)) => {
                match half_open_interval.opening_direction() {
                    OpeningDirection::ToPast => Ok(OverlapPosition::ContainsAndSameStart(None, None)),
                    OpeningDirection::ToFuture => Ok(OverlapPosition::ContainsAndSameEnd(None, None)),
                }
            },
            (Self::ClosedAbsolute(_), Self::Open(_)) => Ok(OverlapPosition::Contains),
        }
    }

    /// Returns whether the given other interval overlaps the current interval
    ///
    /// This method uses [`Interval::overlap_position`]. If this aforementionned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`OverlapPosition`]
    /// given by [`Interval::overlap_position`] counts as overlapping or not.
    ///
    /// If instead you want predetermined decisions on whether some positions count as overlapping or not,
    /// check out [`Interval::overlaps_using_rule_set`].
    #[must_use]
    pub fn overlaps<F>(&self, other: &Self, f: F) -> bool
    where
        F: FnOnce(OverlapPosition) -> bool,
    {
        self.overlap_position(other).map(f).unwrap_or(false)
    }

    /// TODO
    #[must_use]
    pub fn overlaps_using_rule_set(&self, other: &Self, rule_set: OverlapRuleSet) -> bool {
        todo!()
    }
}

fn containment_position_closed(
    interval: &ClosedAbsoluteInterval,
    time: DateTime<Utc>,
) -> Result<ContainmentPosition, ContainmentPositionError> {
    if interval.is_malformed() {
        return Err(ContainmentPositionError::MalformedInterval);
    }

    let containment_position = match (time.cmp(interval.from()), time.cmp(interval.to())) {
        (Ordering::Less, _) => ContainmentPosition::OutsideBefore,
        (_, Ordering::Greater) => ContainmentPosition::OutsideAfter,
        (Ordering::Equal, _) => ContainmentPosition::OnStart(interval.from_inclusivity()),
        (_, Ordering::Equal) => ContainmentPosition::OnEnd(interval.to_inclusivity()),
        (Ordering::Greater, Ordering::Less) => ContainmentPosition::Inside,
    };

    Ok(containment_position)
}

fn containment_position_half_open(interval: &HalfOpenAbsoluteInterval, time: DateTime<Utc>) -> ContainmentPosition {
    match (time.cmp(interval.reference_time()), interval.opening_direction()) {
        (Ordering::Less, OpeningDirection::ToPast) | (Ordering::Greater, OpeningDirection::ToFuture) => {
            ContainmentPosition::Inside
        },
        (Ordering::Equal, OpeningDirection::ToPast) => {
            ContainmentPosition::OnEnd(interval.reference_time_inclusivity())
        },
        (Ordering::Greater, OpeningDirection::ToPast) => ContainmentPosition::OutsideAfter,
        (Ordering::Less, OpeningDirection::ToFuture) => ContainmentPosition::OutsideBefore,
        (Ordering::Equal, OpeningDirection::ToFuture) => {
            ContainmentPosition::OnStart(interval.reference_time_inclusivity())
        },
    }
}

fn overlap_position_closed_pair(
    a: &ClosedAbsoluteInterval,
    b: &ClosedAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if a.is_malformed() || b.is_malformed() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let b_from_cmp = (b.from().cmp(a.from()), b.from().cmp(a.to()));
    let b_to_cmp = (b.to().cmp(a.from()), b.to().cmp(a.to()));

    let overlap_position = match (b_from_cmp, b_to_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::OnStart(a.from_inclusivity(), b.to_inclusivity()),
        ((_, Ordering::Equal), _) => OverlapPosition::OnEnd(a.to_inclusivity(), b.from_inclusivity()),
        ((Ordering::Less, _), (_, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, _), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => {
            OverlapPosition::InsideAndSameStart(Some(a.from_inclusivity()), Some(b.from_inclusivity()))
        },
        ((Ordering::Greater, _), (_, Ordering::Equal)) => {
            OverlapPosition::InsideAndSameEnd(Some(a.to_inclusivity()), Some(b.to_inclusivity()))
        },
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            (Some(a.from_inclusivity()), Some(a.to_inclusivity())),
            (Some(b.from_inclusivity()), Some(b.to_inclusivity())),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => {
            OverlapPosition::ContainsAndSameStart(Some(a.from_inclusivity()), Some(b.from_inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Equal)) => {
            OverlapPosition::ContainsAndSameEnd(Some(a.to_inclusivity()), Some(b.to_inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    };

    Ok(overlap_position)
}

fn overlap_position_closed_half_open(
    a: &ClosedAbsoluteInterval,
    b: &HalfOpenAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if a.is_malformed() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let overlap_position = match (
        b.reference_time().cmp(a.from()),
        b.reference_time().cmp(a.to()),
        b.opening_direction(),
    ) {
        (Ordering::Less, _, OpeningDirection::ToPast) => OverlapPosition::OutsideBefore,
        (_, Ordering::Greater, OpeningDirection::ToFuture) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _, OpeningDirection::ToPast) => {
            OverlapPosition::OnStart(a.from_inclusivity(), b.reference_time_inclusivity())
        },
        (_, Ordering::Equal, OpeningDirection::ToFuture) => {
            OverlapPosition::OnEnd(a.to_inclusivity(), b.reference_time_inclusivity())
        },
        (Ordering::Greater, Ordering::Less, OpeningDirection::ToPast) => OverlapPosition::CrossesStart,
        (Ordering::Greater, Ordering::Less, OpeningDirection::ToFuture) => OverlapPosition::CrossesEnd,
        (Ordering::Equal, _, OpeningDirection::ToFuture) => {
            OverlapPosition::ContainsAndSameStart(Some(a.from_inclusivity()), Some(b.reference_time_inclusivity()))
        },
        (_, Ordering::Equal, OpeningDirection::ToPast) => {
            OverlapPosition::ContainsAndSameEnd(Some(a.to_inclusivity()), Some(b.reference_time_inclusivity()))
        },
        (Ordering::Less, _, OpeningDirection::ToFuture) | (_, Ordering::Greater, OpeningDirection::ToPast) => {
            OverlapPosition::Contains
        },
    };

    Ok(overlap_position)
}

fn overlap_position_half_open_closed(
    a: &HalfOpenAbsoluteInterval,
    b: &ClosedAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if b.is_malformed() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let overlap_position = match (
        b.from().cmp(a.reference_time()),
        b.to().cmp(a.reference_time()),
        a.opening_direction(),
    ) {
        (_, Ordering::Less, OpeningDirection::ToFuture) => OverlapPosition::OutsideBefore,
        (Ordering::Greater, _, OpeningDirection::ToPast) => OverlapPosition::OutsideAfter,
        (_, Ordering::Equal, OpeningDirection::ToFuture) => {
            OverlapPosition::OnStart(a.reference_time_inclusivity(), b.to_inclusivity())
        },
        (Ordering::Equal, _, OpeningDirection::ToPast) => {
            OverlapPosition::OnEnd(a.reference_time_inclusivity(), b.from_inclusivity())
        },
        (Ordering::Less, Ordering::Greater, OpeningDirection::ToFuture) => OverlapPosition::CrossesStart,
        (Ordering::Less, Ordering::Greater, OpeningDirection::ToPast) => OverlapPosition::CrossesEnd,
        (Ordering::Less, Ordering::Less, OpeningDirection::ToPast)
        | (Ordering::Greater, Ordering::Greater, OpeningDirection::ToFuture) => OverlapPosition::Inside,
        (Ordering::Equal, Ordering::Greater, OpeningDirection::ToFuture) => {
            OverlapPosition::InsideAndSameStart(Some(a.reference_time_inclusivity()), Some(b.from_inclusivity()))
        },
        (Ordering::Less, Ordering::Equal, OpeningDirection::ToPast) => {
            OverlapPosition::InsideAndSameEnd(Some(a.reference_time_inclusivity()), Some(b.to_inclusivity()))
        },
    };

    Ok(overlap_position)
}

fn overlap_position_half_open_pair(a: &HalfOpenAbsoluteInterval, b: &HalfOpenAbsoluteInterval) -> OverlapPosition {
    match (
        b.reference_time().cmp(a.reference_time()),
        a.opening_direction(),
        b.opening_direction(),
    ) {
        (Ordering::Less, OpeningDirection::ToPast, OpeningDirection::ToPast) => OverlapPosition::InsideAndSameStart(
            Some(a.reference_time_inclusivity()),
            Some(b.reference_time_inclusivity()),
        ),
        (Ordering::Less, OpeningDirection::ToPast, OpeningDirection::ToFuture) => OverlapPosition::CrossesEnd,
        (Ordering::Less, OpeningDirection::ToFuture, OpeningDirection::ToPast) => OverlapPosition::OutsideBefore,
        (Ordering::Less, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => {
            OverlapPosition::ContainsAndSameEnd(
                Some(a.reference_time_inclusivity()),
                Some(b.reference_time_inclusivity()),
            )
        },
        (Ordering::Equal, OpeningDirection::ToPast, OpeningDirection::ToPast)
        | (Ordering::Equal, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => OverlapPosition::Equal(
            (Some(a.reference_time_inclusivity()), None),
            (Some(b.reference_time_inclusivity()), None),
        ),
        (Ordering::Equal, OpeningDirection::ToPast, OpeningDirection::ToFuture) => {
            OverlapPosition::OnEnd(a.reference_time_inclusivity(), b.reference_time_inclusivity())
        },
        (Ordering::Equal, OpeningDirection::ToFuture, OpeningDirection::ToPast) => {
            OverlapPosition::OnStart(a.reference_time_inclusivity(), b.reference_time_inclusivity())
        },
        (Ordering::Greater, OpeningDirection::ToPast, OpeningDirection::ToPast) => {
            OverlapPosition::ContainsAndSameStart(
                Some(a.reference_time_inclusivity()),
                Some(b.reference_time_inclusivity()),
            )
        },
        (Ordering::Greater, OpeningDirection::ToPast, OpeningDirection::ToFuture) => OverlapPosition::OutsideAfter,
        (Ordering::Greater, OpeningDirection::ToFuture, OpeningDirection::ToPast) => OverlapPosition::CrossesStart,
        (Ordering::Greater, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => {
            OverlapPosition::InsideAndSameEnd(
                Some(a.reference_time_inclusivity()),
                Some(b.reference_time_inclusivity()),
            )
        },
    }
}

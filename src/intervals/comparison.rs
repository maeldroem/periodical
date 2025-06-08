use std::cmp::Ordering;

use chrono::{DateTime, Duration, Utc};

use crate::intervals::Interval;
use crate::intervals::interval::{ClosedAbsoluteInterval, HalfOpenAbsoluteInterval};
use crate::intervals::meta::{OpeningDirection, Relativity};

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
    OnStart,
    /// The given time was found exactly on the end of the time interval
    OnEnd,
    /// The given time was found within the time interval
    Inside,
}

/// Errors that can happen when computing the containment position of some time inside an interval
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContainmentPositionError {
    /// The interval is relative, therefore we can't determine the containment position of the given time
    RelativeInterval,
}

/// Where the other time interval was found relative to the current time interval
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapPosition {
    /// The given other time interval was found before the time interval
    OutsideBefore,
    /// The given other time interval was found after the time interval
    OutsideAfter,
    /// The given other time interval was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given other time interval was found ending on the beginning of the time interval
    OnStart,
    /// The given other time interval was found starting on the end of the time interval
    OnEnd,
    /// The given other time interval was found beginning outside the time interval but ending inside
    CrossesStart,
    /// The given other time interval was found beginning inside the time interval but ending outside
    CrossesEnd,
    /// The given other time interval was found completely inside the time interval
    Inside,
    /// The given other time interval was found beginning on the start of of the time interval and ending inside the time interval
    InsideAndSameStart,
    /// The given other time interval was found beginning inside the time interval and ending at the end of the time interval
    InsideAndSameEnd,
    /// The given other time interval was found beginning and ending at the same times as the time interval
    Equal,
    /// The given other time interval was found beginning on the same point as the time interval and ending after the time interval
    ContainsAndSameStart,
    /// The given other time interval was found beginning before the time interval and ending at the same time as the time interval
    ContainsAndSameEnd,
    /// The given other time interval was found beginning before the time interval's start and ending after the time interval's end
    Contains,
}

/// Errors that can happen when computing the overlap position of two intervals
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapPositionError {
    RelativeInterval,
    MalformedInterval,
}

impl Interval {
    /// Returns the containment position of the given time
    ///
    /// # Errors
    ///
    /// If the interval the operation is done on is relative, the methods returns [`ContainmentPositionError::RelativeInterval`]
    pub fn containment_position(
        &self,
        time: DateTime<Utc>,
    ) -> Result<ContainmentPosition, ContainmentPositionError> {
        match self {
            Self::ClosedRelative(_) | Self::HalfOpenRelative(_) => {
                Err(ContainmentPositionError::RelativeInterval)
            }
            Self::ClosedAbsolute(interval) => Ok(containment_position_closed(interval, time)),
            Self::HalfOpenAbsolute(interval) => Ok(containment_position_half_open(interval, time)),
            Self::Empty(_) => Ok(ContainmentPosition::Outside),
            Self::Open(_) => Ok(ContainmentPosition::Inside),
        }
    }

    /// Returns the overlap position of the given interval
    ///
    /// The other interval is compared to the current interval, that means that if you, for example, compare
    /// a closed absolute interval (instance) with an open interval (given interval), you will get [`OverlapPosition::Contains`]
    /// as the open interval _contains_ any closed absolute interval.
    ///
    /// # Errors
    ///
    /// - Returns [`OverlapPositionError::RelativeInterval`] if the current or given interval is relative.
    /// - Returns [`OverlapPositionError::MalformedInterval`] if the current or given interval is malformed in any way
    ///   (e.g. the start time is after the end time)
    pub fn overlap_position(&self, other: &Self) -> Result<OverlapPosition, OverlapPositionError> {
        match (self, other) {
            (Self::ClosedRelative(_) | Self::HalfOpenRelative(_), _)
            | (_, Self::ClosedRelative(_) | Self::HalfOpenRelative(_)) => {
                Err(OverlapPositionError::RelativeInterval)
            }
            (Self::ClosedAbsolute(interval), Self::ClosedAbsolute(other_interval)) => {
                overlap_position_closed_pair(interval, other_interval)
            }
            (Self::ClosedAbsolute(interval), Self::HalfOpenAbsolute(other_interval)) => {
                overlap_position_closed_half_open(interval, other_interval)
            }
            (Self::HalfOpenAbsolute(interval), Self::ClosedAbsolute(other_interval)) => {
                overlap_position_half_open_closed(interval, other_interval)
            }
            (Self::HalfOpenAbsolute(interval), Self::HalfOpenAbsolute(other_interval)) => {
                Ok(overlap_position_half_open_pair(interval, other_interval))
            }
            // empty intervals are not comparable through time as they don't have a specific time frame
            (Self::Empty(_), _) | (_, Self::Empty(_)) => Ok(OverlapPosition::Outside),
            (Self::Open(_), Self::Open(_)) => Ok(OverlapPosition::Equal),
            (Self::Open(_), Self::HalfOpenAbsolute(half_open_interval)) => {
                match half_open_interval.opening_direction() {
                    OpeningDirection::ToPast => Ok(OverlapPosition::InsideAndSameStart),
                    OpeningDirection::ToFuture => Ok(OverlapPosition::InsideAndSameEnd),
                }
            }
            (Self::Open(_), Self::ClosedAbsolute(_)) => Ok(OverlapPosition::Inside),
            (Self::HalfOpenAbsolute(half_open_interval), Self::Open(_)) => {
                match half_open_interval.opening_direction() {
                    OpeningDirection::ToPast => Ok(OverlapPosition::ContainsAndSameStart),
                    OpeningDirection::ToFuture => Ok(OverlapPosition::ContainsAndSameEnd),
                }
            }
            (Self::ClosedAbsolute(_), Self::Open(_)) => Ok(OverlapPosition::Contains),
        }
    }
}

fn containment_position_closed(
    interval: &ClosedAbsoluteInterval,
    time: DateTime<Utc>,
) -> ContainmentPosition {
    match (time.cmp(interval.from()), time.cmp(interval.to())) {
        (Ordering::Less, _) => ContainmentPosition::OutsideBefore,
        (_, Ordering::Greater) => ContainmentPosition::OutsideAfter,
        (Ordering::Equal, _) => ContainmentPosition::OnStart,
        (_, Ordering::Equal) => ContainmentPosition::OnEnd,
        (Ordering::Greater, Ordering::Less) => ContainmentPosition::Inside,
    }
}

fn containment_position_half_open(
    interval: &HalfOpenAbsoluteInterval,
    time: DateTime<Utc>,
) -> ContainmentPosition {
    match (
        time.cmp(interval.reference_time()),
        interval.opening_direction(),
    ) {
        (Ordering::Less, OpeningDirection::ToPast)
        | (Ordering::Greater, OpeningDirection::ToFuture) => ContainmentPosition::Inside,
        (Ordering::Equal, OpeningDirection::ToPast) => ContainmentPosition::OnEnd,
        (Ordering::Greater, OpeningDirection::ToPast) => ContainmentPosition::OutsideAfter,
        (Ordering::Less, OpeningDirection::ToFuture) => ContainmentPosition::OutsideBefore,
        (Ordering::Equal, OpeningDirection::ToFuture) => ContainmentPosition::OnStart,
    }
}

fn overlap_position_closed_pair(
    a: &ClosedAbsoluteInterval,
    b: &ClosedAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if a.from() > a.to() || b.from() > b.to() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let b_from_cmp = (b.from().cmp(a.from()), b.from().cmp(a.to()));
    let b_to_cmp = (b.to().cmp(a.from()), b.to().cmp(a.to()));

    let overlap_position = match (b_from_cmp, b_to_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::OnStart,
        ((_, Ordering::Equal), _) => OverlapPosition::OnEnd,
        ((Ordering::Less, _), (_, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, _), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => OverlapPosition::InsideAndSameStart,
        ((Ordering::Greater, _), (_, Ordering::Equal)) => OverlapPosition::InsideAndSameEnd,
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal,
        ((Ordering::Equal, _), (_, Ordering::Greater)) => OverlapPosition::ContainsAndSameStart,
        ((Ordering::Less, _), (_, Ordering::Equal)) => OverlapPosition::ContainsAndSameEnd,
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    };

    Ok(overlap_position)
}

fn overlap_position_closed_half_open(
    a: &ClosedAbsoluteInterval,
    b: &HalfOpenAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if a.from() > a.to() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let overlap_position = match (
        b.reference_time().cmp(a.from()),
        b.reference_time().cmp(a.to()),
        b.opening_direction(),
    ) {
        (Ordering::Less, _, OpeningDirection::ToPast) => OverlapPosition::OutsideBefore,
        (_, Ordering::Greater, OpeningDirection::ToFuture) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _, OpeningDirection::ToPast) => OverlapPosition::OnStart,
        (_, Ordering::Equal, OpeningDirection::ToFuture) => OverlapPosition::OnEnd,
        (Ordering::Greater, Ordering::Less, OpeningDirection::ToPast) => {
            OverlapPosition::CrossesStart
        }
        (Ordering::Greater, Ordering::Less, OpeningDirection::ToFuture) => {
            OverlapPosition::CrossesEnd
        }
        (Ordering::Equal, _, OpeningDirection::ToFuture) => OverlapPosition::ContainsAndSameStart,
        (_, Ordering::Equal, OpeningDirection::ToPast) => OverlapPosition::ContainsAndSameEnd,
        (Ordering::Less, _, OpeningDirection::ToFuture)
        | (_, Ordering::Greater, OpeningDirection::ToPast) => OverlapPosition::Contains,
    };

    Ok(overlap_position)
}

fn overlap_position_half_open_closed(
    a: &HalfOpenAbsoluteInterval,
    b: &ClosedAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if b.from() > b.to() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let overlap_position = match (
        b.from().cmp(a.reference_time()),
        b.to().cmp(a.reference_time()),
        a.opening_direction(),
    ) {
        (_, Ordering::Less, OpeningDirection::ToFuture) => OverlapPosition::OutsideBefore,
        (Ordering::Greater, _, OpeningDirection::ToPast) => OverlapPosition::OutsideAfter,
        (_, Ordering::Equal, OpeningDirection::ToFuture) => OverlapPosition::OnStart,
        (Ordering::Equal, _, OpeningDirection::ToPast) => OverlapPosition::OnEnd,
        (Ordering::Less, Ordering::Greater, OpeningDirection::ToFuture) => {
            OverlapPosition::CrossesStart
        }
        (Ordering::Less, Ordering::Greater, OpeningDirection::ToPast) => {
            OverlapPosition::CrossesEnd
        }
        (Ordering::Less, Ordering::Less, OpeningDirection::ToPast)
        | (Ordering::Greater, Ordering::Greater, OpeningDirection::ToFuture) => {
            OverlapPosition::Inside
        }
        (Ordering::Equal, Ordering::Greater, OpeningDirection::ToFuture) => {
            OverlapPosition::InsideAndSameStart
        }
        (Ordering::Less, Ordering::Equal, OpeningDirection::ToPast) => {
            OverlapPosition::InsideAndSameEnd
        }
    };

    Ok(overlap_position)
}

fn overlap_position_half_open_pair(
    a: &HalfOpenAbsoluteInterval,
    b: &HalfOpenAbsoluteInterval,
) -> OverlapPosition {
    match (
        b.reference_time().cmp(a.reference_time()),
        a.opening_direction(),
        b.opening_direction(),
    ) {
        (Ordering::Less, OpeningDirection::ToPast, OpeningDirection::ToPast) => {
            OverlapPosition::InsideAndSameStart
        }
        (Ordering::Less, OpeningDirection::ToPast, OpeningDirection::ToFuture) => {
            OverlapPosition::CrossesEnd
        }
        (Ordering::Less, OpeningDirection::ToFuture, OpeningDirection::ToPast) => {
            OverlapPosition::OutsideBefore
        }
        (Ordering::Less, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => {
            OverlapPosition::ContainsAndSameEnd
        }
        (Ordering::Equal, OpeningDirection::ToPast, OpeningDirection::ToPast)
        | (Ordering::Equal, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => {
            OverlapPosition::Equal
        }
        (Ordering::Equal, OpeningDirection::ToPast, OpeningDirection::ToFuture) => {
            OverlapPosition::OnEnd
        }
        (Ordering::Equal, OpeningDirection::ToFuture, OpeningDirection::ToPast) => {
            OverlapPosition::OnStart
        }
        (Ordering::Greater, OpeningDirection::ToPast, OpeningDirection::ToPast) => {
            OverlapPosition::ContainsAndSameStart
        }
        (Ordering::Greater, OpeningDirection::ToPast, OpeningDirection::ToFuture) => {
            OverlapPosition::OutsideAfter
        }
        (Ordering::Greater, OpeningDirection::ToFuture, OpeningDirection::ToPast) => {
            OverlapPosition::CrossesStart
        }
        (Ordering::Greater, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => {
            OverlapPosition::InsideAndSameEnd
        }
    }
}

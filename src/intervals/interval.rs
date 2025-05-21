use chrono::{DateTime, Duration, Utc};

use super::meta::{Duration as IntervalDuration, OpeningDirection, Openness, Relativity};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedAbsoluteInterval {
    from: DateTime<Utc>,
    to: DateTime<Utc>,
}

impl ClosedAbsoluteInterval {
    #[must_use]
    pub fn new(from: DateTime<Utc>, to: DateTime<Utc>) -> Self {
        ClosedAbsoluteInterval { from, to }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedRelativeInterval {
    offset: Duration,
    length: Duration,
}

impl ClosedRelativeInterval {
    #[must_use]
    pub fn new(offset: Duration, length: Duration) -> Self {
        ClosedRelativeInterval { offset, length }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfOpenAbsoluteInterval {
    reference_time: DateTime<Utc>,
    opening_direction: OpeningDirection,
}

impl HalfOpenAbsoluteInterval {
    #[must_use]
    pub fn new(reference_time: DateTime<Utc>, opening_direction: OpeningDirection) -> Self {
        HalfOpenAbsoluteInterval {
            reference_time,
            opening_direction,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfOpenRelativeInterval {
    offset: Duration,
    opening_direction: OpeningDirection,
}

impl HalfOpenRelativeInterval {
    #[must_use]
    pub fn new(offset: Duration, opening_direction: OpeningDirection) -> Self {
        HalfOpenRelativeInterval {
            offset,
            opening_direction,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenInterval;

/// No interval
///
/// Equivalent to the [empty set](https://en.wikipedia.org/wiki/Empty_set), this allows for still performing
/// operations such as the complement of the interval without issues.
///
/// In regards to operations such as the overlap position, an empty interval has no defined place,
/// it simply represents the _lack_ of a time interval, like the complement of an open interval
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmptyInterval;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Interval {
    ClosedAbsolute(ClosedAbsoluteInterval),
    ClosedRelative(ClosedRelativeInterval),
    HalfOpenAbsolute(HalfOpenAbsoluteInterval),
    HalfOpenRelative(HalfOpenRelativeInterval),
    Open(OpenInterval),
    Empty(EmptyInterval),
}

impl Interval {
    /// Returns the openness of the interval, if possible
    ///
    /// Since an empty time interval doesn't have a defined openness, it will return [`None`]
    #[must_use]
    pub fn openness(&self) -> Option<Openness> {
        match self {
            Self::ClosedAbsolute(_) | Self::ClosedRelative(_) => Some(Openness::Closed),
            Self::HalfOpenAbsolute(_) | Self::HalfOpenRelative(_) => Some(Openness::HalfOpen),
            Self::Open(_) => Some(Openness::Open),
            Self::Empty(_) => None,
        }
    }

    /// Returns the relativity of the interval, if possible
    ///
    /// Since neither an open time interval nor an empty one have a defined relativity, it will return [`None`]
    #[must_use]
    pub fn relativity(&self) -> Option<Relativity> {
        match self {
            Self::ClosedAbsolute(_) | Self::HalfOpenAbsolute(_) => Some(Relativity::Absolute),
            Self::ClosedRelative(_) | Self::HalfOpenRelative(_) => Some(Relativity::Relative),
            Self::Open(_) | Self::Empty(_) => None,
        }
    }

    /// Returns the duration of the time interval, finite or infinite.
    #[must_use]
    pub fn duration(&self) -> IntervalDuration {
        match self {
            Self::ClosedAbsolute(ClosedAbsoluteInterval { from, to }) => {
                IntervalDuration::Finite(*to - from)
            }
            Self::ClosedRelative(ClosedRelativeInterval { offset: _, length }) => {
                IntervalDuration::Finite(*length)
            }
            Self::HalfOpenAbsolute(_) | Self::HalfOpenRelative(_) | Self::Open(_) => {
                IntervalDuration::Infinite
            }
            Self::Empty(_) => IntervalDuration::Finite(Duration::zero()),
        }
    }

    /// Creates a relative clone of the current time interval, given a reference time
    ///
    /// If the current time interval is already relative or has undefined relativity, it just returns a clone of itself.
    #[must_use]
    pub fn to_relative(&self, reference_time: &DateTime<Utc>) -> Self {
        match self {
            Self::ClosedAbsolute(ClosedAbsoluteInterval { from, to }) => Self::ClosedRelative(
                ClosedRelativeInterval::new(*from - reference_time, *to - reference_time),
            ),
            Self::HalfOpenAbsolute(HalfOpenAbsoluteInterval {
                reference_time: og_reference_time,
                opening_direction,
            }) => Self::HalfOpenRelative(HalfOpenRelativeInterval::new(
                *og_reference_time - reference_time,
                *opening_direction,
            )),
            _ => self.clone(),
        }
    }

    /// Creates an absolute clone of the current time interval, given a reference time
    ///
    /// If the current time interval is already absolute or has undefined relativity, it just returns a clone of itself
    #[must_use]
    pub fn to_absolute(&self, reference_time: &DateTime<Utc>) -> Self {
        match self {
            Self::ClosedRelative(ClosedRelativeInterval { offset, length }) => {
                Self::ClosedAbsolute(ClosedAbsoluteInterval::new(
                    *reference_time + *offset,
                    *reference_time + *offset + *length,
                ))
            }
            Self::HalfOpenRelative(HalfOpenRelativeInterval {
                offset,
                opening_direction,
            }) => Self::HalfOpenAbsolute(HalfOpenAbsoluteInterval::new(
                *reference_time + *offset,
                *opening_direction,
            )),
            _ => self.clone(),
        }
    }
}

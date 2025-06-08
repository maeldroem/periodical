use chrono::{DateTime, Duration, Utc};

use super::meta::{Duration as IntervalDuration, OpeningDirection, Openness, Relativity};

/// A closed absolute interval
///
/// Interval set with absolute time, with a defined start and end
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedAbsoluteInterval {
    from: DateTime<Utc>,
    to: DateTime<Utc>,
}

impl ClosedAbsoluteInterval {
    /// Creates a new instance of a closed absolute interval
    #[must_use]
    pub fn new(from: DateTime<Utc>, to: DateTime<Utc>) -> Self {
        ClosedAbsoluteInterval { from, to }
    }

    /// Returns a reference to the start time
    #[must_use]
    pub fn from(&self) -> &DateTime<Utc> {
        &self.from
    }

    /// Returns a reference to the end time
    #[must_use]
    pub fn to(&self) -> &DateTime<Utc> {
        &self.to
    }

    /// Returns a mutable reference to the start time
    #[must_use]
    pub fn from_mut(&mut self) -> &mut DateTime<Utc> {
        &mut self.from
    }

    /// Returns a mutable reference to the end time
    #[must_use]
    pub fn to_mut(&mut self) -> &mut DateTime<Utc> {
        &mut self.to
    }
}

/// A closed relative interval
///
/// An interval set with relative time, with a defined start and end
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedRelativeInterval {
    offset: Duration,
    length: Duration,
}

impl ClosedRelativeInterval {
    /// Creates a new instance of a closed relative interval
    #[must_use]
    pub fn new(offset: Duration, length: Duration) -> Self {
        ClosedRelativeInterval { offset, length }
    }

    /// Returns a reference to the offset
    #[must_use]
    pub fn offset(&self) -> &Duration {
        &self.offset
    }

    /// Returns a reference to the length
    #[must_use]
    pub fn length(&self) -> &Duration {
        &self.length
    }

    /// Returns a mutable reference to the offset
    #[must_use]
    pub fn offset_mut(&mut self) -> &mut Duration {
        &mut self.offset
    }

    /// Returns a mutable reference to the length
    #[must_use]
    pub fn length_mut(&mut self) -> &mut Duration {
        &mut self.length
    }
}

/// A half-open absolute interval
///
/// An interval set with absolute time, has a defined reference time and an opening direction (only one defined bound).
/// Infinite duration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfOpenAbsoluteInterval {
    reference_time: DateTime<Utc>,
    opening_direction: OpeningDirection,
}

impl HalfOpenAbsoluteInterval {
    /// Creates a new instance of a half-open absolute interval
    #[must_use]
    pub fn new(reference_time: DateTime<Utc>, opening_direction: OpeningDirection) -> Self {
        HalfOpenAbsoluteInterval {
            reference_time,
            opening_direction,
        }
    }

    /// Returns a reference to the reference time
    #[must_use]
    pub fn reference_time(&self) -> &DateTime<Utc> {
        &self.reference_time
    }

    /// Returns the opening direction of the interval
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns a mutable reference to the reference time
    #[must_use]
    pub fn reference_time_mut(&mut self) -> &mut DateTime<Utc> {
        &mut self.reference_time
    }
}

/// A half-open relative interval
///
/// An interval set with relative time, has a relative reference time (offset) and an opening direction.
/// Infinite duration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfOpenRelativeInterval {
    offset: Duration,
    opening_direction: OpeningDirection,
}

impl HalfOpenRelativeInterval {
    /// Creates a new instance of a half-open relative interval
    #[must_use]
    pub fn new(offset: Duration, opening_direction: OpeningDirection) -> Self {
        HalfOpenRelativeInterval {
            offset,
            opening_direction,
        }
    }

    /// Returns a reference to the offset
    #[must_use]
    pub fn offset(&self) -> &Duration {
        &self.offset
    }

    /// Returns the opening direction of the interval
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns a mutable reference to the offset
    #[must_use]
    pub fn offset_mut(&mut self) -> &mut Duration {
        &mut self.offset
    }
}

/// An open interval
///
/// Interval without relativity (not absolute nor relative) and without any bounds.
/// Is equivalent to _time itself_ (all time), infinite duration.
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

impl From<ClosedAbsoluteInterval> for Interval {
    fn from(value: ClosedAbsoluteInterval) -> Self {
        Interval::ClosedAbsolute(value)
    }
}

impl From<ClosedRelativeInterval> for Interval {
    fn from(value: ClosedRelativeInterval) -> Self {
        Interval::ClosedRelative(value)
    }
}

impl From<HalfOpenAbsoluteInterval> for Interval {
    fn from(value: HalfOpenAbsoluteInterval) -> Self {
        Interval::HalfOpenAbsolute(value)
    }
}

impl From<HalfOpenRelativeInterval> for Interval {
    fn from(value: HalfOpenRelativeInterval) -> Self {
        Interval::HalfOpenRelative(value)
    }
}

impl From<OpenInterval> for Interval {
    fn from(value: OpenInterval) -> Self {
        Interval::Open(value)
    }
}

impl From<EmptyInterval> for Interval {
    fn from(value: EmptyInterval) -> Self {
        Interval::Empty(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::datetime;

    fn interval_openness_provider() -> Vec<(Interval, Option<Openness>)> {
        vec![
            (
                // Interval
                Interval::ClosedAbsolute(ClosedAbsoluteInterval::new(
                    datetime(&Utc, 2025, 1, 1, 8, 0, 0),
                    datetime(&Utc, 2025, 1, 1, 16, 0, 0),
                )),
                // Expected
                Some(Openness::Closed),
            ),
            (
                Interval::ClosedRelative(ClosedRelativeInterval::new(
                    Duration::hours(8),
                    Duration::hours(8),
                )),
                Some(Openness::Closed),
            ),
            (
                Interval::HalfOpenAbsolute(HalfOpenAbsoluteInterval::new(
                    datetime(&Utc, 2025, 1, 1, 8, 0, 0),
                    OpeningDirection::ToFuture,
                )),
                Some(Openness::HalfOpen),
            ),
            (
                Interval::HalfOpenRelative(HalfOpenRelativeInterval::new(
                    Duration::hours(8),
                    OpeningDirection::ToPast,
                )),
                Some(Openness::HalfOpen),
            ),
            (Interval::Open(OpenInterval), Some(Openness::Open)),
            (Interval::Empty(EmptyInterval), None),
        ]
    }

    fn interval_relativity_provider() -> Vec<(Interval, Option<Relativity>)> {
        vec![
            (
                // Interval
                Interval::ClosedAbsolute(ClosedAbsoluteInterval::new(
                    datetime(&Utc, 2025, 1, 1, 8, 0, 0),
                    datetime(&Utc, 2025, 1, 1, 16, 0, 0),
                )),
                // Expected
                Some(Relativity::Absolute),
            ),
            (
                Interval::ClosedRelative(ClosedRelativeInterval::new(
                    Duration::hours(8),
                    Duration::hours(8),
                )),
                Some(Relativity::Relative),
            ),
            (
                Interval::HalfOpenAbsolute(HalfOpenAbsoluteInterval::new(
                    datetime(&Utc, 2025, 1, 1, 8, 0, 0),
                    OpeningDirection::ToFuture,
                )),
                Some(Relativity::Absolute),
            ),
            (
                Interval::HalfOpenRelative(HalfOpenRelativeInterval::new(
                    Duration::hours(8),
                    OpeningDirection::ToPast,
                )),
                Some(Relativity::Relative),
            ),
            (Interval::Open(OpenInterval), None),
            (Interval::Empty(EmptyInterval), None),
        ]
    }

    #[test]
    fn interval_openness() {
        for (interval, expected) in interval_openness_provider() {
            assert_eq!(interval.openness(), expected);
        }
    }

    #[test]
    fn interval_relativity() {
        for (interval, expected) in interval_relativity_provider() {
            assert_eq!(interval.relativity(), expected);
        }
    }
}

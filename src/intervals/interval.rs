//! Intervals
//!
//! The core of intervals is implemented here. You will find the implementations for each different variant
//! of intervals, but also find how the principal structure, [`Interval`] works.

use chrono::{DateTime, Duration, RoundingError, Utc};

use crate::intervals::ops::Precision;

use super::meta::{BoundInclusivity, Duration as IntervalDuration, OpeningDirection, Openness, Relativity};

pub enum AbsoluteIntervalBound {
    Finite(DateTime<Utc>, BoundInclusivity),
    InfinitePast,
    InfiniteFuture,
}

pub enum RelativeIntervalBound {
    Finite(Duration, BoundInclusivity),
    InfinitePast,
    InfiniteFuture,
}

/// A closed absolute interval
///
/// Interval set with absolute time, with a defined start and end
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedAbsoluteInterval {
    pub(super) from: DateTime<Utc>,
    pub(super) to: DateTime<Utc>,
    pub(super) from_inclusivity: BoundInclusivity,
    pub(super) to_inclusivity: BoundInclusivity,
}

impl ClosedAbsoluteInterval {
    /// Creates a new instance of a closed absolute interval
    #[must_use]
    pub fn new(from: DateTime<Utc>, to: DateTime<Utc>) -> Self {
        ClosedAbsoluteInterval {
            from,
            to,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a closed absolute interval with given inclusivity for the bounds
    #[must_use]
    pub fn with_inclusivity(
        from: DateTime<Utc>,
        from_inclusivity: BoundInclusivity,
        to: DateTime<Utc>,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        ClosedAbsoluteInterval {
            from,
            to,
            from_inclusivity,
            to_inclusivity,
        }
    }

    /// Returns the start time
    #[must_use]
    pub fn from(&self) -> DateTime<Utc> {
        self.from
    }

    /// Returns the end time
    #[must_use]
    pub fn to(&self) -> DateTime<Utc> {
        self.to
    }

    /// Tries to return the start time rounded with the given precision
    ///
    /// # Errors
    ///
    /// See [`Precision::try_precise_time`]
    pub fn try_from_with_precision(&self, precision: Precision) -> Result<DateTime<Utc>, RoundingError> {
        precision.try_precise_time(self.from)
    }

    /// Tries to return the start time rounded with the given precision
    ///
    /// # Errors
    ///
    /// See [`Precision::try_precise_time`]
    pub fn try_to_with_precision(&self, precision: Precision) -> Result<DateTime<Utc>, RoundingError> {
        precision.try_precise_time(self.to)
    }

    /// Returns the inclusivity of the start bound
    #[must_use]
    pub fn from_inclusivity(&self) -> BoundInclusivity {
        self.from_inclusivity
    }

    /// Returns the inclusivity of the end bound
    #[must_use]
    pub fn to_inclusivity(&self) -> BoundInclusivity {
        self.to_inclusivity
    }

    /// Returns whether the interval is malformed
    ///
    /// The interval is considered malformed if the from time is past the to time.
    #[must_use]
    pub fn is_malformed(&self) -> bool {
        self.from > self.to
    }

    /// Sets the from time of the interval
    pub fn set_from(&mut self, new_from: DateTime<Utc>) {
        self.from = new_from;
    }

    /// Sets the to time of the interval
    pub fn set_to(&mut self, new_to: DateTime<Utc>) {
        self.to = new_to;
    }

    /// Sets the inclusivity of the start bound
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.from_inclusivity = new_inclusivity;
    }

    /// Sets the inclusivity of the end bound
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.to_inclusivity = new_inclusivity;
    }
}

pub enum ClosedAbsoluteIntervalConversionErr {
    WrongVariant,
}

impl TryFrom<AbsoluteInterval> for ClosedAbsoluteInterval {
    type Error = ClosedAbsoluteIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Closed(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<ClosedInterval> for ClosedAbsoluteInterval {
    type Error = ClosedAbsoluteIntervalConversionErr;

    fn try_from(value: ClosedInterval) -> Result<Self, Self::Error> {
        match value {
            ClosedInterval::Absolute(interval) => Ok(interval),
            ClosedInterval::Relative(_) => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<Interval> for ClosedAbsoluteInterval {
    type Error = ClosedAbsoluteIntervalConversionErr;

    fn try_from(value: Interval) -> Result<Self, Self::Error> {
        match value {
            Interval::ClosedAbsolute(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// A closed relative interval
///
/// An interval set with relative time, with a defined start and end
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedRelativeInterval {
    pub(super) offset: Duration,
    pub(super) length: Duration,
    pub(super) from_inclusivity: BoundInclusivity,
    pub(super) to_inclusivity: BoundInclusivity,
}

impl ClosedRelativeInterval {
    /// Creates a new instance of a closed relative interval
    #[must_use]
    pub fn new(offset: Duration, length: Duration) -> Self {
        ClosedRelativeInterval {
            offset,
            length,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a closed relative interval with given inclusivity for the bounds
    #[must_use]
    pub fn with_inclusivity(
        offset: Duration,
        start_inclusivity: BoundInclusivity,
        length: Duration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        ClosedRelativeInterval {
            offset,
            length,
            from_inclusivity: start_inclusivity,
            to_inclusivity: end_inclusivity,
        }
    }

    /// Returns the offset of the interval
    #[must_use]
    pub fn offset(&self) -> Duration {
        self.offset
    }

    /// Returns the length of the interval
    #[must_use]
    pub fn length(&self) -> Duration {
        self.length
    }

    /// Returns the inclusivity of the start bound
    #[must_use]
    pub fn from_inclusivity(&self) -> BoundInclusivity {
        self.from_inclusivity
    }

    /// Returns the inclusivity of the end bound
    #[must_use]
    pub fn to_inclusivity(&self) -> BoundInclusivity {
        self.to_inclusivity
    }

    /// Sets the offset of the interval
    pub fn set_offset(&mut self, new_offset: Duration) {
        self.offset = new_offset;
    }

    /// Sets the length of the interval
    pub fn set_length(&mut self, new_length: Duration) {
        self.length = new_length;
    }

    /// Sets the inclusivity of the start bound
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.from_inclusivity = new_inclusivity;
    }

    /// Sets the inclusivity of the end bound
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.to_inclusivity = new_inclusivity;
    }
}

pub enum ClosedRelativeIntervalConversionErr {
    WrongVariant,
}

impl TryFrom<RelativeInterval> for ClosedRelativeInterval {
    type Error = ClosedRelativeIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Closed(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<ClosedInterval> for ClosedRelativeInterval {
    type Error = ClosedRelativeIntervalConversionErr;

    fn try_from(value: ClosedInterval) -> Result<Self, Self::Error> {
        match value {
            ClosedInterval::Relative(interval) => Ok(interval),
            ClosedInterval::Absolute(_) => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<Interval> for ClosedRelativeInterval {
    type Error = ClosedRelativeIntervalConversionErr;

    fn try_from(value: Interval) -> Result<Self, Self::Error> {
        match value {
            Interval::ClosedRelative(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// A half-open absolute interval
///
/// An interval set with absolute time, has a defined reference time and an opening direction (only one defined bound).
/// Infinite duration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfOpenAbsoluteInterval {
    pub(super) reference_time: DateTime<Utc>,
    pub(super) opening_direction: OpeningDirection,
    pub(super) reference_time_inclusivity: BoundInclusivity,
}

impl HalfOpenAbsoluteInterval {
    /// Creates a new instance of a half-open absolute interval
    #[must_use]
    pub fn new(reference_time: DateTime<Utc>, opening_direction: OpeningDirection) -> Self {
        HalfOpenAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_time_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a half-open absolute interval with given inclusivity for the bound
    #[must_use]
    pub fn with_inclusivity(
        reference_time: DateTime<Utc>,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfOpenAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_time_inclusivity,
        }
    }

    /// Returns the reference time of the interval
    #[must_use]
    pub fn reference_time(&self) -> DateTime<Utc> {
        self.reference_time
    }

    /// Tries to return the reference time with the given precision
    ///
    /// # Errors
    ///
    /// See [`Precision::try_precise_time`]
    pub fn try_reference_time_with_precision(&self, precision: Precision) -> Result<DateTime<Utc>, RoundingError> {
        precision.try_precise_time(self.reference_time)
    }

    /// Returns the opening direction of the interval
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference time
    #[must_use]
    pub fn reference_time_inclusivity(&self) -> BoundInclusivity {
        self.reference_time_inclusivity
    }

    /// Sets the reference time of the interval
    pub fn set_reference_time(&mut self, new_reference_time: DateTime<Utc>) {
        self.reference_time = new_reference_time;
    }

    /// Sets the inclusivity of the reference time
    pub fn set_reference_time_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_time_inclusivity = new_inclusivity;
    }
}

pub enum HalfOpenAbsoluteIntervalConversionErr {
    WrongVariant,
}

impl TryFrom<AbsoluteInterval> for HalfOpenAbsoluteInterval {
    type Error = HalfOpenAbsoluteIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::HalfOpen(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<HalfOpenInterval> for HalfOpenAbsoluteInterval {
    type Error = HalfOpenAbsoluteIntervalConversionErr;

    fn try_from(value: HalfOpenInterval) -> Result<Self, Self::Error> {
        match value {
            HalfOpenInterval::Absolute(interval) => Ok(interval),
            HalfOpenInterval::Relative(_) => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<Interval> for HalfOpenAbsoluteInterval {
    type Error = HalfOpenAbsoluteIntervalConversionErr;

    fn try_from(value: Interval) -> Result<Self, Self::Error> {
        match value {
            Interval::HalfOpenAbsolute(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// A half-open relative interval
///
/// An interval set with relative time, has a relative reference time (offset) and an opening direction.
/// Infinite duration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfOpenRelativeInterval {
    pub(super) offset: Duration,
    pub(super) opening_direction: OpeningDirection,
    pub(super) reference_time_inclusivity: BoundInclusivity,
}

impl HalfOpenRelativeInterval {
    /// Creates a new instance of a half-open relative interval
    #[must_use]
    pub fn new(offset: Duration, opening_direction: OpeningDirection) -> Self {
        HalfOpenRelativeInterval {
            offset,
            opening_direction,
            reference_time_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a half-open relative interval with given inclusivity for the bound
    #[must_use]
    pub fn with_inclusivity(
        offset: Duration,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfOpenRelativeInterval {
            offset,
            opening_direction,
            reference_time_inclusivity,
        }
    }

    /// Returns the offset of the interval
    #[must_use]
    pub fn offset(&self) -> Duration {
        self.offset
    }

    /// Returns the opening direction of the interval
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference time
    #[must_use]
    pub fn reference_time_inclusivity(&self) -> BoundInclusivity {
        self.reference_time_inclusivity
    }

    /// Sets the offset of the interval
    pub fn set_offset(&mut self, new_offset: Duration) {
        self.offset = new_offset;
    }

    /// Sets the inclusivity of the reference time
    pub fn set_reference_time_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_time_inclusivity = new_inclusivity;
    }
}

pub enum HalfOpenRelativeIntervalConversionErr {
    WrongVariant,
}

impl TryFrom<RelativeInterval> for HalfOpenRelativeInterval {
    type Error = HalfOpenRelativeIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::HalfOpen(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<HalfOpenInterval> for HalfOpenRelativeInterval {
    type Error = HalfOpenRelativeIntervalConversionErr;

    fn try_from(value: HalfOpenInterval) -> Result<Self, Self::Error> {
        match value {
            HalfOpenInterval::Relative(interval) => Ok(interval),
            HalfOpenInterval::Absolute(_) => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<Interval> for HalfOpenRelativeInterval {
    type Error = HalfOpenRelativeIntervalConversionErr;

    fn try_from(value: Interval) -> Result<Self, Self::Error> {
        match value {
            Interval::HalfOpenRelative(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// An open interval
///
/// Interval without relativity (not absolute nor relative) and without any bounds.
/// Is equivalent to _time itself_ (all time), infinite duration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenInterval;

pub enum OpenIntervalConversionErr {
    WrongVariant,
}

impl TryFrom<AbsoluteInterval> for OpenInterval {
    type Error = OpenIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Open(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<RelativeInterval> for OpenInterval {
    type Error = OpenIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Open(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<Interval> for OpenInterval {
    type Error = OpenIntervalConversionErr;

    fn try_from(value: Interval) -> Result<Self, Self::Error> {
        match value {
            Interval::Open(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// No interval
///
/// Equivalent to the [empty set](https://en.wikipedia.org/wiki/Empty_set), this allows for still performing
/// operations such as the complement of the interval without issues.
///
/// In regards to operations such as the overlap position, an empty interval has no defined place,
/// it simply represents the _lack_ of a time interval, like the complement of an open interval
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmptyInterval;

pub enum EmptyIntervalConversionErr {
    WrongVariant,
}

impl TryFrom<AbsoluteInterval> for EmptyInterval {
    type Error = EmptyIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Empty(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<RelativeInterval> for EmptyInterval {
    type Error = EmptyIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Empty(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<Interval> for EmptyInterval {
    type Error = EmptyIntervalConversionErr;

    fn try_from(value: Interval) -> Result<Self, Self::Error> {
        match value {
            Interval::Empty(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// Represents any absolute interval, including empty and open intervals
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbsoluteInterval {
    Closed(ClosedAbsoluteInterval),
    HalfOpen(HalfOpenAbsoluteInterval),
    Open(OpenInterval),
    Empty(EmptyInterval),
}

impl From<ClosedAbsoluteInterval> for AbsoluteInterval {
    fn from(value: ClosedAbsoluteInterval) -> Self {
        AbsoluteInterval::Closed(value)
    }
}

impl From<HalfOpenAbsoluteInterval> for AbsoluteInterval {
    fn from(value: HalfOpenAbsoluteInterval) -> Self {
        AbsoluteInterval::HalfOpen(value)
    }
}

impl From<OpenInterval> for AbsoluteInterval {
    fn from(value: OpenInterval) -> Self {
        AbsoluteInterval::Open(value)
    }
}

impl From<EmptyInterval> for AbsoluteInterval {
    fn from(value: EmptyInterval) -> Self {
        AbsoluteInterval::Empty(value)
    }
}

/// Represents any relative interval, including empty and open interval
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelativeInterval {
    Closed(ClosedRelativeInterval),
    HalfOpen(HalfOpenRelativeInterval),
    Open(OpenInterval),
    Empty(EmptyInterval),
}

impl From<ClosedRelativeInterval> for RelativeInterval {
    fn from(value: ClosedRelativeInterval) -> Self {
        RelativeInterval::Closed(value)
    }
}

impl From<HalfOpenRelativeInterval> for RelativeInterval {
    fn from(value: HalfOpenRelativeInterval) -> Self {
        RelativeInterval::HalfOpen(value)
    }
}

impl From<OpenInterval> for RelativeInterval {
    fn from(value: OpenInterval) -> Self {
        RelativeInterval::Open(value)
    }
}

impl From<EmptyInterval> for RelativeInterval {
    fn from(value: EmptyInterval) -> Self {
        RelativeInterval::Empty(value)
    }
}

/// Represents any closed interval, absolute or relative
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosedInterval {
    Absolute(ClosedAbsoluteInterval),
    Relative(ClosedRelativeInterval),
}

impl From<ClosedAbsoluteInterval> for ClosedInterval {
    fn from(value: ClosedAbsoluteInterval) -> Self {
        ClosedInterval::Absolute(value)
    }
}

impl From<ClosedRelativeInterval> for ClosedInterval {
    fn from(value: ClosedRelativeInterval) -> Self {
        ClosedInterval::Relative(value)
    }
}

/// Represents any half-open interval, absolute or relative
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HalfOpenInterval {
    Absolute(HalfOpenAbsoluteInterval),
    Relative(HalfOpenRelativeInterval),
}

impl From<HalfOpenAbsoluteInterval> for HalfOpenInterval {
    fn from(value: HalfOpenAbsoluteInterval) -> Self {
        HalfOpenInterval::Absolute(value)
    }
}

impl From<HalfOpenRelativeInterval> for HalfOpenInterval {
    fn from(value: HalfOpenRelativeInterval) -> Self {
        HalfOpenInterval::Relative(value)
    }
}

/// Any kind of interval
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
            Self::ClosedAbsolute(ClosedAbsoluteInterval { from, to, .. }) => IntervalDuration::Finite(*to - from),
            Self::ClosedRelative(ClosedRelativeInterval { length, .. }) => IntervalDuration::Finite(*length),
            Self::HalfOpenAbsolute(_) | Self::HalfOpenRelative(_) | Self::Open(_) => IntervalDuration::Infinite,
            Self::Empty(_) => IntervalDuration::Finite(Duration::zero()),
        }
    }

    /// Returns the inclusivity of the start and end bounds
    ///
    /// The first element of the tuple contains the inclusivity of the start bound,
    /// the second contains the inclusivity of the end bound.
    ///
    /// If the concept of inclusivity doesn't apply for a bound (i.e. in case of infinity for the side going to infinity
    /// in the case of half-open intervals, for both bounds for open and empty intervals) then it will be equal to [`None`]
    #[must_use]
    pub fn bounds_inclusivity(&self) -> (Option<BoundInclusivity>, Option<BoundInclusivity>) {
        match self {
            Interval::ClosedAbsolute(ClosedAbsoluteInterval {
                from_inclusivity,
                to_inclusivity,
                ..
            })
            | Interval::ClosedRelative(ClosedRelativeInterval {
                from_inclusivity,
                to_inclusivity,
                ..
            }) => (Some(*from_inclusivity), Some(*to_inclusivity)),
            Interval::HalfOpenAbsolute(HalfOpenAbsoluteInterval {
                reference_time_inclusivity,
                opening_direction,
                ..
            })
            | Interval::HalfOpenRelative(HalfOpenRelativeInterval {
                reference_time_inclusivity,
                opening_direction,
                ..
            }) => match opening_direction {
                OpeningDirection::ToPast => (None, Some(*reference_time_inclusivity)),
                OpeningDirection::ToFuture => (Some(*reference_time_inclusivity), None),
            },
            _ => (None, None),
        }
    }

    /// Creates a relative clone of the current time interval, given a reference time
    ///
    /// If the current time interval is already relative or has undefined relativity, it just returns a clone of itself.
    #[must_use]
    pub fn to_relative(&self, reference_time: &DateTime<Utc>) -> Self {
        match self {
            Self::ClosedAbsolute(ClosedAbsoluteInterval { from, to, .. }) => Self::ClosedRelative(
                ClosedRelativeInterval::new(*from - reference_time, *to - reference_time),
            ),
            Self::HalfOpenAbsolute(HalfOpenAbsoluteInterval {
                reference_time: og_reference_time,
                opening_direction,
                ..
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
            Self::ClosedRelative(ClosedRelativeInterval { offset, length, .. }) => Self::ClosedAbsolute(
                ClosedAbsoluteInterval::new(*reference_time + *offset, *reference_time + *offset + *length),
            ),
            Self::HalfOpenRelative(HalfOpenRelativeInterval {
                offset,
                opening_direction,
                ..
            }) => Self::HalfOpenAbsolute(HalfOpenAbsoluteInterval::new(
                *reference_time + *offset,
                *opening_direction,
            )),
            _ => self.clone(),
        }
    }

    // TODO: Convenience method like today() until_now() after_now() etc.
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

impl From<AbsoluteInterval> for Interval {
    fn from(value: AbsoluteInterval) -> Self {
        match value {
            AbsoluteInterval::Closed(interval) => Interval::ClosedAbsolute(interval),
            AbsoluteInterval::HalfOpen(interval) => Interval::HalfOpenAbsolute(interval),
            AbsoluteInterval::Open(interval) => Interval::Open(interval),
            AbsoluteInterval::Empty(interval) => Interval::Empty(interval),
        }
    }
}

impl From<RelativeInterval> for Interval {
    fn from(value: RelativeInterval) -> Self {
        match value {
            RelativeInterval::Closed(interval) => Interval::ClosedRelative(interval),
            RelativeInterval::HalfOpen(interval) => Interval::HalfOpenRelative(interval),
            RelativeInterval::Open(interval) => Interval::Open(interval),
            RelativeInterval::Empty(interval) => Interval::Empty(interval),
        }
    }
}

impl From<ClosedInterval> for Interval {
    fn from(value: ClosedInterval) -> Self {
        match value {
            ClosedInterval::Absolute(interval) => Interval::ClosedAbsolute(interval),
            ClosedInterval::Relative(interval) => Interval::ClosedRelative(interval),
        }
    }
}

impl From<HalfOpenInterval> for Interval {
    fn from(value: HalfOpenInterval) -> Self {
        match value {
            HalfOpenInterval::Absolute(interval) => Interval::HalfOpenAbsolute(interval),
            HalfOpenInterval::Relative(interval) => Interval::HalfOpenRelative(interval),
        }
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
                Interval::ClosedRelative(ClosedRelativeInterval::new(Duration::hours(8), Duration::hours(8))),
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
                Interval::ClosedRelative(ClosedRelativeInterval::new(Duration::hours(8), Duration::hours(8))),
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

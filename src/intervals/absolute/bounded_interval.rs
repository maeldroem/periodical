//! Absolute bounded interval
//!
//! A bounded interval has a start and end. Like all specific absolute interval
//! types, it conserves the invariant of its bounds being in chronological order
//! and if the bounds have the same time, they must be inclusive.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a bounded interval must remain a bounded
//! interval. It cannot mutate from being a bounded interval to a half-bounded
//! interval.
//!
//! Instead, if you are looking for an absolute interval that doesn't keep the
//! [openness](Openness) invariant, see [`AbsoluteBoundPair`].

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::{Range, RangeInclusive};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteInterval,
    HasAbsoluteBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasBoundInclusivity,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    Openness,
    Relativity,
};

/// A bounded absolute interval
///
/// A bounded interval has a start and end. Like all specific absolute interval
/// types, it conserves the invariant of its bounds being in chronological order
/// and if the bounds have the same time, they must be inclusive.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a bounded interval must remain a bounded
/// interval. It cannot mutate from being a bounded interval to a half-bounded
/// interval.
///
/// Instead, if you are looking for an absolute interval that doesn't keep the
/// [openness](Openness) invariant, see [`AbsoluteBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct BoundedAbsoluteInterval {
    start: Timestamp,
    end: Timestamp,
    start_inclusivity: BoundInclusivity,
    end_inclusivity: BoundInclusivity,
}

impl BoundedAbsoluteInterval {
    /// Creates a new [`BoundedAbsoluteInterval`] without checking if it
    /// violates the invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even though the times are not in chronological order
    /// let bounded_interval = BoundedAbsoluteInterval::unchecked_new(start, end);
    ///
    /// // They remain that way
    /// assert_eq!(bounded_interval.start(), start);
    /// assert_eq!(bounded_interval.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn unchecked_new(start: Timestamp, end: Timestamp) -> Self {
        BoundedAbsoluteInterval {
            start,
            end,
            start_inclusivity: BoundInclusivity::default(),
            end_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with default bound
    /// inclusivities
    ///
    /// If the start time is past the end time, it swaps them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Times that are not in chronological order
    /// let bounded_interval = BoundedAbsoluteInterval::new(start, end);
    ///
    /// // Are swapped
    /// assert_eq!(bounded_interval.start(), end);
    /// assert_eq!(bounded_interval.end(), start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new(mut start: Timestamp, mut end: Timestamp) -> Self {
        if start > end {
            std::mem::swap(&mut start, &mut end);
        }

        Self::unchecked_new(start, end)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with the given bound
    /// inclusivities without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Same time, not doubly inclusive
    /// let bounded_interval = BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
    ///     time,
    ///     BoundInclusivity::Inclusive,
    ///     time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn unchecked_new_with_inclusivity(
        start: Timestamp,
        start_inclusivity: BoundInclusivity,
        end: Timestamp,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        BoundedAbsoluteInterval {
            start,
            end,
            start_inclusivity,
            end_inclusivity,
        }
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with the given bound
    /// inclusivities
    ///
    /// If the given times are not in chronological order, we swap them so they
    /// are in chronological order.
    ///
    /// If the given times are equal but have bound inclusivities other than
    /// inclusive, we set them to
    /// [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Same time, not doubly inclusive
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     time,
    ///     BoundInclusivity::Inclusive,
    ///     time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// // Therefore gets reset to inclusive for both bounds
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        start: Timestamp,
        start_inclusivity: BoundInclusivity,
        end: Timestamp,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        match start.cmp(&end) {
            Ordering::Less => Self::unchecked_new_with_inclusivity(start, start_inclusivity, end, end_inclusivity),
            Ordering::Equal => Self::unchecked_new(start, end),
            Ordering::Greater => Self::unchecked_new_with_inclusivity(end, end_inclusivity, start, start_inclusivity),
        }
    }

    /// Returns the start time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_inclusivity = BoundedAbsoluteInterval::new(start, end);
    ///
    /// assert_eq!(bounded_inclusivity.start(), start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start(&self) -> Timestamp {
        self.start
    }

    /// Returns the end time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_inclusivity = BoundedAbsoluteInterval::new(start, end);
    ///
    /// assert_eq!(bounded_inclusivity.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(&self) -> Timestamp {
        self.end
    }

    /// Returns the inclusivity of the start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     start,
    ///     BoundInclusivity::Exclusive,
    ///     end,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start_inclusivity(&self) -> BoundInclusivity {
        self.start_inclusivity
    }

    /// Returns the inclusivity of the end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     start,
    ///     BoundInclusivity::Exclusive,
    ///     end,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end_inclusivity(&self) -> BoundInclusivity {
        self.end_inclusivity
    }

    /// Sets the start time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(start, end);
    ///
    /// // New start is not in chronological order
    /// let new_start = "2025-01-01 17:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.unchecked_set_start(new_start);
    ///
    /// // And yet is stays that way
    /// assert_eq!(bounded_interval.start(), new_start);
    /// assert_eq!(bounded_interval.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: Timestamp) {
        self.start = new_start;
    }

    /// Sets the end time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(start, end);
    ///
    /// // New end is not in chronological order
    /// let new_end = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.unchecked_set_end(new_end);
    ///
    /// // And yet is stays that way
    /// assert_eq!(bounded_interval.start(), start);
    /// assert_eq!(bounded_interval.end(), new_end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: Timestamp) {
        self.end = new_end;
    }

    /// Sets the start time
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new start time is after the current end time.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new start time would set it on the same time as the end time
    /// without the bound inclusivities being both
    /// [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(start, end);
    ///
    /// let new_start = "2025-01-01 05:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.set_start(new_start)?;
    ///
    /// assert_eq!(bounded_interval.start(), new_start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start(&mut self, new_start: Timestamp) -> Result<(), BoundedAbsoluteIntervalUpdateError> {
        match new_start.cmp(&self.end) {
            Ordering::Less => {
                self.unchecked_set_start(new_start);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity != BoundInclusivity::Inclusive
                    || self.end_inclusivity != BoundInclusivity::Inclusive
                {
                    return Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation);
                }

                self.unchecked_set_start(new_start);
                Ok(())
            },
            Ordering::Greater => Err(BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the end time
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new end time is before the current start time.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new end time would set it on the same time as the start time
    /// without the bound inclusivities being both
    /// [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(start, end);
    ///
    /// let new_end = "2025-01-01 18:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.set_end(new_end)?;
    ///
    /// assert_eq!(bounded_interval.end(), new_end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end(&mut self, new_end: Timestamp) -> Result<(), BoundedAbsoluteIntervalUpdateError> {
        match self.start.cmp(&new_end) {
            Ordering::Less => {
                self.unchecked_set_end(new_end);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity != BoundInclusivity::Inclusive
                    || self.end_inclusivity != BoundInclusivity::Inclusive
                {
                    return Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation);
                }

                self.unchecked_set_end(new_end);
                Ok(())
            },
            Ordering::Greater => Err(BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the start bound's inclusivity without checking if it violates
    /// invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(time, time);
    ///
    /// // Violates the same time doubly inclusive invariant
    /// bounded_interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Yet stays that way
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_start_inclusivity(&mut self, new_start_inclusivity: BoundInclusivity) {
        self.start_inclusivity = new_start_inclusivity;
    }

    /// Sets the end bound's inclusivity without checking if it violates
    /// invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(time, time);
    ///
    /// // Violates the same time doubly inclusive invariant
    /// bounded_interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Yet stays that way
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_end_inclusivity(&mut self, new_end_inclusivity: BoundInclusivity) {
        self.end_inclusivity = new_end_inclusivity;
    }

    /// Sets the start bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the start and end are on the same time and the given new inclusivity
    /// is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// bounded_interval.set_start_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start_inclusivity(
        &mut self,
        new_inclusivity: BoundInclusivity,
    ) -> Result<(), BoundedAbsoluteIntervalUpdateError> {
        if self.start == self.end && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_start_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Sets the end bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the start and end are on the same time and the given new inclusivity
    /// is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// bounded_interval.set_end_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end_inclusivity(
        &mut self,
        new_inclusivity: BoundInclusivity,
    ) -> Result<(), BoundedAbsoluteIntervalUpdateError> {
        if self.start == self.end && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_end_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Wraps the interval in [`AbsoluteInterval`]
    #[must_use]
    pub fn to_interval(self) -> AbsoluteInterval {
        AbsoluteInterval::from(self)
    }

    /// Wraps the interval in [`EmptiableAbsoluteInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableAbsoluteInterval {
        EmptiableAbsoluteInterval::from(self)
    }
}

/// Errors that can occur when creating a new [`BoundedAbsoluteInterval`]
///
/// Those errors are mostly created by convenience methods, such as
/// [`BoundedAbsoluteInterval::today`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalCreationError {
    /// Provided or computed start bound is out of range
    OutOfRangeStart,
    /// Provided or computed end bound is out of range
    OutOfRangeEnd,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for BoundedAbsoluteIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStart => write!(f, "Provided or computed start bound is out of range"),
            Self::OutOfRangeEnd => write!(f, "Provided or computed end bound is out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalCreationError {}

/// Errors that can occur when updating a [`BoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalUpdateError {
    /// Update would violate the chronological order invariant
    ChronologicalOrderViolation,
    /// Update would violate the same time = doubly inclusive invariant
    SameTimeDoublyInclusiveViolation,
}

impl Display for BoundedAbsoluteIntervalUpdateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ChronologicalOrderViolation => write!(f, "Update would violate the chronological order invariant"),
            Self::SameTimeDoublyInclusiveViolation => {
                write!(f, "Update would violate the same time = doubly inclusive invariant")
            },
        }
    }
}

impl Error for BoundedAbsoluteIntervalUpdateError {}

impl Interval for BoundedAbsoluteInterval {}

impl HasOpenness for BoundedAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::Bounded
    }
}

impl HasRelativity for BoundedAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for BoundedAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(
            self.end.duration_since(self.start).unsigned_abs(),
            Epsilon::from((self.start_inclusivity(), self.end_inclusivity())),
        )
    }
}

impl HasAbsoluteBoundPair for BoundedAbsoluteInterval {
    fn abs_bound_pair(&self) -> AbsoluteBoundPair {
        AbsoluteBoundPair::unchecked_new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        AbsoluteFiniteBound::new_with_inclusivity(self.start, self.start_inclusivity).to_start_bound()
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        AbsoluteFiniteBound::new_with_inclusivity(self.end, self.end_inclusivity).to_end_bound()
    }
}

impl From<(Timestamp, Timestamp)> for BoundedAbsoluteInterval {
    fn from((start, end): (Timestamp, Timestamp)) -> Self {
        BoundedAbsoluteInterval::new(start, end)
    }
}

impl From<((Timestamp, BoundInclusivity), (Timestamp, BoundInclusivity))> for BoundedAbsoluteInterval {
    fn from(
        ((start, start_inclusivity), (end, end_inclusivity)): (
            (Timestamp, BoundInclusivity),
            (Timestamp, BoundInclusivity),
        ),
    ) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(start, start_inclusivity, end, end_inclusivity)
    }
}

impl From<Range<Timestamp>> for BoundedAbsoluteInterval {
    fn from(range: Range<Timestamp>) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<Timestamp>> for BoundedAbsoluteInterval {
    fn from(range: RangeInclusive<Timestamp>) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

/// Errors that can occur when trying to convert [`AbsoluteBoundPair`] into
/// [`BoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalFromAbsoluteBoundPairError {
    NotBoundedInterval,
}

impl Display for BoundedAbsoluteIntervalFromAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotBoundedInterval => write!(f, "Not a bounded interval"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalFromAbsoluteBoundPairError {}

impl TryFrom<AbsoluteBoundPair> for BoundedAbsoluteInterval {
    type Error = BoundedAbsoluteIntervalFromAbsoluteBoundPairError;

    fn try_from(value: AbsoluteBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
                Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity(),
                    finite_end.time(),
                    finite_end.inclusivity(),
                ))
            },
            _ => Err(Self::Error::NotBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`AbsoluteInterval`] into
/// [`BoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalFromAbsoluteIntervalError {
    WrongVariant,
}

impl Display for BoundedAbsoluteIntervalFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for BoundedAbsoluteInterval {
    type Error = BoundedAbsoluteIntervalFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Bounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

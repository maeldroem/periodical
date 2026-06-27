//! Absolute bounded interval
//!
//! A bounded interval has a finite start and a finite end.
//! Like all specific interval types, it conserves the invariant of its bounds
//! being in chronological order and if the bounds have the same position, they must be inclusive.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a bounded interval must remain a bounded
//! interval.
//!
//! Instead, if you are looking for an absolute interval that doesn't keep the
//! [openness](Openness) invariant, see [`AbsBoundPair`].

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, Range, RangeBounds, RangeInclusive};
use std::time::Duration as StdDuration;

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
    AbsInterval,
    AbsStartBound,
    AbsStartEndBoundsCheckForIntervalCreationError,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HasAbsBoundPair,
    check_abs_finite_start_end_bounds_for_interval_creation,
    prepare_abs_finite_start_end_bounds_for_interval_creation,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasBoundInclusivity,
    HasDuration,
    HasIntervalTypeWithRel,
    HasOpenness,
    HasRelativity,
    Interval,
    IntervalTypeWithRel,
    IsEmpty,
    Openness,
    Relativity,
};

/// Absolute bounded interval
///
/// A bounded interval has a finite start and a finite end.
/// Like all specific interval types, it conserves the invariant of its bounds
/// being in chronological order and if the bounds have the same position, they must be inclusive.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a bounded interval must remain a bounded
/// interval.
///
/// Instead, if you are looking for an absolute interval that doesn't keep the
/// [openness](Openness) invariant, see [`AbsBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct BoundedAbsInterval {
    start: AbsFiniteStartBound,
    end: AbsFiniteEndBound,
}

impl BoundedAbsInterval {
    /// Creates a new [`BoundedAbsInterval`] without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let start = AbsFiniteBoundPos::new("2026-01-05 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let end =
    ///     AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
    ///
    /// // Even though the times are not in chronological order
    /// let bounded_interval = BoundedAbsInterval::unchecked_new(start, end);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start(), start);
    /// assert_eq!(bounded_interval.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn unchecked_new(start: AbsFiniteStartBound, end: AbsFiniteEndBound) -> Self {
        BoundedAbsInterval {
            start,
            end,
        }
    }

    /// Creates a new [`BoundedAbsInterval`]
    ///
    /// If the bounds are not in chronological order, it swaps them.
    /// If they are on the same position, it makes them both inclusive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let start_pos = AbsFiniteBoundPos::new("2026-01-05 00:00:00Z".parse::<Timestamp>()?);
    /// let end_pos = AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?);
    ///
    /// // Since the times are not in chronological order
    /// let bounded_interval = BoundedAbsInterval::new(
    ///     start_pos.to_finite_start_bound(),
    ///     end_pos.to_finite_end_bound(),
    /// );
    ///
    /// // They are swapped
    /// assert_eq!(bounded_interval.start(), end_pos.to_finite_start_bound());
    /// assert_eq!(bounded_interval.end(), start_pos.to_finite_end_bound());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new(mut start: AbsFiniteStartBound, mut end: AbsFiniteEndBound) -> Self {
        prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

        Self::unchecked_new(start, end)
    }

    /// Creates a new [`BoundedAbsInterval`] from times without checking if it
    /// violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even though the times are not in chronological order
    /// let bounded_interval = BoundedAbsInterval::unchecked_from_times(start, end);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_time(), start);
    /// assert_eq!(bounded_interval.end_time(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn unchecked_from_times(start: Timestamp, end: Timestamp) -> Self {
        Self::unchecked_new(
            AbsFiniteBoundPos::new(start).to_finite_start_bound(),
            AbsFiniteBoundPos::new(end).to_finite_end_bound(),
        )
    }

    /// Creates a new [`BoundedAbsInterval`] from times with default bound
    /// inclusivities
    ///
    /// If the times are not in chronological order, it swaps them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Times that are not in chronological order
    /// let bounded_interval = BoundedAbsInterval::from_times(start, end);
    ///
    /// // Are swapped
    /// assert_eq!(bounded_interval.start_time(), end);
    /// assert_eq!(bounded_interval.end_time(), start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_times(start: Timestamp, end: Timestamp) -> Self {
        Self::new(
            AbsFiniteBoundPos::new(start).to_finite_start_bound(),
            AbsFiniteBoundPos::new(end).to_finite_end_bound(),
        )
    }

    /// Creates a new [`BoundedAbsInterval`] from times and inclusivities without checking
    /// if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even if it violates the same time doubly inclusive invariant
    /// let bounded_interval = BoundedAbsInterval::unchecked_from_times_incl(
    ///     time,
    ///     BoundInclusivity::Inclusive,
    ///     time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_time(), time);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(bounded_interval.end_time(), time);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn unchecked_from_times_incl(
        start: Timestamp,
        start_inclusivity: BoundInclusivity,
        end: Timestamp,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        Self::unchecked_new(
            AbsFiniteBoundPos::new_with_incl(start, start_inclusivity).to_finite_start_bound(),
            AbsFiniteBoundPos::new_with_incl(end, end_inclusivity).to_finite_end_bound(),
        )
    }

    /// Creates a new [`BoundedAbsInterval`] from times and inclusivities
    ///
    /// If the bounds are not in chronological order, it swaps them.
    /// If they are on the same position, it makes them both inclusive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start_time = "2026-01-03 00:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2026-01-05 00:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsInterval::from_times_incl(
    ///     start_time,
    ///     BoundInclusivity::Inclusive,
    ///     end_time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.start_time(), start_time);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(bounded_interval.end_time(), end_time);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_times_incl(
        start: Timestamp,
        start_inclusivity: BoundInclusivity,
        end: Timestamp,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        Self::new(
            AbsFiniteBoundPos::new_with_incl(start, start_inclusivity).to_finite_start_bound(),
            AbsFiniteBoundPos::new_with_incl(end, end_inclusivity).to_finite_end_bound(),
        )
    }

    /// Attempts to create a new [`BoundedAbsInterval`] from a start time and a length
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if `start + length` overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let length = Duration::from_hours(5);
    ///
    /// let bounded_interval = BoundedAbsInterval::from_start_len(start, length)?;
    ///
    /// assert_eq!(bounded_interval.start_time(), start);
    /// assert_eq!(
    ///     bounded_interval.end_time(),
    ///     "2026-01-01 05:00:00Z".parse::<Timestamp>()?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_start_len(start: Timestamp, length: StdDuration) -> Result<Self, BoundedAbsIntervalCreationError> {
        Ok(Self::unchecked_from_times(
            start,
            start
                .checked_add(length)
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?,
        ))
    }

    /// Attempts to create a new [`BoundedAbsInterval`] from a start time, a length, and inclusivities
    /// without checking if it violates invariants
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if `start + length` overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even if it violates the doubly inclusive variant
    /// let bounded_interval = BoundedAbsInterval::unchecked_from_start_len_incl(
    ///     start,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::ZERO,
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_time(), start);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(bounded_interval.end_time(), start);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_from_start_len_incl(
        start: Timestamp,
        start_inclusivity: BoundInclusivity,
        length: StdDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Ok(Self::unchecked_from_times_incl(
            start,
            start_inclusivity,
            start
                .checked_add(length)
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?,
            end_inclusivity,
        ))
    }

    /// Attempts to create a new [`BoundedAbsInterval`] from a start time, a length, and inclusivities
    ///
    /// If the length is zero, then the inclusivities will be set to inclusive.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if `start + length` overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start_time = "2026-01-03 00:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsInterval::from_start_len_incl(
    ///     start_time,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::from_hours(5),
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// assert_eq!(bounded_interval.start_time(), start_time);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_time(),
    ///     "2026-01-03 05:00:00Z".parse::<Timestamp>()?
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_start_len_incl(
        start: Timestamp,
        start_inclusivity: BoundInclusivity,
        length: StdDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        if length.is_zero() {
            return Ok(Self::unchecked_from_times(start, start));
        }

        Self::unchecked_from_start_len_incl(start, start_inclusivity, length, end_inclusivity)
    }

    /// Attempts to create a new [`BoundedAbsInterval`] from an end time and a length
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if `end - length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let end = "2026-01-01 10:00:00Z".parse::<Timestamp>()?;
    /// let length = Duration::from_hours(5);
    ///
    /// let bounded_interval = BoundedAbsInterval::from_end_len(end, length)?;
    ///
    /// assert_eq!(
    ///     bounded_interval.start_time(),
    ///     "2026-01-01 05:00:00Z".parse::<Timestamp>()?
    /// );
    /// assert_eq!(bounded_interval.end_time(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_end_len(end: Timestamp, length: StdDuration) -> Result<Self, BoundedAbsIntervalCreationError> {
        Ok(Self::unchecked_from_times(
            end.checked_sub(length)
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?,
            end,
        ))
    }

    /// Attempts to create a new [`BoundedAbsInterval`] from an end time, a length, and inclusivities
    /// without checking if it violates invariants
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if `end - length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even if it violates the doubly inclusive variant
    /// let bounded_interval = BoundedAbsInterval::unchecked_from_end_len_incl(
    ///     end,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::ZERO,
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_time(), end);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(bounded_interval.end_time(), end);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_from_end_len_incl(
        end: Timestamp,
        end_inclusivity: BoundInclusivity,
        length: StdDuration,
        start_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Ok(Self::unchecked_from_times_incl(
            end.checked_sub(length)
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?,
            start_inclusivity,
            end,
            end_inclusivity,
        ))
    }

    /// Attempts to create a new [`BoundedAbsInterval`] from an end time, a length, and inclusivities
    ///
    /// If the length is zero, then the inclusivities will be set to inclusive.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if `end - length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let end_time = "2026-01-03 10:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsInterval::from_end_len_incl(
    ///     end_time,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::from_hours(5),
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// assert_eq!(
    ///     bounded_interval.start_time(),
    ///     "2026-01-03 05:00:00Z".parse::<Timestamp>()?
    /// );
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(bounded_interval.end_time(), end_time);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_end_len_incl(
        end: Timestamp,
        end_inclusivity: BoundInclusivity,
        length: StdDuration,
        start_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        if length.is_zero() {
            return Ok(Self::unchecked_from_times(end, end));
        }

        Self::unchecked_from_end_len_incl(end, end_inclusivity, length, start_inclusivity)
    }

    /// Attempts to create a [`BoundedAbsInterval`] from a [`Timestamp`] range
    ///
    /// # Errors
    ///
    /// Returns [`BoundedAbsIntervalTryFromRangeError`] if any range bound is [unbounded](Bound::Unbounded).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let interval = BoundedAbsInterval::try_from_range(start..end)?;
    ///
    /// assert_eq!(interval.start_time(), start);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), end);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, BoundedAbsIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        let (start, start_inclusivity) = match range.start_bound() {
            Bound::Included(&time) => (time, BoundInclusivity::Inclusive),
            Bound::Excluded(&time) => (time, BoundInclusivity::Exclusive),
            Bound::Unbounded => return Err(BoundedAbsIntervalTryFromRangeError),
        };

        let (end, end_inclusivity) = match range.end_bound() {
            Bound::Included(&time) => (time, BoundInclusivity::Inclusive),
            Bound::Excluded(&time) => (time, BoundInclusivity::Exclusive),
            Bound::Unbounded => return Err(BoundedAbsIntervalTryFromRangeError),
        };

        Ok(Self::from_times_incl(start, start_inclusivity, end, end_inclusivity))
    }

    /// Returns the finite start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let end =
    ///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
    ///
    /// let interval = BoundedAbsInterval::new(start, end);
    ///
    /// assert_eq!(interval.start(), start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start(&self) -> AbsFiniteStartBound {
        self.start
    }

    /// Returns the finite end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let end =
    ///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
    ///
    /// let interval = BoundedAbsInterval::new(start, end);
    ///
    /// assert_eq!(interval.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(&self) -> AbsFiniteEndBound {
        self.end
    }

    /// Returns the start time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsInterval::from_times(start, end);
    ///
    /// assert_eq!(bounded_interval.start_time(), start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start_time(&self) -> Timestamp {
        self.start().pos().time()
    }

    /// Returns the end time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsInterval::from_times(start, end);
    ///
    /// assert_eq!(bounded_interval.end_time(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end_time(&self) -> Timestamp {
        self.end().pos().time()
    }

    /// Returns the inclusivity of the start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let bounded_interval = BoundedAbsInterval::from_times_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Inclusive,
    ///     "2025-01-01 16:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start_inclusivity(&self) -> BoundInclusivity {
        self.start().pos().inclusivity()
    }

    /// Returns the inclusivity of the end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let bounded_interval = BoundedAbsInterval::from_times_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Inclusive,
    ///     "2025-01-01 16:00:00Z".parse::<Timestamp>()?,
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
        self.end().pos().inclusivity()
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// let new_start_time = "2026-01-01 18:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even if the new start time violates the chronological order invariant
    /// bounded_interval
    ///     .unchecked_set_start(AbsFiniteBoundPos::new(new_start_time).to_finite_start_bound());
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_time(), new_start_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: AbsFiniteStartBound) {
        self.start = new_start;
    }

    /// Sets the start bound
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new start bound violates the chronological order invariant.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new start bound violates the same time doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// let new_start_time = "2026-01-01 10:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.set_start(AbsFiniteBoundPos::new(new_start_time).to_finite_start_bound())?;
    ///
    /// assert_eq!(bounded_interval.start_time(), new_start_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start(&mut self, new_start: AbsFiniteStartBound) -> Result<(), BoundedAbsIntervalUpdateError> {
        check_abs_finite_start_end_bounds_for_interval_creation(&new_start, &self.end()).map_err(|err| match err {
            AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd => {
                BoundedAbsIntervalUpdateError::ChronologicalOrderViolation
            },
            AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive => {
                BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation
            },
        })?;

        self.unchecked_set_start(new_start);
        Ok(())
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// let new_end_time = "2026-01-01 06:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even if the new end time violates the chronological order invariant
    /// bounded_interval.unchecked_set_end(AbsFiniteBoundPos::new(new_end_time).to_finite_end_bound());
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.end_time(), new_end_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: AbsFiniteEndBound) {
        self.end = new_end;
    }

    /// Sets the end bound
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new end bound violates the chronological order invariant.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new end bound violates the same time doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, BoundedAbsInterval};
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// let new_end_time = "2026-01-01 10:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.set_end(AbsFiniteBoundPos::new(new_end_time).to_finite_end_bound())?;
    ///
    /// assert_eq!(bounded_interval.end_time(), new_end_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end(&mut self, new_end: AbsFiniteEndBound) -> Result<(), BoundedAbsIntervalUpdateError> {
        check_abs_finite_start_end_bounds_for_interval_creation(&self.start(), &new_end).map_err(|err| match err {
            AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd => {
                BoundedAbsIntervalUpdateError::ChronologicalOrderViolation
            },
            AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive => {
                BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation
            },
        })?;

        self.unchecked_set_end(new_end);
        Ok(())
    }

    /// Sets the start time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsInterval::from_times(start_time, end_time);
    ///
    /// let new_start_time = "2025-01-01 17:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even if the new start time violates the chronological order invariant
    /// bounded_interval.unchecked_set_start_time(new_start_time);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_time(), new_start_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_start_time(&mut self, new_start_time: Timestamp) {
        self.start.pos_mut().set_time(new_start_time);
    }

    /// Sets the start time
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new start time violates the chronological order invariant.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new start time violates the same time doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsInterval::from_times(start_time, end_time);
    ///
    /// let new_start_time = "2025-01-01 05:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.set_start_time(new_start_time)?;
    ///
    /// assert_eq!(bounded_interval.start_time(), new_start_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start_time(&mut self, new_start_time: Timestamp) -> Result<(), BoundedAbsIntervalUpdateError> {
        match new_start_time.cmp(&self.end_time()) {
            Ordering::Less => {
                self.unchecked_set_start_time(new_start_time);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity() != BoundInclusivity::Inclusive
                    || self.end_inclusivity() != BoundInclusivity::Inclusive
                {
                    return Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation);
                }

                self.unchecked_set_start_time(new_start_time);
                Ok(())
            },
            Ordering::Greater => Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the end time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsInterval::from_times(start_time, end_time);
    ///
    /// let new_end_time = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even if the new end time violates the chronological order invariant
    /// bounded_interval.unchecked_set_end_time(new_end_time);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.end_time(), new_end_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_end_time(&mut self, new_end_time: Timestamp) {
        self.end.pos_mut().set_time(new_end_time);
    }

    /// Sets the end time
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new end time violates the chronological order invariant.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new end time violates the same time doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsInterval::from_times(start_time, end_time);
    ///
    /// let new_end_time = "2025-01-01 18:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.set_end_time(new_end_time)?;
    ///
    /// assert_eq!(bounded_interval.end_time(), new_end_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end_time(&mut self, new_end_time: Timestamp) -> Result<(), BoundedAbsIntervalUpdateError> {
        match self.start_time().cmp(&new_end_time) {
            Ordering::Less => {
                self.unchecked_set_end_time(new_end_time);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity() != BoundInclusivity::Inclusive
                    || self.end_inclusivity() != BoundInclusivity::Inclusive
                {
                    return Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation);
                }

                self.unchecked_set_end_time(new_end_time);
                Ok(())
            },
            Ordering::Greater => Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the length starting from the start bound
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the given length is zero and the start and end bounds are not
    /// both [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// Returns [`OutOfRange`](BoundedAbsIntervalUpdateError::OutOfRange)
    /// if the given length would result in an out-of-range end time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// bounded_interval.set_length_from_start(Duration::from_hours(10))?;
    ///
    /// assert_eq!(
    ///     bounded_interval.end_time(),
    ///     "2026-01-01 18:00:00Z".parse::<Timestamp>()?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_length_from_start(&mut self, new_length: StdDuration) -> Result<(), BoundedAbsIntervalUpdateError> {
        if new_length.is_zero()
            && (self.start_inclusivity() != BoundInclusivity::Inclusive
                || self.end_inclusivity() != BoundInclusivity::Inclusive)
        {
            return Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_end_time(
            self.start_time()
                .checked_add(new_length)
                .or(Err(BoundedAbsIntervalUpdateError::OutOfRange))?,
        );
        Ok(())
    }

    /// Sets the length starting from the start bound
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the given length is zero and the start and end bounds are not
    /// both [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// Returns [`OutOfRange`](BoundedAbsIntervalUpdateError::OutOfRange)
    /// if the given length would result in an out-of-range end time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// bounded_interval.set_length_from_end(Duration::from_hours(10))?;
    ///
    /// assert_eq!(
    ///     bounded_interval.start_time(),
    ///     "2026-01-01 06:00:00Z".parse::<Timestamp>()?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_length_from_end(&mut self, new_length: StdDuration) -> Result<(), BoundedAbsIntervalUpdateError> {
        if new_length.is_zero()
            && (self.start_inclusivity() != BoundInclusivity::Inclusive
                || self.end_inclusivity() != BoundInclusivity::Inclusive)
        {
            return Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_start_time(
            self.end_time()
                .checked_sub(new_length)
                .or(Err(BoundedAbsIntervalUpdateError::OutOfRange))?,
        );
        Ok(())
    }

    /// Sets the start bound's inclusivity without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let mut bounded_interval = BoundedAbsInterval::from_times(time, time);
    ///
    /// // Even if the new start inclusivity violates the same time doubly inclusive invariant
    /// bounded_interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // It remains that way
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_start_inclusivity(&mut self, new_start_inclusivity: BoundInclusivity) {
        self.start.pos_mut().set_inclusivity(new_start_inclusivity);
    }

    /// Sets the start bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the start and end are on the same time and the given new inclusivity
    /// is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// bounded_interval.set_start_inclusivity(BoundInclusivity::Exclusive)?;
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
    ) -> Result<(), BoundedAbsIntervalUpdateError> {
        if self.start_time() == self.end_time() && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_start_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Sets the end bound's inclusivity without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let mut bounded_interval = BoundedAbsInterval::from_times(time, time);
    ///
    /// // Even if the new end inclusivity violates the same time doubly inclusive invariant
    /// bounded_interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // It remains that way
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_end_inclusivity(&mut self, new_end_inclusivity: BoundInclusivity) {
        self.end.pos_mut().set_inclusivity(new_end_inclusivity);
    }

    /// Sets the end bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the start and end are on the same time and the given new inclusivity
    /// is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// bounded_interval.set_end_inclusivity(BoundInclusivity::Exclusive)?;
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
    ) -> Result<(), BoundedAbsIntervalUpdateError> {
        if self.start_time() == self.end_time() && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_end_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Wraps `self` in an [`AbsInterval`]
    #[must_use]
    pub fn to_interval(self) -> AbsInterval {
        AbsInterval::from(self)
    }

    /// Wraps `self` in an [`EmptiableAbsInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableAbsInterval {
        EmptiableAbsInterval::from(self)
    }
}

/// Errors that can occur when creating a [`BoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsIntervalCreationError {
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

impl Display for BoundedAbsIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStart => write!(f, "Provided or computed start bound is out of range"),
            Self::OutOfRangeEnd => write!(f, "Provided or computed end bound is out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for BoundedAbsIntervalCreationError {}

/// Error that can occur when trying to create a [`BoundedAbsInterval`]
/// from a [`Timestamp`] range
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedAbsIntervalTryFromRangeError;

impl Display for BoundedAbsIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `BoundedAbsInterval`",
        )
    }
}

impl Error for BoundedAbsIntervalTryFromRangeError {}

/// Errors that can occur when updating a [`BoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsIntervalUpdateError {
    /// Update would violate the chronological order invariant
    ChronologicalOrderViolation,
    /// Update would violate the same time = doubly inclusive invariant
    SameTimeDoublyInclusiveViolation,
    /// Given data would set a bound out of range
    OutOfRange,
}

impl Display for BoundedAbsIntervalUpdateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ChronologicalOrderViolation => write!(f, "Update would violate the chronological order invariant"),
            Self::SameTimeDoublyInclusiveViolation => {
                write!(f, "Update would violate the same time = doubly inclusive invariant")
            },
            Self::OutOfRange => write!(f, "Given data would set a bound out of range"),
        }
    }
}

impl Error for BoundedAbsIntervalUpdateError {}

impl Interval for BoundedAbsInterval {}

impl HasOpenness for BoundedAbsInterval {
    fn openness(&self) -> Openness {
        Openness::Bounded
    }
}

impl HasRelativity for BoundedAbsInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for BoundedAbsInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(
            self.end()
                .pos()
                .time()
                .duration_since(self.start().pos().time())
                .unsigned_abs(),
            Epsilon::from((self.start_inclusivity(), self.end_inclusivity())),
        )
    }
}

impl HasAbsBoundPair for BoundedAbsInterval {
    fn abs_bound_pair(&self) -> AbsBoundPair {
        AbsBoundPair::unchecked_new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsStartBound {
        self.start().to_start_bound()
    }

    fn abs_end(&self) -> AbsEndBound {
        self.end().to_end_bound()
    }
}

impl IsEmpty for BoundedAbsInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl HasIntervalTypeWithRel for BoundedAbsInterval {
    fn interval_type_with_rel(&self) -> IntervalTypeWithRel {
        IntervalTypeWithRel::AbsBounded
    }
}

impl From<(AbsFiniteStartBound, AbsFiniteEndBound)> for BoundedAbsInterval {
    fn from((start, end): (AbsFiniteStartBound, AbsFiniteEndBound)) -> Self {
        Self::new(start, end)
    }
}

impl From<(Timestamp, Timestamp)> for BoundedAbsInterval {
    fn from((start, end): (Timestamp, Timestamp)) -> Self {
        BoundedAbsInterval::from_times(start, end)
    }
}

impl From<((Timestamp, BoundInclusivity), (Timestamp, BoundInclusivity))> for BoundedAbsInterval {
    fn from(
        ((start, start_inclusivity), (end, end_inclusivity)): (
            (Timestamp, BoundInclusivity),
            (Timestamp, BoundInclusivity),
        ),
    ) -> Self {
        BoundedAbsInterval::from_times_incl(start, start_inclusivity, end, end_inclusivity)
    }
}

impl From<(AbsFiniteBoundPos, AbsFiniteBoundPos)> for BoundedAbsInterval {
    fn from((start, end): (AbsFiniteBoundPos, AbsFiniteBoundPos)) -> Self {
        Self::new(start.to_finite_start_bound(), end.to_finite_end_bound())
    }
}

impl From<Range<Timestamp>> for BoundedAbsInterval {
    fn from(range: Range<Timestamp>) -> Self {
        BoundedAbsInterval::from_times_incl(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<Timestamp>> for BoundedAbsInterval {
    fn from(range: RangeInclusive<Timestamp>) -> Self {
        BoundedAbsInterval::from_times_incl(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

/// Error that can occur when trying to convert [`AbsBoundPair`] into [`BoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedAbsIntervalTryFromAbsBoundPairError;

impl Display for BoundedAbsIntervalTryFromAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsBoundPair` into `BoundedAbsInterval`"
        )
    }
}

impl Error for BoundedAbsIntervalTryFromAbsBoundPairError {}

impl TryFrom<AbsBoundPair> for BoundedAbsInterval {
    type Error = BoundedAbsIntervalTryFromAbsBoundPairError;

    fn try_from(value: AbsBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsStartBound::Finite(finite_start), AbsEndBound::Finite(finite_end)) => {
                Ok(BoundedAbsInterval::new(finite_start, finite_end))
            },
            _ => Err(BoundedAbsIntervalTryFromAbsBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsBoundPair`] into [`BoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedAbsIntervalTryFromEmptiableAbsBoundPairError;

impl Display for BoundedAbsIntervalTryFromEmptiableAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsBoundPair` into `BoundedAbsInterval`"
        )
    }
}

impl Error for BoundedAbsIntervalTryFromEmptiableAbsBoundPairError {}

impl TryFrom<EmptiableAbsBoundPair> for BoundedAbsInterval {
    type Error = BoundedAbsIntervalTryFromEmptiableAbsBoundPairError;

    fn try_from(value: EmptiableAbsBoundPair) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(BoundedAbsIntervalTryFromEmptiableAbsBoundPairError)?,
        )
        .or(Err(BoundedAbsIntervalTryFromEmptiableAbsBoundPairError))
    }
}

/// Error that can occur when trying to convert [`AbsInterval`] into
/// [`BoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedAbsIntervalFromAbsIntervalError;

impl Display for BoundedAbsIntervalFromAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsInterval` into `BoundedAbsInterval"
        )
    }
}

impl Error for BoundedAbsIntervalFromAbsIntervalError {}

impl TryFrom<AbsInterval> for BoundedAbsInterval {
    type Error = BoundedAbsIntervalFromAbsIntervalError;

    fn try_from(value: AbsInterval) -> Result<Self, Self::Error> {
        value.bounded().ok_or(BoundedAbsIntervalFromAbsIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsInterval`] into [`BoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedAbsIntervalTryFromEmptiableAbsIntervalError;

impl Display for BoundedAbsIntervalTryFromEmptiableAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsInterval` into `BoundedAbsInterval`"
        )
    }
}

impl Error for BoundedAbsIntervalTryFromEmptiableAbsIntervalError {}

impl TryFrom<EmptiableAbsInterval> for BoundedAbsInterval {
    type Error = BoundedAbsIntervalTryFromEmptiableAbsIntervalError;

    fn try_from(value: EmptiableAbsInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(BoundedAbsIntervalTryFromEmptiableAbsIntervalError)?,
        )
        .or(Err(BoundedAbsIntervalTryFromEmptiableAbsIntervalError))
    }
}

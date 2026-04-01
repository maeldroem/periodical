//! Relative bounded interval
//!
//! A bounded interval has a start and end. Like all specific relative interval
//! types, it conserves the invariant of its bounds being in chronological order
//! and if the bounds have the same offset, they must be inclusive.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a bounded interval must remain a bounded
//! interval. It cannot mutate from being a bounded interval to a half-bounded
//! interval.
//!
//! Instead, if you are looking for an relative interval that doesn't keep the
//! [openness](Openness) invariant, see [`RelativeBoundPair`].

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, Range, RangeBounds, RangeInclusive};
use std::time::Duration as StdDuration;

use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Emptiable,
    Epsilon,
    HasBoundInclusivity,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};

/// Relative bounded interval
///
/// A bounded interval has a start offset and an end offset.
/// Like all specific relative interval types, it conserves the invariant of its
/// bounds being in chronological order and if the bounds have the same offset,
/// they must be inclusive.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a bounded interval must remain a bounded
/// interval. It cannot mutate from being a bounded interval to a half-bounded
/// interval.
///
/// Instead, if you are looking for an relative interval that doesn't keep the
/// [openness](Openness) invariant, see [`RelativeBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct BoundedRelativeInterval {
    start: SignedDuration,
    end: SignedDuration,
    start_inclusivity: BoundInclusivity,
    end_inclusivity: BoundInclusivity,
}

impl BoundedRelativeInterval {
    /// Creates a new [`BoundedRelativeInterval`] without checking if it
    /// violates the invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(2);
    /// let end = SignedDuration::from_hours(-5);
    ///
    /// // Even though the end offset is before the start offset
    /// let bounded_interval = BoundedRelativeInterval::unchecked_new(start, end);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start(), start);
    /// assert_eq!(bounded_interval.end(), end);
    /// ```
    #[must_use]
    pub fn unchecked_new(start: SignedDuration, end: SignedDuration) -> Self {
        BoundedRelativeInterval {
            start,
            end,
            start_inclusivity: BoundInclusivity::default(),
            end_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`BoundedRelativeInterval`] with default bound
    /// inclusivities
    ///
    /// If the start offset is past the end offset, it swaps them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(16);
    /// let end = SignedDuration::from_hours(8);
    ///
    /// // Offsets that are not in chronological order
    /// let bounded_interval = BoundedRelativeInterval::new(start, end);
    ///
    /// // Are swapped
    /// assert_eq!(bounded_interval.start(), end);
    /// assert_eq!(bounded_interval.end(), start);
    /// ```
    #[must_use]
    pub fn new(mut start: SignedDuration, mut end: SignedDuration) -> Self {
        if start > end {
            std::mem::swap(&mut start, &mut end);
        }

        Self::unchecked_new(start, end)
    }

    /// Creates a new [`BoundedRelativeInterval`] with default bound
    /// inclusivities
    ///
    /// # Errors
    ///
    /// Returns [`BoundedRelativeIntervalCreationError`] if `start + length`
    /// overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(-1);
    /// let length = Duration::from_hours(5);
    ///
    /// let bounded_interval = BoundedRelativeInterval::new_with_length(start, length)?;
    ///
    /// assert_eq!(bounded_interval.start(), SignedDuration::from_hours(-1));
    /// assert_eq!(bounded_interval.end(), SignedDuration::from_hours(4));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn new_with_length(
        start: SignedDuration,
        length: StdDuration,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        Ok(BoundedRelativeInterval::unchecked_new(
            start,
            SignedDuration::from_nanos_i128(
                start
                    .as_nanos()
                    .checked_add_unsigned(length.as_nanos())
                    .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeEnd)?,
            ),
        ))
    }

    /// Creates a new [`BoundedRelativeInterval`] with the given bound
    /// inclusivities without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// // Not doubly inclusive
    /// let bounded_interval = BoundedRelativeInterval::unchecked_new_with_inclusivity(
    ///     SignedDuration::ZERO,
    ///     BoundInclusivity::Inclusive,
    ///     SignedDuration::ZERO,
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
    /// ```
    #[must_use]
    pub fn unchecked_new_with_inclusivity(
        start: SignedDuration,
        start_inclusivity: BoundInclusivity,
        end: SignedDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        BoundedRelativeInterval {
            start,
            end,
            start_inclusivity,
            end_inclusivity,
        }
    }

    /// Creates a new [`BoundedRelativeInterval`] with the given bound
    /// inclusivities
    ///
    /// If the given offsets are equal, then the inclusivities will be set to
    /// inclusive.
    ///
    /// If the start offset is past the end offset, it swaps them. The bound
    /// inclusivities are also swapped in this process.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    ///
    /// // Same offset, not doubly inclusive
    /// let bounded_interval = BoundedRelativeInterval::new_with_inclusivity(
    ///     SignedDuration::from_hours(5),
    ///     BoundInclusivity::Inclusive,
    ///     SignedDuration::from_hours(5),
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
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        start: SignedDuration,
        start_inclusivity: BoundInclusivity,
        end: SignedDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        match start.cmp(&end) {
            Ordering::Less => Self::unchecked_new_with_inclusivity(start, start_inclusivity, end, end_inclusivity),
            Ordering::Equal => Self::unchecked_new(start, end),
            Ordering::Greater => Self::unchecked_new_with_inclusivity(end, end_inclusivity, start, start_inclusivity),
        }
    }

    /// Creates a new [`BoundedRelativeInterval`] with the given bound
    /// inclusivities
    ///
    /// If the length is zero, then the inclusivities will be set to inclusive.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeEnd`](BoundedRelativeIntervalCreationError::OutOfRangeEnd) if `start + length` overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let bounded_interval = BoundedRelativeInterval::new_with_length_and_inclusivity(
    ///     SignedDuration::from_hours(3),
    ///     BoundInclusivity::Inclusive,
    ///     Duration::from_hours(5),
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// assert_eq!(bounded_interval.start(), SignedDuration::from_hours(3));
    /// assert_eq!(bounded_interval.end(), SignedDuration::from_hours(8));
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
    pub fn new_with_length_and_inclusivity(
        start: SignedDuration,
        start_inclusivity: BoundInclusivity,
        length: StdDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        if length.is_zero() {
            return Ok(BoundedRelativeInterval::unchecked_new(start, start));
        }

        Ok(BoundedRelativeInterval::unchecked_new_with_inclusivity(
            start,
            start_inclusivity,
            SignedDuration::from_nanos_i128(
                start
                    .as_nanos()
                    .checked_add_unsigned(length.as_nanos())
                    .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeEnd)?,
            ),
            end_inclusivity,
        ))
    }

    /// Attempts to create a [`BoundedRelativeInterval`] from a [`SignedDuration`] range
    ///
    /// # Errors
    ///
    /// Returns [`BoundedRelativeIntervalTryFromRangeError`] if any range bound is [unbounded](Bound::Unbounded).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{BoundedRelativeInterval, BoundedRelativeIntervalTryFromRangeError};
    /// let start = SignedDuration::from_hours(8);
    /// let end = SignedDuration::from_hours(16);
    ///
    /// let interval = BoundedRelativeInterval::try_from_range(start..end)?;
    ///
    /// assert_eq!(interval.start(), start);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end(), end);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, BoundedRelativeIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        let (start, start_inclusivity) = match range.start_bound() {
            Bound::Included(&offset) => (offset, BoundInclusivity::Inclusive),
            Bound::Excluded(&offset) => (offset, BoundInclusivity::Exclusive),
            Bound::Unbounded => return Err(BoundedRelativeIntervalTryFromRangeError),
        };

        let (end, end_inclusivity) = match range.end_bound() {
            Bound::Included(&offset) => (offset, BoundInclusivity::Inclusive),
            Bound::Excluded(&offset) => (offset, BoundInclusivity::Exclusive),
            Bound::Unbounded => return Err(BoundedRelativeIntervalTryFromRangeError),
        };

        Ok(Self::new_with_inclusivity(
            start,
            start_inclusivity,
            end,
            end_inclusivity,
        ))
    }

    /// Returns the start offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval =
    ///     BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(5));
    ///
    /// assert_eq!(bounded_interval.start(), SignedDuration::from_hours(1));
    /// ```
    #[must_use]
    pub fn start(&self) -> SignedDuration {
        self.start
    }

    /// Returns the end offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval =
    ///     BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(5));
    ///
    /// assert_eq!(bounded_interval.end(), SignedDuration::from_hours(5));
    /// ```
    #[must_use]
    pub fn end(&self) -> SignedDuration {
        self.end
    }

    /// Returns the inclusivity of the start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::new_with_inclusivity(
    ///     SignedDuration::from_hours(1),
    ///     BoundInclusivity::Inclusive,
    ///     SignedDuration::from_hours(5),
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
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
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::new_with_inclusivity(
    ///     SignedDuration::from_hours(1),
    ///     BoundInclusivity::Inclusive,
    ///     SignedDuration::from_hours(5),
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    #[must_use]
    pub fn end_inclusivity(&self) -> BoundInclusivity {
        self.end_inclusivity
    }

    /// Sets the start offset without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start_offset = SignedDuration::from_hours(1);
    /// let end_offset = SignedDuration::from_hours(4);
    ///
    /// let mut bounded_interval = BoundedRelativeInterval::new(start_offset, end_offset);
    ///
    /// // New start is not in chronological order
    /// let new_start_offset = SignedDuration::from_hours(10);
    ///
    /// bounded_interval.unchecked_set_start(new_start_offset);
    ///
    /// // And yet it stays that way
    /// assert_eq!(bounded_interval.start(), new_start_offset);
    /// assert_eq!(bounded_interval.end(), end_offset);
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: SignedDuration) {
        self.start = new_start;
    }

    /// Sets the end offset without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start_offset = SignedDuration::from_hours(1);
    /// let end_offset = SignedDuration::from_hours(4);
    ///
    /// let mut bounded_interval = BoundedRelativeInterval::new(start_offset, end_offset);
    ///
    /// // New end is not in chronological order
    /// let new_end_offset = SignedDuration::from_hours(-5);
    ///
    /// bounded_interval.unchecked_set_end(new_end_offset);
    ///
    /// // And yet it stays that way
    /// assert_eq!(bounded_interval.start(), start_offset);
    /// assert_eq!(bounded_interval.end(), new_end_offset);
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: SignedDuration) {
        self.end = new_end;
    }

    /// Sets the start
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new start offset is after the current end offset.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new start offset would set it on the same offset as the end
    /// offset without the bound inclusivities being both
    /// [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(2);
    /// let end = SignedDuration::from_hours(5);
    ///
    /// let mut bounded_interval = BoundedRelativeInterval::new(start, end);
    ///
    /// let new_start = SignedDuration::from_hours(4);
    ///
    /// bounded_interval.set_start(new_start)?;
    ///
    /// assert_eq!(bounded_interval.start(), new_start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start(&mut self, new_start: SignedDuration) -> Result<(), BoundedRelativeIntervalUpdateError> {
        match new_start.cmp(&self.end) {
            Ordering::Less => {
                self.unchecked_set_start(new_start);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity != BoundInclusivity::Inclusive
                    || self.end_inclusivity != BoundInclusivity::Inclusive
                {
                    return Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation);
                }

                self.unchecked_set_start(new_start);
                Ok(())
            },
            Ordering::Greater => Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the end
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new end offset is before the current start offset.
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the new end offset would set it on the same offset as the start
    /// offset without the bound inclusivities being both
    /// [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(2);
    /// let end = SignedDuration::from_hours(5);
    ///
    /// let mut bounded_interval = BoundedRelativeInterval::new(start, end);
    ///
    /// let new_end = SignedDuration::from_hours(4);
    ///
    /// bounded_interval.set_end(new_end)?;
    ///
    /// assert_eq!(bounded_interval.end(), new_end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end(&mut self, new_end: SignedDuration) -> Result<(), BoundedRelativeIntervalUpdateError> {
        match self.start.cmp(&new_end) {
            Ordering::Less => {
                self.unchecked_set_end(new_end);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity != BoundInclusivity::Inclusive
                    || self.end_inclusivity != BoundInclusivity::Inclusive
                {
                    return Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation);
                }

                self.unchecked_set_end(new_end);
                Ok(())
            },
            Ordering::Greater => Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the length starting from the start bound
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the given length is zero and the start and end bounds are not
    /// both [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// Returns [`OutOfRange`](BoundedRelativeIntervalUpdateError::OutOfRange)
    /// if the given length would result in an out-of-range end offset.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let mut bounded_interval =
    ///     BoundedRelativeInterval::new(SignedDuration::from_hours(2), SignedDuration::from_hours(5));
    ///
    /// bounded_interval.set_length_from_start(Duration::from_hours(10))?;
    ///
    /// assert_eq!(bounded_interval.start(), SignedDuration::from_hours(2));
    /// assert_eq!(bounded_interval.end(), SignedDuration::from_hours(12));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_length_from_start(&mut self, new_length: StdDuration) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if new_length.is_zero()
            && (self.start_inclusivity != BoundInclusivity::Inclusive
                || self.end_inclusivity != BoundInclusivity::Inclusive)
        {
            return Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_end(
            SignedDuration::try_from_nanos_i128(
                self.start
                    .as_nanos()
                    .checked_add_unsigned(new_length.as_nanos())
                    .ok_or(BoundedRelativeIntervalUpdateError::OutOfRange)?,
            )
            .ok_or(BoundedRelativeIntervalUpdateError::OutOfRange)?,
        );

        Ok(())
    }

    /// Sets the length starting from the end bound
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the given length is zero and the start and end bounds are not
    /// both [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// Returns [`OutOfRange`](BoundedRelativeIntervalUpdateError::OutOfRange)
    /// if the given length would result in an out-of-range start offset.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let mut bounded_interval =
    ///     BoundedRelativeInterval::new(SignedDuration::from_hours(2), SignedDuration::from_hours(5));
    ///
    /// bounded_interval.set_length_from_end(Duration::from_hours(10))?;
    ///
    /// assert_eq!(bounded_interval.start(), SignedDuration::from_hours(-5));
    /// assert_eq!(bounded_interval.end(), SignedDuration::from_hours(5));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_length_from_end(&mut self, new_length: StdDuration) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if new_length.is_zero()
            && (self.start_inclusivity != BoundInclusivity::Inclusive
                || self.end_inclusivity != BoundInclusivity::Inclusive)
        {
            return Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_start(
            SignedDuration::try_from_nanos_i128(
                self.end
                    .as_nanos()
                    .checked_sub_unsigned(new_length.as_nanos())
                    .ok_or(BoundedRelativeIntervalUpdateError::OutOfRange)?,
            )
            .ok_or(BoundedRelativeIntervalUpdateError::OutOfRange)?,
        );

        Ok(())
    }

    /// Sets the start bound's inclusivity without checking if it violates
    /// invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval =
    ///     BoundedRelativeInterval::new(SignedDuration::from_hours(5), SignedDuration::from_hours(5));
    ///
    /// // Violates the same time doubly inclusive invariant
    /// bounded_interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Yet stays this way
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// ```
    pub fn unchecked_set_start_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.start_inclusivity = new_inclusivity;
    }

    /// Sets the end bound's inclusivity without checking if it violates
    /// invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval =
    ///     BoundedRelativeInterval::new(SignedDuration::from_hours(5), SignedDuration::from_hours(5));
    ///
    /// // Violates the same time doubly inclusive invariant
    /// bounded_interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Yet stays this way
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    pub fn unchecked_set_end_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.end_inclusivity = new_inclusivity;
    }

    /// Sets the start bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the start and end are on the same offset and the given new
    /// inclusivity is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedRelativeInterval::new(
    ///     SignedDuration::from_hours(5),
    ///     SignedDuration::from_hours(10),
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
    ) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if self.start == self.end && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_start_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Sets the end bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameTimeDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
    /// if the start and end are on the same offset and the given new
    /// inclusivity is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedRelativeInterval::new(
    ///     SignedDuration::from_hours(5),
    ///     SignedDuration::from_hours(10),
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
    ) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if self.start == self.end && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation);
        }

        self.unchecked_set_end_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Wraps the interval in [`RelativeInterval`]
    #[must_use]
    pub fn to_interval(self) -> RelativeInterval {
        RelativeInterval::from(self)
    }

    /// Wraps the interval in [`EmptiableRelativeInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableRelativeInterval {
        EmptiableRelativeInterval::from(self)
    }
}

/// Errors the can occur when creating a [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedRelativeIntervalCreationError {
    /// Provided or computed start bound is out of range
    OutOfRangeStart,
    /// Provided or computed end bound is out of range
    OutOfRangeEnd,
}

impl Display for BoundedRelativeIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStart => write!(f, "Provided or computed start bound is out of range"),
            Self::OutOfRangeEnd => write!(f, "Provided or computed end bound is out of range"),
        }
    }
}

impl Error for BoundedRelativeIntervalCreationError {}

/// Error that can occur when trying to create a [`BoundedRelativeInterval`]
/// from a [`SignedDuration`] range
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedRelativeIntervalTryFromRangeError;

impl Display for BoundedRelativeIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `SignedDuration` range into a `BoundedRelativeInterval`",
        )
    }
}

impl Error for BoundedRelativeIntervalTryFromRangeError {}

/// Errors that can occur when updating a [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedRelativeIntervalUpdateError {
    /// Update would violate the chronological order invariant
    ChronologicalOrderViolation,
    /// Update would violate the same time = doubly inclusive invariant
    SameTimeDoublyInclusiveViolation,
    /// Given data would set a bound out of range
    OutOfRange,
}

impl Display for BoundedRelativeIntervalUpdateError {
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

impl Error for BoundedRelativeIntervalUpdateError {}

impl Interval for BoundedRelativeInterval {}

impl HasOpenness for BoundedRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::Bounded
    }
}

impl HasRelativity for BoundedRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for BoundedRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(
            self.end.saturating_sub(self.start).unsigned_abs(),
            Epsilon::from((self.start_inclusivity(), self.end_inclusivity())),
        )
    }
}

impl HasRelativeBoundPair for BoundedRelativeInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        RelativeBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        RelativeFiniteBound::new_with_inclusivity(self.start, self.start_inclusivity).to_start_bound()
    }

    fn rel_end(&self) -> RelativeEndBound {
        RelativeFiniteBound::new_with_inclusivity(self.end, self.end_inclusivity).to_end_bound()
    }
}

impl Emptiable for BoundedRelativeInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<(SignedDuration, SignedDuration)> for BoundedRelativeInterval {
    fn from((start, end): (SignedDuration, SignedDuration)) -> Self {
        BoundedRelativeInterval::new(start, end)
    }
}

impl From<((SignedDuration, BoundInclusivity), (SignedDuration, BoundInclusivity))> for BoundedRelativeInterval {
    fn from(
        ((start, start_inclusivity), (end, end_inclusivity)): (
            (SignedDuration, BoundInclusivity),
            (SignedDuration, BoundInclusivity),
        ),
    ) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(start, start_inclusivity, end, end_inclusivity)
    }
}

impl From<Range<SignedDuration>> for BoundedRelativeInterval {
    fn from(range: Range<SignedDuration>) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<SignedDuration>> for BoundedRelativeInterval {
    fn from(range: RangeInclusive<SignedDuration>) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

/// Errors that can occur when trying to convert [`RelativeBoundPair`] into
/// [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedRelativeIntervalFromRelativeBoundPairError {
    NotBoundedInterval,
}

impl Display for BoundedRelativeIntervalFromRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotBoundedInterval => write!(f, "Not a bounded interval"),
        }
    }
}

impl Error for BoundedRelativeIntervalFromRelativeBoundPairError {}

impl TryFrom<RelativeBoundPair> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalFromRelativeBoundPairError;

    fn try_from(value: RelativeBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
                Ok(BoundedRelativeInterval::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity(),
                    finite_end.offset(),
                    finite_end.inclusivity(),
                ))
            },
            _ => Err(Self::Error::NotBoundedInterval),
        }
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeBoundPair`] into [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError;

impl Display for BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeBoundPair` into `BoundedRelativeInterval`"
        )
    }
}

impl Error for BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError {}

impl TryFrom<EmptiableRelativeBoundPair> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError;

    fn try_from(value: EmptiableRelativeBoundPair) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError)?,
        )
        .or(Err(BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError))
    }
}

/// Error that can occur when trying to convert [`RelativeInterval`] into
/// [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedRelativeIntervalFromRelativeIntervalError;

impl Display for BoundedRelativeIntervalFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeInterval` into `BoundedRelativeInterval"
        )
    }
}

impl Error for BoundedRelativeIntervalFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        value.bounded().ok_or(BoundedRelativeIntervalFromRelativeIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeInterval`] into [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError;

impl Display for BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeInterval` into `BoundedRelativeInterval`"
        )
    }
}

impl Error for BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError {}

impl TryFrom<EmptiableRelativeInterval> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError;

    fn try_from(value: EmptiableRelativeInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)?,
        )
        .or(Err(BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError))
    }
}

//! Relative bounded interval
//!
//! A bounded interval has a finite start and a finite end.
//! Like all specific interval types, it conserves the invariant of its bounds
//! being in chronological order and if the bounds have the same position, they must be inclusive.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a bounded interval must remain a bounded
//! interval.
//!
//! Instead, if you are looking for a relative interval that doesn't keep the
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
    Epsilon,
    HasBoundInclusivity,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    IsEmpty,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteEndBound,
    RelativeFiniteStartBound,
    RelativeInterval,
    RelativeStartBound,
    RelativeStartEndBoundsCheckForIntervalCreationError,
    check_relative_finite_start_end_bounds_for_interval_creation,
    prepare_relative_finite_start_end_bounds_for_interval_creation,
};

/// Relative bounded interval
///
/// A bounded interval has a finite start and a finite end.
/// Like all specific interval types, it conserves the invariant of its bounds
/// being in chronological order and if the bounds have the same position, they must be inclusive.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a bounded interval must remain a bounded
/// interval.
///
/// Instead, if you are looking for a relative interval that doesn't keep the
/// [openness](Openness) invariant, see [`RelativeBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct BoundedRelativeInterval {
    start: RelativeFiniteStartBound,
    end: RelativeFiniteEndBound,
}

impl BoundedRelativeInterval {
    /// Creates a new [`BoundedRelativeInterval`] without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let start = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(5)).to_finite_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_finite_end_bound();
    ///
    /// // Even though the offsets are not in chronological order
    /// let bounded_interval = BoundedRelativeInterval::unchecked_new(start, end);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start(), start);
    /// assert_eq!(bounded_interval.end(), end);
    /// ```
    #[must_use]
    pub fn unchecked_new(start: RelativeFiniteStartBound, end: RelativeFiniteEndBound) -> Self {
        BoundedRelativeInterval {
            start,
            end,
        }
    }

    /// Creates a new [`BoundedRelativeInterval`]
    ///
    /// If the bounds are not in chronological order, it swaps them.
    /// If they are on the same position, it makes them both inclusive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let start_pos = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(5));
    /// let end_pos = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3));
    ///
    /// // Since offsets are not in chronological order
    /// let bounded_interval = BoundedRelativeInterval::new(start_pos.to_finite_start_bound(), end_pos.to_finite_end_bound());
    ///
    /// // They are swapped
    /// assert_eq!(bounded_interval.start(), end_pos.to_finite_start_bound());
    /// assert_eq!(bounded_interval.end(), start_pos.to_finite_end_bound());
    /// ```
    #[must_use]
    pub fn new(mut start: RelativeFiniteStartBound, mut end: RelativeFiniteEndBound) -> Self {
        prepare_relative_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

        Self::unchecked_new(start, end)
    }

    /// Creates a new [`BoundedRelativeInterval`] from offsets without checking if it
    /// violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(2);
    /// let end = SignedDuration::from_hours(-5);
    ///
    /// // Even though the offsets are not in chronological order
    /// let bounded_interval = BoundedRelativeInterval::unchecked_from_offsets(start, end);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_offset(), start);
    /// assert_eq!(bounded_interval.end_offset(), end);
    /// ```
    #[must_use]
    pub fn unchecked_from_offsets(start: SignedDuration, end: SignedDuration) -> Self {
        Self::unchecked_new(
            RelativeFiniteBoundPosition::new(start).to_finite_start_bound(),
            RelativeFiniteBoundPosition::new(end).to_finite_end_bound(),
        )
    }

    /// Creates a new [`BoundedRelativeInterval`] from offsets with default bound
    /// inclusivities
    ///
    /// If the offsets are not in chronological order, it swaps them.
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
    /// let bounded_interval = BoundedRelativeInterval::from_offsets(start, end);
    ///
    /// // Are swapped
    /// assert_eq!(bounded_interval.start_offset(), end);
    /// assert_eq!(bounded_interval.end_offset(), start);
    /// ```
    #[must_use]
    pub fn from_offsets(start: SignedDuration, end: SignedDuration) -> Self {
        Self::new(
            RelativeFiniteBoundPosition::new(start).to_finite_start_bound(),
            RelativeFiniteBoundPosition::new(end).to_finite_end_bound(),
        )
    }

    /// Creates a new [`BoundedRelativeInterval`] from offsets and inclusivities without checking
    /// if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(1);
    ///
    /// // Even if it violates the same offset doubly inclusive invariant
    /// let bounded_interval = BoundedRelativeInterval::unchecked_from_offsets_incl(
    ///     offset,
    ///     BoundInclusivity::Inclusive,
    ///     offset,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_offset(), offset);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(bounded_interval.end_offset(), offset);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    #[must_use]
    pub fn unchecked_from_offsets_incl(
        start: SignedDuration,
        start_inclusivity: BoundInclusivity,
        end: SignedDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        Self::unchecked_new(
            RelativeFiniteBoundPosition::new_with_inclusivity(start, start_inclusivity).to_finite_start_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(end, end_inclusivity).to_finite_end_bound(),
        )
    }

    /// Creates a new [`BoundedRelativeInterval`] from offsets and inclusivities
    ///
    /// If the bounds are not in chronological order, it swaps them.
    /// If they are on the same position, it makes them both inclusive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start_offset = SignedDuration::from_hours(3);
    /// let end_offset = SignedDuration::from_hours(5);
    ///
    /// let bounded_interval = BoundedRelativeInterval::from_offsets_incl(
    ///     start_offset,
    ///     BoundInclusivity::Inclusive,
    ///     end_offset,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.start_offset(), start_offset);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(bounded_interval.end_offset(), end_offset);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    #[must_use]
    pub fn from_offsets_incl(
        start: SignedDuration,
        start_inclusivity: BoundInclusivity,
        end: SignedDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        Self::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(start, start_inclusivity).to_finite_start_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(end, end_inclusivity).to_finite_end_bound(),
        )
    }

    /// Attempts to create a new [`BoundedRelativeInterval`] from a start offset and a length
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
    /// let start = SignedDuration::from_hours(-1);
    /// let length = Duration::from_hours(5);
    ///
    /// let bounded_interval = BoundedRelativeInterval::from_start_len(start, length)?;
    ///
    /// assert_eq!(
    ///     bounded_interval.start_offset(),
    ///     SignedDuration::from_hours(-1)
    /// );
    /// assert_eq!(bounded_interval.end_offset(), SignedDuration::from_hours(4));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_start_len(
        start: SignedDuration,
        length: StdDuration,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        Ok(Self::unchecked_from_offsets(
            start,
            SignedDuration::try_from_nanos_i128(
                start
                    .as_nanos()
                    .checked_add_unsigned(length.as_nanos())
                    .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeEnd)?,
            )
            .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeEnd)?,
        ))
    }

    /// Attempts to create a new [`BoundedRelativeInterval`] from a start offset, a length, and inclusivities
    /// without checking if it violates invariants
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
    /// let start = SignedDuration::from_hours(1);
    ///
    /// // Even if it violates the same offset doubly inclusive variant
    /// let bounded_interval = BoundedRelativeInterval::unchecked_from_start_len_incl(
    ///     start,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::ZERO,
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_offset(), start);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(bounded_interval.end_offset(), start);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_from_start_len_incl(
        start: SignedDuration,
        start_inclusivity: BoundInclusivity,
        length: StdDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        Ok(Self::unchecked_from_offsets_incl(
            start,
            start_inclusivity,
            SignedDuration::try_from_nanos_i128(
                start
                    .as_nanos()
                    .checked_add_unsigned(length.as_nanos())
                    .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeEnd)?,
            )
            .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeEnd)?,
            end_inclusivity,
        ))
    }

    /// Attempts to create a new [`BoundedRelativeInterval`] from a start offset, a length, and inclusivities
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
    /// let start_offset = SignedDuration::from_hours(-1);
    ///
    /// let bounded_interval = BoundedRelativeInterval::from_start_len_incl(
    ///     start_offset,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::from_hours(5),
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// assert_eq!(bounded_interval.start_offset(), start_offset);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(bounded_interval.end_offset(), SignedDuration::from_hours(4));
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_start_len_incl(
        start: SignedDuration,
        start_inclusivity: BoundInclusivity,
        length: StdDuration,
        end_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        if length.is_zero() {
            return Ok(Self::unchecked_from_offsets(start, start));
        }

        Self::unchecked_from_start_len_incl(start, start_inclusivity, length, end_inclusivity)
    }

    /// Attempts to create a new [`BoundedRelativeInterval`] from an end offset and a length
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedRelativeIntervalCreationError::OutOfRangeStart) if `end - length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let end = SignedDuration::from_hours(5);
    /// let length = Duration::from_hours(6);
    ///
    /// let bounded_interval = BoundedRelativeInterval::from_end_len(end, length)?;
    ///
    /// assert_eq!(
    ///     bounded_interval.start_offset(),
    ///     SignedDuration::from_hours(-1)
    /// );
    /// assert_eq!(bounded_interval.end_offset(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_end_len(
        end: SignedDuration,
        length: StdDuration,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        Ok(Self::unchecked_from_offsets(
            SignedDuration::try_from_nanos_i128(
                end.as_nanos()
                    .checked_sub_unsigned(length.as_nanos())
                    .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeStart)?,
            )
            .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeStart)?,
            end,
        ))
    }

    /// Attempts to create a new [`BoundedRelativeInterval`] from an end offset, a length, and inclusivities
    /// without checking if it violates invariants
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedRelativeIntervalCreationError::OutOfRangeStart) if `end - length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let end = SignedDuration::from_hours(1);
    ///
    /// // Even if it violates the same offset doubly inclusive variant
    /// let bounded_interval = BoundedRelativeInterval::unchecked_from_end_len_incl(
    ///     end,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::ZERO,
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_offset(), end);
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(bounded_interval.end_offset(), end);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_from_end_len_incl(
        end: SignedDuration,
        end_inclusivity: BoundInclusivity,
        length: StdDuration,
        start_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        Ok(Self::unchecked_from_offsets_incl(
            SignedDuration::try_from_nanos_i128(
                end.as_nanos()
                    .checked_sub_unsigned(length.as_nanos())
                    .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeStart)?,
            )
            .ok_or(BoundedRelativeIntervalCreationError::OutOfRangeStart)?,
            start_inclusivity,
            end,
            end_inclusivity,
        ))
    }

    /// Attempts to create a new [`BoundedRelativeInterval`] from an end offset, a length, and inclusivities
    ///
    /// If the length is zero, then the inclusivities will be set to inclusive.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedRelativeIntervalCreationError::OutOfRangeStart) if `end - length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let end_offset = SignedDuration::from_hours(-1);
    ///
    /// let bounded_interval = BoundedRelativeInterval::from_end_len_incl(
    ///     end_offset,
    ///     BoundInclusivity::Inclusive,
    ///     Duration::from_hours(5),
    ///     BoundInclusivity::Exclusive,
    /// )?;
    ///
    /// assert_eq!(
    ///     bounded_interval.start_offset(),
    ///     SignedDuration::from_hours(-6)
    /// );
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(bounded_interval.end_offset(), end_offset);
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_end_len_incl(
        end: SignedDuration,
        end_inclusivity: BoundInclusivity,
        length: StdDuration,
        start_inclusivity: BoundInclusivity,
    ) -> Result<Self, BoundedRelativeIntervalCreationError> {
        if length.is_zero() {
            return Ok(Self::unchecked_from_offsets(end, end));
        }

        Self::unchecked_from_end_len_incl(end, end_inclusivity, length, start_inclusivity)
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
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(8);
    /// let end = SignedDuration::from_hours(16);
    ///
    /// let interval = BoundedRelativeInterval::try_from_range(start..end)?;
    ///
    /// assert_eq!(interval.start_offset(), start);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_offset(), end);
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

        Ok(Self::from_offsets_incl(start, start_inclusivity, end, end_inclusivity))
    }

    /// Returns the finite start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let start = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_finite_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16)).to_finite_end_bound();
    ///
    /// let interval = BoundedRelativeInterval::new(start, end);
    ///
    /// assert_eq!(interval.start(), start);
    /// ```
    #[must_use]
    pub fn start(&self) -> RelativeFiniteStartBound {
        self.start
    }

    /// Returns the finite end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let start = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_finite_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16)).to_finite_end_bound();
    ///
    /// let interval = BoundedRelativeInterval::new(start, end);
    ///
    /// assert_eq!(interval.end(), end);
    /// ```
    #[must_use]
    pub fn end(&self) -> RelativeFiniteEndBound {
        self.end
    }

    /// Returns the start offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(1);
    /// let end = SignedDuration::from_hours(5);
    ///
    /// let bounded_interval = BoundedRelativeInterval::from_offsets(start, end);
    ///
    /// assert_eq!(bounded_interval.start_offset(), start);
    /// ```
    #[must_use]
    pub fn start_offset(&self) -> SignedDuration {
        self.start().pos().offset()
    }

    /// Returns the end offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start = SignedDuration::from_hours(1);
    /// let end = SignedDuration::from_hours(5);
    ///
    /// let bounded_interval = BoundedRelativeInterval::from_offsets(start, end);
    ///
    /// assert_eq!(bounded_interval.end_offset(), end);
    /// ```
    #[must_use]
    pub fn end_offset(&self) -> SignedDuration {
        self.end().pos().offset()
    }

    /// Returns the inclusivity of the start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::from_offsets_incl(
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
        self.start().pos().inclusivity()
    }

    /// Returns the inclusivity of the end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::from_offsets_incl(
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
        self.end().pos().inclusivity()
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(8),
    ///     SignedDuration::from_hours(16)
    /// );
    ///
    /// let new_start_offset = SignedDuration::from_hours(18);
    ///
    /// // Even if the new start offset violates the chronological order invariant
    /// bounded_interval.unchecked_set_start(RelativeFiniteBoundPosition::new(new_start_offset).to_finite_start_bound());
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_offset(), new_start_offset);
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: RelativeFiniteStartBound) {
        self.start = new_start;
    }

    /// Sets the start bound
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new start bound violates the chronological order invariant.
    ///
    /// Returns [`SameOffsetDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
    /// if the new start bound violates the same offset doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(8),
    ///     SignedDuration::from_hours(16)
    /// );
    ///
    /// let new_start_offset = SignedDuration::from_hours(10);
    ///
    /// bounded_interval.set_start(RelativeFiniteBoundPosition::new(new_start_offset).to_finite_start_bound())?;
    ///
    /// assert_eq!(bounded_interval.start_offset(), new_start_offset);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start(&mut self, new_start: RelativeFiniteStartBound) -> Result<(), BoundedRelativeIntervalUpdateError> {
        check_relative_finite_start_end_bounds_for_interval_creation(&new_start, &self.end()).map_err(
            |err| match err {
                RelativeStartEndBoundsCheckForIntervalCreationError::StartPastEnd => {
                    BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation
                },
                RelativeStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive => {
                    BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation
                },
            },
        )?;

        self.unchecked_set_start(new_start);
        Ok(())
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(8),
    ///     SignedDuration::from_hours(16)
    /// );
    ///
    /// let new_end_offset = SignedDuration::from_hours(18);
    ///
    /// // Even if the new end offset violates the chronological order invariant
    /// bounded_interval.unchecked_set_end(RelativeFiniteBoundPosition::new(new_end_offset).to_finite_end_bound());
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.end_offset(), new_end_offset);
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: RelativeFiniteEndBound) {
        self.end = new_end;
    }

    /// Sets the end bound
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new end bound violates the chronological order invariant.
    ///
    /// Returns [`SameOffsetDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
    /// if the new end bound violates the same offset doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, BoundedRelativeInterval};
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(8),
    ///     SignedDuration::from_hours(16)
    /// );
    ///
    /// let new_end_offset = SignedDuration::from_hours(10);
    ///
    /// bounded_interval.set_end(RelativeFiniteBoundPosition::new(new_end_offset).to_finite_end_bound())?;
    ///
    /// assert_eq!(bounded_interval.end_offset(), new_end_offset);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end(&mut self, new_end: RelativeFiniteEndBound) -> Result<(), BoundedRelativeIntervalUpdateError> {
        check_relative_finite_start_end_bounds_for_interval_creation(&self.start(), &new_end).map_err(
            |err| match err {
                RelativeStartEndBoundsCheckForIntervalCreationError::StartPastEnd => {
                    BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation
                },
                RelativeStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive => {
                    BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation
                },
            },
        )?;

        self.unchecked_set_end(new_end);
        Ok(())
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
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(start_offset, end_offset);
    ///
    /// let new_start_offset = SignedDuration::from_hours(10);
    ///
    /// // Even if the new start offset violates the chronological order invariant
    /// bounded_interval.unchecked_set_start_offset(new_start_offset);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.start_offset(), new_start_offset);
    /// ```
    pub fn unchecked_set_start_offset(&mut self, new_start_offset: SignedDuration) {
        self.start.pos_mut().set_offset(new_start_offset);
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
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(start_offset, end_offset);
    ///
    /// let new_end_offset = SignedDuration::from_hours(-5);
    ///
    /// // Even if the new end offset violates the chronological order invariant
    /// bounded_interval.unchecked_set_end_offset(new_end_offset);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.end_offset(), new_end_offset);
    /// ```
    pub fn unchecked_set_end_offset(&mut self, new_end_offset: SignedDuration) {
        self.end.pos_mut().set_offset(new_end_offset);
    }

    /// Sets the start offset
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new start offset violates the chronological order invariant.
    ///
    /// Returns [`SameOffsetDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
    /// if the new start offset violates the same offset doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start_offset = SignedDuration::from_hours(2);
    /// let end_offset = SignedDuration::from_hours(5);
    ///
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(start_offset, end_offset);
    ///
    /// let new_start_offset = SignedDuration::from_hours(4);
    ///
    /// bounded_interval.set_start_offset(new_start_offset)?;
    ///
    /// assert_eq!(bounded_interval.start_offset(), new_start_offset);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start_offset(
        &mut self,
        new_start_offset: SignedDuration,
    ) -> Result<(), BoundedRelativeIntervalUpdateError> {
        match new_start_offset.cmp(&self.end_offset()) {
            Ordering::Less => {
                self.unchecked_set_start_offset(new_start_offset);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity() != BoundInclusivity::Inclusive
                    || self.end_inclusivity() != BoundInclusivity::Inclusive
                {
                    return Err(BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation);
                }

                self.unchecked_set_start_offset(new_start_offset);
                Ok(())
            },
            Ordering::Greater => Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the end offset
    ///
    /// # Errors
    ///
    /// Returns [`ChronologicalOrderViolation`](BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
    /// if the new end offset violates the chronological order invariant.
    ///
    /// Returns [`SameOffsetDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
    /// if the new end offset violates the same offset doubly inclusive invariant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let start_offset = SignedDuration::from_hours(2);
    /// let end_offset = SignedDuration::from_hours(5);
    ///
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(start_offset, end_offset);
    ///
    /// let new_end_offset = SignedDuration::from_hours(4);
    ///
    /// bounded_interval.set_end_offset(new_end_offset)?;
    ///
    /// assert_eq!(bounded_interval.end_offset(), new_end_offset);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end_offset(&mut self, new_end_offset: SignedDuration) -> Result<(), BoundedRelativeIntervalUpdateError> {
        match self.start_offset().cmp(&new_end_offset) {
            Ordering::Less => {
                self.unchecked_set_end_offset(new_end_offset);
                Ok(())
            },
            Ordering::Equal => {
                if self.start_inclusivity() != BoundInclusivity::Inclusive
                    || self.end_inclusivity() != BoundInclusivity::Inclusive
                {
                    return Err(BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation);
                }

                self.unchecked_set_end_offset(new_end_offset);
                Ok(())
            },
            Ordering::Greater => Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation),
        }
    }

    /// Sets the length starting from the start bound
    ///
    /// # Errors
    ///
    /// Returns [`SameOffsetDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
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
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(2),
    ///     SignedDuration::from_hours(5),
    /// );
    ///
    /// bounded_interval.set_length_from_start(Duration::from_hours(10))?;
    ///
    /// assert_eq!(
    ///     bounded_interval.end_offset(),
    ///     SignedDuration::from_hours(12)
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_length_from_start(&mut self, new_length: StdDuration) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if new_length.is_zero()
            && (self.start_inclusivity() != BoundInclusivity::Inclusive
                || self.end_inclusivity() != BoundInclusivity::Inclusive)
        {
            return Err(BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation);
        }

        self.unchecked_set_end_offset(
            SignedDuration::try_from_nanos_i128(
                self.start_offset()
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
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(2),
    ///     SignedDuration::from_hours(5),
    /// );
    ///
    /// bounded_interval.set_length_from_end(Duration::from_hours(10))?;
    ///
    /// assert_eq!(
    ///     bounded_interval.start_offset(),
    ///     SignedDuration::from_hours(-5)
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_length_from_end(&mut self, new_length: StdDuration) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if new_length.is_zero()
            && (self.start_inclusivity() != BoundInclusivity::Inclusive
                || self.end_inclusivity() != BoundInclusivity::Inclusive)
        {
            return Err(BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation);
        }

        self.unchecked_set_start_offset(
            SignedDuration::try_from_nanos_i128(
                self.end_offset()
                    .as_nanos()
                    .checked_sub_unsigned(new_length.as_nanos())
                    .ok_or(BoundedRelativeIntervalUpdateError::OutOfRange)?,
            )
            .ok_or(BoundedRelativeIntervalUpdateError::OutOfRange)?,
        );

        Ok(())
    }

    /// Sets the start bound's inclusivity without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(5);
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(offset, offset);
    ///
    /// // Even if the new start inclusivity violates the same offset doubly inclusive invariant
    /// bounded_interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // It remains that way
    /// assert_eq!(
    ///     bounded_interval.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    pub fn unchecked_set_start_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.start.pos_mut().set_inclusivity(new_inclusivity);
    }

    /// Sets the end bound's inclusivity without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(5);
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(offset, offset);
    ///
    /// // Even if the new end inclusivity violates the same offset doubly inclusive invariant
    /// bounded_interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // It remains that way
    /// assert_eq!(
    ///     bounded_interval.end_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    pub fn unchecked_set_end_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.end.pos_mut().set_inclusivity(new_inclusivity);
    }

    /// Sets the start bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameOffsetDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
    /// if the start and end are on the same offset and the given new inclusivity
    /// is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(5),
    ///     SignedDuration::from_hours(10),
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
    ) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if self.start_offset() == self.end_offset() && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation);
        }

        self.unchecked_set_start_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Sets the end bound's inclusivity
    ///
    /// # Errors
    ///
    /// Returns [`SameOffsetDoublyInclusiveViolation`](BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
    /// if the start and end are on the same offset and the given new inclusivity
    /// is not [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut bounded_interval = BoundedRelativeInterval::from_offsets(
    ///     SignedDuration::from_hours(5),
    ///     SignedDuration::from_hours(10),
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
    ) -> Result<(), BoundedRelativeIntervalUpdateError> {
        if self.start_offset() == self.end_offset() && new_inclusivity != BoundInclusivity::Inclusive {
            return Err(BoundedRelativeIntervalUpdateError::SameOffsetDoublyInclusiveViolation);
        }

        self.unchecked_set_end_inclusivity(new_inclusivity);
        Ok(())
    }

    /// Wraps `self` in a [`RelativeInterval`]
    #[must_use]
    pub fn to_interval(self) -> RelativeInterval {
        RelativeInterval::from(self)
    }

    /// Wraps `self` in an [`EmptiableRelativeInterval`]
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
    SameOffsetDoublyInclusiveViolation,
    /// Given data would set a bound out of range
    OutOfRange,
}

impl Display for BoundedRelativeIntervalUpdateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ChronologicalOrderViolation => write!(f, "Update would violate the chronological order invariant"),
            Self::SameOffsetDoublyInclusiveViolation => {
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
            self.end_offset().saturating_sub(self.start_offset()).unsigned_abs(),
            Epsilon::from((self.start_inclusivity(), self.end_inclusivity())),
        )
    }
}

impl HasRelativeBoundPair for BoundedRelativeInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        RelativeBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        self.start().to_start_bound()
    }

    fn rel_end(&self) -> RelativeEndBound {
        self.end().to_end_bound()
    }
}

impl IsEmpty for BoundedRelativeInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<(RelativeFiniteStartBound, RelativeFiniteEndBound)> for BoundedRelativeInterval {
    fn from((start, end): (RelativeFiniteStartBound, RelativeFiniteEndBound)) -> Self {
        Self::new(start, end)
    }
}

impl From<(SignedDuration, SignedDuration)> for BoundedRelativeInterval {
    fn from((start, end): (SignedDuration, SignedDuration)) -> Self {
        BoundedRelativeInterval::from_offsets(start, end)
    }
}

impl From<((SignedDuration, BoundInclusivity), (SignedDuration, BoundInclusivity))> for BoundedRelativeInterval {
    fn from(
        ((start, start_inclusivity), (end, end_inclusivity)): (
            (SignedDuration, BoundInclusivity),
            (SignedDuration, BoundInclusivity),
        ),
    ) -> Self {
        BoundedRelativeInterval::from_offsets_incl(start, start_inclusivity, end, end_inclusivity)
    }
}

impl From<(RelativeFiniteBoundPosition, RelativeFiniteBoundPosition)> for BoundedRelativeInterval {
    fn from((start, end): (RelativeFiniteBoundPosition, RelativeFiniteBoundPosition)) -> Self {
        Self::new(start.to_finite_start_bound(), end.to_finite_end_bound())
    }
}

impl From<Range<SignedDuration>> for BoundedRelativeInterval {
    fn from(range: Range<SignedDuration>) -> Self {
        BoundedRelativeInterval::from_offsets_incl(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<SignedDuration>> for BoundedRelativeInterval {
    fn from(range: RangeInclusive<SignedDuration>) -> Self {
        BoundedRelativeInterval::from_offsets_incl(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

/// Error that can occur when trying to convert [`RelativeBoundPair`] into [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundedRelativeIntervalTryFromRelativeBoundPairError;

impl Display for BoundedRelativeIntervalTryFromRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeBoundPair` into `BoundedRelativeInterval`"
        )
    }
}

impl Error for BoundedRelativeIntervalTryFromRelativeBoundPairError {}

impl TryFrom<RelativeBoundPair> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalTryFromRelativeBoundPairError;

    fn try_from(value: RelativeBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
                Ok(BoundedRelativeInterval::new(finite_start, finite_end))
            },
            _ => Err(BoundedRelativeIntervalTryFromRelativeBoundPairError),
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

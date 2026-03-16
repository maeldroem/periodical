//! Absolute half-bounded interval
//! 
//! A half-bounded interval has a reference time and an opening direction.
//! 
//! Similar to the other specific interval types, its [openness](Openness) cannot change.
//! That is to say a half-bounded interval must remain a half-bounded interval.
//! It cannot mutate from being a half-bounded interval to a bounded interval.
//! 
//! Instead, if you are looking for an absolute interval that doesn't keep the [openness](Openness) invariant,
//! see [`AbsoluteBoundPair`].

use std::error::Error;
use std::fmt::Display;
use std::ops::{RangeFrom, RangeTo, RangeToInclusive};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    HasAbsoluteBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity, Duration as IntervalDuration, HasBoundInclusivity, HasDuration, HasOpenness, HasRelativity, Interval, OpeningDirection, Openness, Relativity
};

/// A half-bounded absolute interval
/// 
/// A half-bounded interval has a reference time and an opening direction.
/// 
/// Similar to the other specific interval types, its [openness](Openness) cannot change.
/// That is to say a half-bounded interval must remain a half-bounded interval.
/// It cannot mutate from being a half-bounded interval to a bounded interval.
/// 
/// Instead, if you are looking for an absolute interval that doesn't keep the [openness](Openness) invariant,
/// see [`AbsoluteBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct HalfBoundedAbsoluteInterval {
    reference: Timestamp,
    opening_direction: OpeningDirection,
    reference_inclusivity: BoundInclusivity,
}

impl HalfBoundedAbsoluteInterval {
    /// Creates a new [`HalfBoundedAbsoluteInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_time);
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new(reference: Timestamp, opening_direction: OpeningDirection) -> Self {
        HalfBoundedAbsoluteInterval {
            reference,
            opening_direction,
            reference_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] with the given bound inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_time);
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        reference: Timestamp,
        reference_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfBoundedAbsoluteInterval {
            reference,
            opening_direction,
            reference_inclusivity,
        }
    }

    /// Returns the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference(&self) -> Timestamp {
        self.reference
    }

    /// Returns the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference time
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference_inclusivity
    }

    /// Sets the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_ref_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// half_bounded_interval.set_reference(new_ref_time);
    ///
    /// assert_eq!(half_bounded_interval.reference(), new_ref_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_reference(&mut self, new_reference: Timestamp) {
        self.reference = new_reference;
    }

    /// Sets the inclusivity of the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded_interval.set_reference_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_reference_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_inclusivity = new_inclusivity;
    }

    /// Sets the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded_interval.set_opening_direction(OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        self.opening_direction = new_opening_direction;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalCreationError {
    /// Reference date could not be created as it was out of range
    OutOfRangeReferenceDate,
    /// Reference time could not be created as positioned in a time gap
    ///
    /// Time gaps are often created by daylight savings time (DST), where a given duration can be skipped,
    /// therefore creating either a fold or a gap in time.
    ReferenceTimeInTimeGap,
    /// Something went wrong when computing a date
    ///
    /// This does not mean that the resulting date was out of range, but rather that something failed
    /// in the process of calculating a date.
    DateOperationError,
}

impl Display for HalfBoundedAbsoluteIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeReferenceDate => write!(f, "Reference date could not be created as it was out of range"),
            Self::ReferenceTimeInTimeGap => {
                write!(f, "Reference time could not be created as positioned in a time gap")
            },
            Self::DateOperationError => write!(f, "Something went wrong when computing a date"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalCreationError {}

impl Interval for HalfBoundedAbsoluteInterval {}

impl HasOpenness for HalfBoundedAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for HalfBoundedAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasAbsoluteBoundPair for HalfBoundedAbsoluteInterval {
    fn abs_bound_pair(&self) -> AbsoluteBoundPair {
        AbsoluteBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteStartBound::InfinitePast,
            OpeningDirection::ToFuture => AbsoluteFiniteBound::new_with_inclusivity(
                self.reference,
                self.reference_inclusivity,
            ).to_start_bound(),
        }
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteFiniteBound::new_with_inclusivity(
                self.reference,
                self.reference_inclusivity,
            ).to_end_bound(),
            OpeningDirection::ToFuture => AbsoluteEndBound::InfiniteFuture,
        }
    }
}

impl From<(Timestamp, OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from((time, direction): (Timestamp, OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new(time, direction)
    }
}

impl From<((Timestamp, BoundInclusivity), OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from(((time, inclusivity), direction): ((Timestamp, BoundInclusivity), OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(time, inclusivity, direction)
    }
}

impl From<RangeFrom<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeFrom<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeTo<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

/// Errors that can occur when trying to convert [`AbsoluteBoundPair`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalFromAbsoluteBoundPairError {
    NotHalfBoundedInterval,
}

impl Display for HalfBoundedAbsoluteIntervalFromAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotHalfBoundedInterval => write!(f, "Not a half-bounded interval"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalFromAbsoluteBoundPairError {}

impl TryFrom<AbsoluteBoundPair> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalFromAbsoluteBoundPairError;

    fn try_from(value: AbsoluteBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(finite_end)) => {
                Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    finite_end.time(),
                    finite_end.inclusivity(),
                    OpeningDirection::ToPast,
                ))
            },
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::InfiniteFuture) => {
                Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity(),
                    OpeningDirection::ToFuture,
                ))
            },
            _ => Err(Self::Error::NotHalfBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`AbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {
    WrongVariant,
}

impl Display for HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::HalfBounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

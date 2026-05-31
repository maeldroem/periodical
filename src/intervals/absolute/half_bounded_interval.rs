//! Absolute half-bounded interval
//!
//! A half-bounded interval has a reference time and an opening direction.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a half-bounded interval must remain a
//! half-bounded interval. It cannot mutate from being a half-bounded interval
//! to a bounded interval.
//!
//! Instead, if you are looking for an absolute interval that doesn't keep the
//! [openness](Openness) invariant, see [`AbsoluteBoundPair`].

use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeFrom, RangeTo, RangeToInclusive};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteInterval,
    HalfBoundedToFutureAbsoluteInterval,
    HalfBoundedToPastAbsoluteInterval,
    HasAbsoluteBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    HasBoundInclusivity,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};

/// A half-bounded absolute interval
///
/// A half-bounded interval has a reference time and an opening direction.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a half-bounded interval must remain a
/// half-bounded interval. It cannot mutate from being a half-bounded interval
/// to a bounded interval.
///
/// Instead, if you are looking for an absolute interval that doesn't keep the
/// [openness](Openness) invariant, see [`AbsoluteBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum HalfBoundedAbsoluteInterval {
    ToFuture(HalfBoundedToFutureAbsoluteInterval),
    ToPast(HalfBoundedToPastAbsoluteInterval),
}

impl HalfBoundedAbsoluteInterval {
    pub fn new(reference: AbsoluteFiniteBoundPosition, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureAbsoluteInterval::new(
                reference.to_finite_start_bound(),
            )),
            OpeningDirection::ToPast => {
                Self::ToPast(HalfBoundedToPastAbsoluteInterval::new(reference.to_finite_end_bound()))
            },
        }
    }

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
    /// let half_bounded_interval =
    ///     HalfBoundedAbsoluteInterval::new(ref_time, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_time);
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToPast
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new_from_time(reference: Timestamp, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureAbsoluteInterval::new_from_time(reference)),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastAbsoluteInterval::new_from_time(reference)),
        }
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] with the given bound
    /// inclusivities
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
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToFuture
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new_from_time_and_inclusivity(
        reference: Timestamp,
        reference_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(
                HalfBoundedToFutureAbsoluteInterval::new_from_time_and_inclusivity(reference, reference_inclusivity),
            ),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastAbsoluteInterval::new_from_time_and_inclusivity(
                reference,
                reference_inclusivity,
            )),
        }
    }

    /// Attempts to create a [`HalfBoundedAbsoluteInterval`] from a [`Timestamp`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedAbsoluteIntervalTryFromRangeError`] if there is not exactly
    /// one [unbounded](Bound::Unbounded) range bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalTryFromRangeError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let reference = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let interval = HalfBoundedAbsoluteInterval::try_from_range(..reference)?;
    ///
    /// assert_eq!(interval.reference(), reference);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedAbsoluteIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(_) | Bound::Excluded(_), Bound::Included(_) | Bound::Excluded(_))
            | (Bound::Unbounded, Bound::Unbounded) => Err(HalfBoundedAbsoluteIntervalTryFromRangeError),
            (Bound::Unbounded, Bound::Included(&reference)) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Unbounded, Bound::Excluded(&reference)) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Included(&reference), Bound::Unbounded) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
            (Bound::Excluded(&reference), Bound::Unbounded) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        }
    }

    pub fn reference(&self) -> AbsoluteFiniteBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_finite_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_finite_bound(),
        }
    }

    pub fn reference_pos(&self) -> AbsoluteFiniteBoundPosition {
        self.reference().pos()
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
    /// let half_bounded_interval =
    ///     HalfBoundedAbsoluteInterval::new(ref_time, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference_time(&self) -> Timestamp {
        self.reference().pos().time()
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
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference().pos().inclusivity()
    }

    pub fn set_reference(&mut self, new_reference: AbsoluteFiniteBound) {
        match new_reference {
            AbsoluteFiniteBound::Start(finite_start) => {
                *self = Self::ToFuture(HalfBoundedToFutureAbsoluteInterval::new(finite_start))
            },
            AbsoluteFiniteBound::End(finite_end) => {
                *self = Self::ToPast(HalfBoundedToPastAbsoluteInterval::new(finite_end))
            },
        }
    }

    pub fn set_reference_pos(&mut self, new_reference_pos: AbsoluteFiniteBoundPosition) {
        match self {
            Self::ToFuture(hb_to_future) => *hb_to_future.start_mut().pos_mut() = new_reference_pos,
            Self::ToPast(hb_to_past) => *hb_to_past.end_mut().pos_mut() = new_reference_pos,
        }
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
    /// let mut half_bounded_interval =
    ///     HalfBoundedAbsoluteInterval::new(ref_time, OpeningDirection::ToFuture);
    ///
    /// let new_ref_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// half_bounded_interval.set_reference(new_ref_time);
    ///
    /// assert_eq!(half_bounded_interval.reference(), new_ref_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_reference_time(&mut self, new_reference_time: Timestamp) {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start_mut().pos_mut().set_time(new_reference_time),
            Self::ToPast(hb_to_past) => hb_to_past.end_mut().pos_mut().set_time(new_reference_time),
        }
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
    /// let mut half_bounded_interval =
    ///     HalfBoundedAbsoluteInterval::new(ref_time, OpeningDirection::ToFuture);
    ///
    /// half_bounded_interval.set_reference_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_reference_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start_mut().pos_mut().set_inclusivity(new_inclusivity),
            Self::ToPast(hb_to_past) => hb_to_past.end_mut().pos_mut().set_inclusivity(new_inclusivity),
        }
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
    /// let mut half_bounded_interval =
    ///     HalfBoundedAbsoluteInterval::new(ref_time, OpeningDirection::ToFuture);
    ///
    /// half_bounded_interval.set_opening_direction(OpeningDirection::ToPast);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToPast
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        match new_opening_direction {
            OpeningDirection::ToFuture => {
                *self = Self::ToFuture(HalfBoundedToFutureAbsoluteInterval::new(
                    self.reference_pos().to_finite_start_bound(),
                ));
            },
            OpeningDirection::ToPast => {
                *self = Self::ToPast(HalfBoundedToPastAbsoluteInterval::new(
                    self.reference_pos().to_finite_end_bound(),
                ));
            },
        }
    }

    pub fn opposite(self) -> Self {
        match self {
            Self::ToFuture(hb_to_future) => Self::ToPast(hb_to_future.opposite()),
            Self::ToPast(hb_to_past) => Self::ToFuture(hb_to_past.opposite()),
        }
    }

    pub fn half_bounded_to_future(self) -> Option<HalfBoundedToFutureAbsoluteInterval> {
        match self {
            Self::ToFuture(hb_to_future) => Some(hb_to_future),
            Self::ToPast(_) => None,
        }
    }

    pub fn half_bounded_to_past(self) -> Option<HalfBoundedToPastAbsoluteInterval> {
        match self {
            Self::ToFuture(_) => None,
            Self::ToPast(hb_to_past) => Some(hb_to_past),
        }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeReference,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedAbsoluteIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeReference => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalCreationError {}

/// Error that can occur when trying to convert a [`Timestamp`] range into a [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsoluteIntervalTryFromRangeError;

impl Display for HalfBoundedAbsoluteIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedAbsoluteIntervalTryFromRangeError {}

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
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_start_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.start(),
        }
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.end(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_end_bound(),
        }
    }
}

impl IsEmpty for HalfBoundedAbsoluteInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<(Timestamp, OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from((time, direction): (Timestamp, OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new_from_time(time, direction)
    }
}

impl From<(Timestamp, BoundInclusivity, OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from((time, inclusivity, direction): (Timestamp, BoundInclusivity, OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(time, inclusivity, direction)
    }
}

impl From<(AbsoluteFiniteBoundPosition, OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from((reference, opening_direction): (AbsoluteFiniteBoundPosition, OpeningDirection)) -> Self {
        Self::new_from_time_and_inclusivity(reference.time(), reference.inclusivity(), opening_direction)
    }
}

impl From<RangeFrom<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeFrom<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeTo<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

/// Error that can occur when trying to convert [`AbsoluteBoundPair`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError;

impl Display for HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteBoundPair` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError {}

impl TryFrom<AbsoluteBoundPair> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError;

    fn try_from(value: AbsoluteBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(finite_end)) => {
                Ok(Self::ToPast(HalfBoundedToPastAbsoluteInterval::new(finite_end)))
            },
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::InfiniteFuture) => {
                Ok(Self::ToFuture(HalfBoundedToFutureAbsoluteInterval::new(finite_start)))
            },
            _ => Err(HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`AbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError;

impl Display for HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteInterval` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError;

impl Display for HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteInterval` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError {}

impl TryFrom<EmptiableAbsoluteInterval> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError;

    fn try_from(value: EmptiableAbsoluteInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)?,
        )
        .or(Err(HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError))
    }
}

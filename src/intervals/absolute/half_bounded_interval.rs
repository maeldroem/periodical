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
//! [openness](Openness) invariant, see [`AbsBoundPair`].

use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeFrom, RangeTo, RangeToInclusive};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasAbsBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    HasBoundInclusivity,
    HasDuration,
    HasOpeningDirection,
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
/// [openness](Openness) invariant, see [`AbsBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum HalfBoundedAbsInterval {
    ToFuture(HalfBoundedToFutureAbsInterval),
    ToPast(HalfBoundedToPastAbsInterval),
}

impl HalfBoundedAbsInterval {
    pub fn new(reference: AbsFiniteBoundPos, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => {
                Self::ToFuture(HalfBoundedToFutureAbsInterval::new(reference.to_finite_start_bound()))
            },
            OpeningDirection::ToPast => {
                Self::ToPast(HalfBoundedToPastAbsInterval::new(reference.to_finite_end_bound()))
            },
        }
    }

    /// Creates a new [`HalfBoundedAbsInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval =
    ///     HalfBoundedAbsInterval::new(ref_time, OpeningDirection::ToPast);
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
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureAbsInterval::new_from_time(reference)),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastAbsInterval::new_from_time(reference)),
        }
    }

    /// Creates a new [`HalfBoundedAbsInterval`] with the given bound
    /// inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsInterval::new_with_inclusivity(
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
                HalfBoundedToFutureAbsInterval::new_from_time_and_inclusivity(reference, reference_inclusivity),
            ),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastAbsInterval::new_from_time_and_inclusivity(
                reference,
                reference_inclusivity,
            )),
        }
    }

    /// Attempts to create a [`HalfBoundedAbsInterval`] from a [`Timestamp`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedAbsIntervalTryFromRangeError`] if there is not exactly
    /// one [unbounded](Bound::Unbounded) range bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{HalfBoundedAbsInterval, HalfBoundedAbsIntervalTryFromRangeError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let reference = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let interval = HalfBoundedAbsInterval::try_from_range(..reference)?;
    ///
    /// assert_eq!(interval.reference(), reference);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedAbsIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(_) | Bound::Excluded(_), Bound::Included(_) | Bound::Excluded(_))
            | (Bound::Unbounded, Bound::Unbounded) => Err(HalfBoundedAbsIntervalTryFromRangeError),
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

    pub fn reference(&self) -> AbsFiniteBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_finite_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_finite_bound(),
        }
    }

    pub fn reference_pos(&self) -> AbsFiniteBoundPos {
        self.reference().pos()
    }

    /// Returns the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval =
    ///     HalfBoundedAbsInterval::new(ref_time, OpeningDirection::ToPast);
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
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsInterval::new_with_inclusivity(
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

    pub fn set_reference(&mut self, new_reference: AbsFiniteBound) {
        match new_reference {
            AbsFiniteBound::Start(finite_start) => {
                *self = Self::ToFuture(HalfBoundedToFutureAbsInterval::new(finite_start))
            },
            AbsFiniteBound::End(finite_end) => *self = Self::ToPast(HalfBoundedToPastAbsInterval::new(finite_end)),
        }
    }

    pub fn set_reference_pos(&mut self, new_reference_pos: AbsFiniteBoundPos) {
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
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedAbsInterval::new(ref_time, OpeningDirection::ToFuture);
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
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedAbsInterval::new(ref_time, OpeningDirection::ToFuture);
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
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedAbsInterval::new(ref_time, OpeningDirection::ToFuture);
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
                *self = Self::ToFuture(HalfBoundedToFutureAbsInterval::new(
                    self.reference_pos().to_finite_start_bound(),
                ));
            },
            OpeningDirection::ToPast => {
                *self = Self::ToPast(HalfBoundedToPastAbsInterval::new(
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

    pub fn half_bounded_to_future(self) -> Option<HalfBoundedToFutureAbsInterval> {
        match self {
            Self::ToFuture(hb_to_future) => Some(hb_to_future),
            Self::ToPast(_) => None,
        }
    }

    pub fn half_bounded_to_past(self) -> Option<HalfBoundedToPastAbsInterval> {
        match self {
            Self::ToFuture(_) => None,
            Self::ToPast(hb_to_past) => Some(hb_to_past),
        }
    }

    /// Wraps the interval in [`AbsInterval`]
    #[must_use]
    pub fn to_interval(self) -> AbsInterval {
        AbsInterval::from(self)
    }

    /// Wraps the interval in [`EmptiableAbsInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableAbsInterval {
        EmptiableAbsInterval::from(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeReference,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedAbsIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeReference => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedAbsIntervalCreationError {}

/// Error that can occur when trying to convert a [`Timestamp`] range into a [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromRangeError;

impl Display for HalfBoundedAbsIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromRangeError {}

impl Interval for HalfBoundedAbsInterval {}

impl HasOpenness for HalfBoundedAbsInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedAbsInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Abs
    }
}

impl HasDuration for HalfBoundedAbsInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedAbsInterval {
    fn opening_direction(&self) -> OpeningDirection {
        match self {
            Self::ToFuture(_) => OpeningDirection::ToFuture,
            Self::ToPast(_) => OpeningDirection::ToPast,
        }
    }
}

impl HasAbsBoundPair for HalfBoundedAbsInterval {
    fn abs_bound_pair(&self) -> AbsBoundPair {
        AbsBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsStartBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_start_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.start(),
        }
    }

    fn abs_end(&self) -> AbsEndBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.end(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_end_bound(),
        }
    }
}

impl IsEmpty for HalfBoundedAbsInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<(Timestamp, OpeningDirection)> for HalfBoundedAbsInterval {
    fn from((time, direction): (Timestamp, OpeningDirection)) -> Self {
        HalfBoundedAbsInterval::new_from_time(time, direction)
    }
}

impl From<(Timestamp, BoundInclusivity, OpeningDirection)> for HalfBoundedAbsInterval {
    fn from((time, inclusivity, direction): (Timestamp, BoundInclusivity, OpeningDirection)) -> Self {
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(time, inclusivity, direction)
    }
}

impl From<(AbsFiniteBoundPos, OpeningDirection)> for HalfBoundedAbsInterval {
    fn from((reference, opening_direction): (AbsFiniteBoundPos, OpeningDirection)) -> Self {
        Self::new_from_time_and_inclusivity(reference.time(), reference.inclusivity(), opening_direction)
    }
}

impl From<RangeFrom<Timestamp>> for HalfBoundedAbsInterval {
    fn from(range: RangeFrom<Timestamp>) -> Self {
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<Timestamp>> for HalfBoundedAbsInterval {
    fn from(range: RangeTo<Timestamp>) -> Self {
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedAbsInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<HalfBoundedToFutureAbsInterval> for HalfBoundedAbsInterval {
    fn from(value: HalfBoundedToFutureAbsInterval) -> Self {
        HalfBoundedAbsInterval::ToFuture(value)
    }
}

impl From<HalfBoundedToPastAbsInterval> for HalfBoundedAbsInterval {
    fn from(value: HalfBoundedToPastAbsInterval) -> Self {
        HalfBoundedAbsInterval::ToPast(value)
    }
}

/// Error that can occur when trying to convert [`AbsBoundPair`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromAbsBoundPairError;

impl Display for HalfBoundedAbsIntervalTryFromAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsBoundPair` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromAbsBoundPairError {}

impl TryFrom<AbsBoundPair> for HalfBoundedAbsInterval {
    type Error = HalfBoundedAbsIntervalTryFromAbsBoundPairError;

    fn try_from(value: AbsBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsStartBound::InfinitePast, AbsEndBound::Finite(finite_end)) => {
                Ok(Self::ToPast(HalfBoundedToPastAbsInterval::new(finite_end)))
            },
            (AbsStartBound::Finite(finite_start), AbsEndBound::InfiniteFuture) => {
                Ok(Self::ToFuture(HalfBoundedToFutureAbsInterval::new(finite_start)))
            },
            _ => Err(HalfBoundedAbsIntervalTryFromAbsBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`AbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromAbsIntervalError;

impl Display for HalfBoundedAbsIntervalTryFromAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromAbsIntervalError {}

impl TryFrom<AbsInterval> for HalfBoundedAbsInterval {
    type Error = HalfBoundedAbsIntervalTryFromAbsIntervalError;

    fn try_from(value: AbsInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedAbsIntervalTryFromAbsIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError;

impl Display for HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError {}

impl TryFrom<EmptiableAbsInterval> for HalfBoundedAbsInterval {
    type Error = HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError;

    fn try_from(value: EmptiableAbsInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError)?,
        )
        .or(Err(HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError))
    }
}

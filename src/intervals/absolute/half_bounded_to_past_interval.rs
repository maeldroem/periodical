use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeTo, RangeToInclusive};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteFiniteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HalfBoundedToFutureAbsoluteInterval,
    HasAbsoluteBoundPair,
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
/// [openness](Openness) invariant, see [`AbsoluteBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct HalfBoundedToPastAbsoluteInterval(pub(crate) AbsoluteFiniteEndBound);

impl HalfBoundedToPastAbsoluteInterval {
    pub fn new(end: AbsoluteFiniteEndBound) -> Self {
        HalfBoundedToPastAbsoluteInterval(end)
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
    pub fn new_from_time(reference: Timestamp) -> Self {
        Self::new(AbsoluteFiniteBoundPosition::new(reference).to_finite_end_bound())
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
    pub fn new_from_time_and_inclusivity(reference: Timestamp, reference_inclusivity: BoundInclusivity) -> Self {
        HalfBoundedToPastAbsoluteInterval::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(reference, reference_inclusivity).to_finite_end_bound(),
        )
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
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToPastAbsoluteIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Unbounded, Bound::Included(&reference)) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
            )),
            (Bound::Unbounded, Bound::Excluded(&reference)) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
            )),
            _ => Err(HalfBoundedToPastAbsoluteIntervalTryFromRangeError),
        }
    }

    pub fn start(&self) -> AbsoluteStartBound {
        AbsoluteStartBound::InfinitePast
    }

    pub fn end(&self) -> AbsoluteFiniteEndBound {
        self.0
    }

    pub fn end_mut(&mut self) -> &mut AbsoluteFiniteEndBound {
        &mut self.0
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
    pub fn end_time(&self) -> Timestamp {
        self.end().pos().time()
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
    pub fn end_inclusivity(&self) -> BoundInclusivity {
        self.end().pos().inclusivity()
    }

    pub fn set_end(&mut self, new_end: AbsoluteFiniteEndBound) {
        self.0 = new_end;
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
    pub fn set_end_time(&mut self, new_end_time: Timestamp) {
        self.end_mut().pos_mut().set_time(new_end_time);
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
        self.end_mut().pos_mut().set_inclusivity(new_inclusivity);
    }

    pub fn opposite(self) -> HalfBoundedToFutureAbsoluteInterval {
        HalfBoundedToFutureAbsoluteInterval(self.end().opposite())
    }

    pub fn to_half_bounded_interval(self) -> HalfBoundedAbsoluteInterval {
        HalfBoundedAbsoluteInterval::ToPast(self)
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
pub enum HalfBoundedToPastAbsoluteIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeEnd,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToPastAbsoluteIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeEnd => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToPastAbsoluteIntervalCreationError {}

/// Error that can occur when trying to convert a [`Timestamp`] range into a [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsoluteIntervalTryFromRangeError;

impl Display for HalfBoundedToPastAbsoluteIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsoluteIntervalTryFromRangeError {}

impl Interval for HalfBoundedToPastAbsoluteInterval {}

impl HasOpenness for HalfBoundedToPastAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToPastAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for HalfBoundedToPastAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToPastAbsoluteInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToPast
    }
}

impl HasAbsoluteBoundPair for HalfBoundedToPastAbsoluteInterval {
    fn abs_bound_pair(&self) -> AbsoluteBoundPair {
        AbsoluteBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        self.start()
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        self.end().to_end_bound()
    }
}

impl IsEmpty for HalfBoundedToPastAbsoluteInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<Timestamp> for HalfBoundedToPastAbsoluteInterval {
    fn from(time: Timestamp) -> Self {
        HalfBoundedToPastAbsoluteInterval::new_from_time(time)
    }
}

impl From<(Timestamp, BoundInclusivity)> for HalfBoundedToPastAbsoluteInterval {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        HalfBoundedToPastAbsoluteInterval::new_from_time_and_inclusivity(time, inclusivity)
    }
}

impl From<AbsoluteFiniteBoundPosition> for HalfBoundedToPastAbsoluteInterval {
    fn from(end: AbsoluteFiniteBoundPosition) -> Self {
        Self::new(end.to_finite_end_bound())
    }
}

impl From<AbsoluteFiniteEndBound> for HalfBoundedToPastAbsoluteInterval {
    fn from(end: AbsoluteFiniteEndBound) -> Self {
        Self::new(end)
    }
}

impl From<RangeTo<Timestamp>> for HalfBoundedToPastAbsoluteInterval {
    fn from(range: RangeTo<Timestamp>) -> Self {
        HalfBoundedToPastAbsoluteInterval::new_from_time_and_inclusivity(range.end, BoundInclusivity::Exclusive)
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedToPastAbsoluteInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedToPastAbsoluteInterval::new_from_time_and_inclusivity(range.end, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`AbsoluteBoundPair`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteBoundPairError;

impl Display for HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteBoundPair` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteBoundPairError {}

impl TryFrom<AbsoluteBoundPair> for HalfBoundedToPastAbsoluteInterval {
    type Error = HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteBoundPairError;

    fn try_from(value: AbsoluteBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(finite_end)) => Ok(Self::new(finite_end)),
            _ => Err(HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`AbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteIntervalError;

impl Display for HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteInterval` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for HalfBoundedToPastAbsoluteInterval {
    type Error = HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteIntervalError)?
            .half_bounded_to_past()
            .ok_or(HalfBoundedToPastAbsoluteIntervalTryFromAbsoluteIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError;

impl Display for HalfBoundedToPastAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteInterval` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError {}

impl TryFrom<EmptiableAbsoluteInterval> for HalfBoundedToPastAbsoluteInterval {
    type Error = HalfBoundedToPastAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError;

    fn try_from(value: EmptiableAbsoluteInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToPastAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)?,
        )
        .or(Err(
            HalfBoundedToPastAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError,
        ))
    }
}

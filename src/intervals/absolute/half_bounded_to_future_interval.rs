use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeFrom};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteFiniteStartBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HalfBoundedToPastAbsoluteInterval,
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
pub struct HalfBoundedToFutureAbsoluteInterval(pub(crate) AbsoluteFiniteStartBound);

impl HalfBoundedToFutureAbsoluteInterval {
    pub fn new(start: AbsoluteFiniteStartBound) -> Self {
        HalfBoundedToFutureAbsoluteInterval(start)
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
        Self::new(AbsoluteFiniteBoundPosition::new(reference).to_finite_start_bound())
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
        HalfBoundedToFutureAbsoluteInterval::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(reference, reference_inclusivity).to_finite_start_bound(),
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
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToFutureAbsoluteIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(&reference), Bound::Unbounded) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
            )),
            (Bound::Excluded(&reference), Bound::Unbounded) => Ok(Self::new_from_time_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
            )),
            _ => Err(HalfBoundedToFutureAbsoluteIntervalTryFromRangeError),
        }
    }

    pub fn start(&self) -> AbsoluteFiniteStartBound {
        self.0
    }

    pub fn start_mut(&mut self) -> &mut AbsoluteFiniteStartBound {
        &mut self.0
    }

    pub fn end(&self) -> AbsoluteEndBound {
        AbsoluteEndBound::InfiniteFuture
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
    pub fn start_time(&self) -> Timestamp {
        self.start().pos().time()
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
    pub fn start_inclusivity(&self) -> BoundInclusivity {
        self.start().pos().inclusivity()
    }

    pub fn set_start(&mut self, new_start: AbsoluteFiniteStartBound) {
        self.0 = new_start;
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
    pub fn set_start_time(&mut self, new_start_time: Timestamp) {
        self.start_mut().pos_mut().set_time(new_start_time);
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
    pub fn set_start_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.start_mut().pos_mut().set_inclusivity(new_inclusivity);
    }

    pub fn opposite(self) -> HalfBoundedToPastAbsoluteInterval {
        HalfBoundedToPastAbsoluteInterval::new(self.start().opposite())
    }

    pub fn to_half_bounded_interval(self) -> HalfBoundedAbsoluteInterval {
        HalfBoundedAbsoluteInterval::ToFuture(self)
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
pub enum HalfBoundedToFutureAbsoluteIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeStart,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToFutureAbsoluteIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStart => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToFutureAbsoluteIntervalCreationError {}

/// Error that can occur when trying to convert a [`Timestamp`] range into a [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsoluteIntervalTryFromRangeError;

impl Display for HalfBoundedToFutureAbsoluteIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsoluteIntervalTryFromRangeError {}

impl Interval for HalfBoundedToFutureAbsoluteInterval {}

impl HasOpenness for HalfBoundedToFutureAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToFutureAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for HalfBoundedToFutureAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToFutureAbsoluteInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToFuture
    }
}

impl HasAbsoluteBoundPair for HalfBoundedToFutureAbsoluteInterval {
    fn abs_bound_pair(&self) -> AbsoluteBoundPair {
        AbsoluteBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        self.start().to_start_bound()
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        self.end()
    }
}

impl IsEmpty for HalfBoundedToFutureAbsoluteInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<Timestamp> for HalfBoundedToFutureAbsoluteInterval {
    fn from(time: Timestamp) -> Self {
        HalfBoundedToFutureAbsoluteInterval::new_from_time(time)
    }
}

impl From<(Timestamp, BoundInclusivity)> for HalfBoundedToFutureAbsoluteInterval {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        HalfBoundedToFutureAbsoluteInterval::new_from_time_and_inclusivity(time, inclusivity)
    }
}

impl From<AbsoluteFiniteBoundPosition> for HalfBoundedToFutureAbsoluteInterval {
    fn from(start: AbsoluteFiniteBoundPosition) -> Self {
        Self::new(start.to_finite_start_bound())
    }
}

impl From<AbsoluteFiniteStartBound> for HalfBoundedToFutureAbsoluteInterval {
    fn from(start: AbsoluteFiniteStartBound) -> Self {
        Self::new(start)
    }
}

impl From<RangeFrom<Timestamp>> for HalfBoundedToFutureAbsoluteInterval {
    fn from(range: RangeFrom<Timestamp>) -> Self {
        HalfBoundedToFutureAbsoluteInterval::new_from_time_and_inclusivity(range.start, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`AbsoluteBoundPair`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteBoundPairError;

impl Display for HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteBoundPair` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteBoundPairError {}

impl TryFrom<AbsoluteBoundPair> for HalfBoundedToFutureAbsoluteInterval {
    type Error = HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteBoundPairError;

    fn try_from(value: AbsoluteBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::InfiniteFuture) => Ok(Self::new(finite_start)),
            _ => Err(HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`AbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteIntervalError;

impl Display for HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteInterval` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for HalfBoundedToFutureAbsoluteInterval {
    type Error = HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteIntervalError)?
            .half_bounded_to_future()
            .ok_or(HalfBoundedToFutureAbsoluteIntervalTryFromAbsoluteIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError;

impl Display for HalfBoundedToFutureAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteInterval` into `HalfBoundedAbsoluteInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError {}

impl TryFrom<EmptiableAbsoluteInterval> for HalfBoundedToFutureAbsoluteInterval {
    type Error = HalfBoundedToFutureAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError;

    fn try_from(value: EmptiableAbsoluteInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToFutureAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)?,
        )
        .or(Err(
            HalfBoundedToFutureAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError,
        ))
    }
}

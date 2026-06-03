use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeTo, RangeToInclusive};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
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
pub struct HalfBoundedToPastAbsInterval(pub(crate) AbsFiniteEndBound);

impl HalfBoundedToPastAbsInterval {
    pub fn new(end: AbsFiniteEndBound) -> Self {
        HalfBoundedToPastAbsInterval(end)
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
    pub fn new_from_time(reference: Timestamp) -> Self {
        Self::new(AbsFiniteBoundPos::new(reference).to_finite_end_bound())
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
    /// let half_bounded_interval = HalfBoundedAbsInterval::new_with_incl(
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
        HalfBoundedToPastAbsInterval::new(
            AbsFiniteBoundPos::new_with_incl(reference, reference_inclusivity).to_finite_end_bound(),
        )
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
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToPastAbsIntervalTryFromRangeError>
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
            _ => Err(HalfBoundedToPastAbsIntervalTryFromRangeError),
        }
    }

    pub fn start(&self) -> AbsStartBound {
        AbsStartBound::InfinitePast
    }

    pub fn end(&self) -> AbsFiniteEndBound {
        self.0
    }

    pub fn end_mut(&mut self) -> &mut AbsFiniteEndBound {
        &mut self.0
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
    pub fn end_time(&self) -> Timestamp {
        self.end().pos().time()
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
    /// let half_bounded_interval = HalfBoundedAbsInterval::new_with_incl(
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

    pub fn set_end(&mut self, new_end: AbsFiniteEndBound) {
        self.0 = new_end;
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
        self.end_mut().pos_mut().set_inclusivity(new_inclusivity);
    }

    pub fn opposite(self) -> HalfBoundedToFutureAbsInterval {
        HalfBoundedToFutureAbsInterval(self.end().opposite())
    }

    pub fn to_half_bounded_interval(self) -> HalfBoundedAbsInterval {
        HalfBoundedAbsInterval::ToPast(self)
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
pub enum HalfBoundedToPastAbsIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeEnd,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToPastAbsIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeEnd => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToPastAbsIntervalCreationError {}

/// Error that can occur when trying to convert a [`Timestamp`] range into a [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsIntervalTryFromRangeError;

impl Display for HalfBoundedToPastAbsIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsIntervalTryFromRangeError {}

impl Interval for HalfBoundedToPastAbsInterval {}

impl HasOpenness for HalfBoundedToPastAbsInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToPastAbsInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Abs
    }
}

impl HasDuration for HalfBoundedToPastAbsInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToPastAbsInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToPast
    }
}

impl HasAbsBoundPair for HalfBoundedToPastAbsInterval {
    fn abs_bound_pair(&self) -> AbsBoundPair {
        AbsBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsStartBound {
        self.start()
    }

    fn abs_end(&self) -> AbsEndBound {
        self.end().to_end_bound()
    }
}

impl IsEmpty for HalfBoundedToPastAbsInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<Timestamp> for HalfBoundedToPastAbsInterval {
    fn from(time: Timestamp) -> Self {
        HalfBoundedToPastAbsInterval::new_from_time(time)
    }
}

impl From<(Timestamp, BoundInclusivity)> for HalfBoundedToPastAbsInterval {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        HalfBoundedToPastAbsInterval::new_from_time_and_inclusivity(time, inclusivity)
    }
}

impl From<AbsFiniteBoundPos> for HalfBoundedToPastAbsInterval {
    fn from(end: AbsFiniteBoundPos) -> Self {
        Self::new(end.to_finite_end_bound())
    }
}

impl From<AbsFiniteEndBound> for HalfBoundedToPastAbsInterval {
    fn from(end: AbsFiniteEndBound) -> Self {
        Self::new(end)
    }
}

impl From<RangeTo<Timestamp>> for HalfBoundedToPastAbsInterval {
    fn from(range: RangeTo<Timestamp>) -> Self {
        HalfBoundedToPastAbsInterval::new_from_time_and_inclusivity(range.end, BoundInclusivity::Exclusive)
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedToPastAbsInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedToPastAbsInterval::new_from_time_and_inclusivity(range.end, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`AbsBoundPair`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError;

impl Display for HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsBoundPair` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError {}

impl TryFrom<AbsBoundPair> for HalfBoundedToPastAbsInterval {
    type Error = HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError;

    fn try_from(value: AbsBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsStartBound::InfinitePast, AbsEndBound::Finite(finite_end)) => Ok(Self::new(finite_end)),
            _ => Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`AbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsIntervalTryFromAbsIntervalError;

impl Display for HalfBoundedToPastAbsIntervalTryFromAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsIntervalTryFromAbsIntervalError {}

impl TryFrom<AbsInterval> for HalfBoundedToPastAbsInterval {
    type Error = HalfBoundedToPastAbsIntervalTryFromAbsIntervalError;

    fn try_from(value: AbsInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToPastAbsIntervalTryFromAbsIntervalError)?
            .half_bounded_to_past()
            .ok_or(HalfBoundedToPastAbsIntervalTryFromAbsIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError;

impl Display for HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError {}

impl TryFrom<EmptiableAbsInterval> for HalfBoundedToPastAbsInterval {
    type Error = HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError;

    fn try_from(value: EmptiableAbsInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError)?,
        )
        .or(Err(HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError))
    }
}

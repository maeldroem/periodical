//! Absolute half-bounded interval opened to the future
//!
//! A half-bounded interval opened to the future only has finite start bound
//! and an infinite end bound.
//!
//! Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
//! cannot change.
//!
//! If you are looking for a half-bounded absolute interval that doesn't keep the
//! [opening direction](OpeningDirection) invariant, see [`HalfBoundedAbsInterval`].

use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeFrom};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsFiniteStartBound,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
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

/// Absolute half-bounded interval opened to the future
///
/// A half-bounded interval opened to the future only has finite start bound
/// and an infinite end bound.
///
/// Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
/// cannot change.
///
/// If you are looking for a half-bounded absolute interval that doesn't keep the
/// [opening direction](OpeningDirection) invariant, see [`HalfBoundedAbsInterval`].
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsInterval(pub(crate) AbsFiniteStartBound);

impl HalfBoundedToFutureAbsInterval {
    /// Creates a new half-bounded interval opened to the future
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsFiniteBoundPos,
    /// #     HalfBoundedToFutureAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToFutureAbsInterval::new(AbsFiniteBoundPos::new(time).to_finite_start_bound());
    ///
    /// assert_eq!(half_bounded.start_time(), time);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new(start: AbsFiniteStartBound) -> Self {
        HalfBoundedToFutureAbsInterval(start)
    }

    /// Creates a new half-bounded interval opened to the future from a time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToFutureAbsInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedToFutureAbsInterval::from_time(time);
    ///
    /// assert_eq!(half_bounded.start_time(), time);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_time(start: Timestamp) -> Self {
        Self::new(AbsFiniteBoundPos::new(start).to_finite_start_bound())
    }

    /// Creates a new half-bounded interval opened to the future from a time
    /// and a bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToFutureAbsInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToFutureAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.start_time(), time);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_time_incl(reference: Timestamp, reference_inclusivity: BoundInclusivity) -> Self {
        HalfBoundedToFutureAbsInterval::new(
            AbsFiniteBoundPos::new_with_incl(reference, reference_inclusivity).to_finite_start_bound(),
        )
    }

    /// Attempts to create a [`HalfBoundedAbsInterval`] from a [`Timestamp`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedToFutureAbsIntervalTryFromRangeError`] if the range's end bound
    /// is not [`Unbounded`](Bound::Unbounded).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToFutureAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedToFutureAbsInterval::try_from_range(time..)?;
    ///
    /// assert_eq!(half_bounded.start_time(), time);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToFutureAbsIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(&reference), Bound::Unbounded) => {
                Ok(Self::from_time_incl(reference, BoundInclusivity::Inclusive))
            },
            (Bound::Excluded(&reference), Bound::Unbounded) => {
                Ok(Self::from_time_incl(reference, BoundInclusivity::Exclusive))
            },
            _ => Err(HalfBoundedToFutureAbsIntervalTryFromRangeError),
        }
    }

    /// Returns the finite start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     HalfBoundedToFutureAbsInterval,
    /// #     AbsFiniteBoundPos,
    /// # };
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToFutureAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.start(),
    ///     AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_finite_start_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start(&self) -> AbsFiniteStartBound {
        self.0
    }

    /// Returns the infinite end bound
    #[must_use]
    pub fn end(&self) -> AbsEndBound {
        AbsEndBound::InfiniteFuture
    }

    /// Returns the start time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToFutureAbsInterval;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedToFutureAbsInterval::from_time(time);
    ///
    /// assert_eq!(half_bounded.start_time(), time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start_time(&self) -> Timestamp {
        self.start().pos().time()
    }

    /// Returns the start bound's inclusivity
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToFutureAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToFutureAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start_inclusivity(&self) -> BoundInclusivity {
        self.start().pos().inclusivity()
    }

    /// Returns a mutable pointer to the finite start bound
    ///
    /// This is used for mutating which position the start bound represents.
    #[must_use]
    pub fn start_mut(&mut self) -> &mut AbsFiniteStartBound {
        &mut self.0
    }

    /// Sets the finite start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsFiniteBoundPos,
    /// #     HalfBoundedToFutureAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let new_start = AbsFiniteBoundPos::new_with_incl(
    ///     "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_finite_start_bound();
    /// let mut half_bounded =
    ///     HalfBoundedToFutureAbsInterval::from_time("2020-01-01 00:00:00Z".parse::<Timestamp>()?);
    ///
    /// half_bounded.set_start(new_start);
    ///
    /// assert_eq!(half_bounded.start(), new_start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start(&mut self, new_start: AbsFiniteStartBound) {
        self.0 = new_start;
    }

    /// Sets the start time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToFutureAbsInterval;
    /// let mut half_bounded =
    ///     HalfBoundedToFutureAbsInterval::from_time("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
    ///
    /// let new_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// half_bounded.set_start_time(new_time);
    ///
    /// assert_eq!(half_bounded.start_time(), new_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start_time(&mut self, new_start_time: Timestamp) {
        self.start_mut().pos_mut().set_time(new_start_time);
    }

    /// Sets the start bound's inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToFutureAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut half_bounded =
    ///     HalfBoundedToFutureAbsInterval::from_time("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
    ///
    /// half_bounded.set_start_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.start_mut().pos_mut().set_inclusivity(new_inclusivity);
    }

    /// Returns the opposite half-bounded interval opened to the past
    ///
    /// Returns a half-bounded interval of opposite opening direction and bound inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     HalfBoundedToFutureAbsInterval,
    /// #     HalfBoundedToPastAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedToFutureAbsInterval::from_time(time);
    ///
    /// assert_eq!(
    ///     half_bounded.opposite(),
    ///     HalfBoundedToPastAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(self) -> HalfBoundedToPastAbsInterval {
        HalfBoundedToPastAbsInterval::new(self.start().opposite())
    }

    /// Wraps `self` in [`HalfBoundedAbsInterval`]
    #[must_use]
    pub fn to_half_bounded_interval(self) -> HalfBoundedAbsInterval {
        HalfBoundedAbsInterval::ToFuture(self)
    }

    /// Converts `self` into [`AbsInterval`]
    #[must_use]
    pub fn to_interval(self) -> AbsInterval {
        AbsInterval::from(self)
    }

    /// Converts `self` into [`EmptiableAbsInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableAbsInterval {
        EmptiableAbsInterval::from(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedToFutureAbsIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeStart,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToFutureAbsIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStart => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToFutureAbsIntervalCreationError {}

/// Error that can occur when trying to convert a [`Timestamp`] range into a [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsIntervalTryFromRangeError;

impl Display for HalfBoundedToFutureAbsIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsIntervalTryFromRangeError {}

impl Interval for HalfBoundedToFutureAbsInterval {}

impl HasOpenness for HalfBoundedToFutureAbsInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToFutureAbsInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Abs
    }
}

impl HasDuration for HalfBoundedToFutureAbsInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToFutureAbsInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToFuture
    }
}

impl HasAbsBoundPair for HalfBoundedToFutureAbsInterval {
    fn abs_bound_pair(&self) -> AbsBoundPair {
        AbsBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsStartBound {
        self.start().to_start_bound()
    }

    fn abs_end(&self) -> AbsEndBound {
        self.end()
    }
}

impl IsEmpty for HalfBoundedToFutureAbsInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<Timestamp> for HalfBoundedToFutureAbsInterval {
    fn from(time: Timestamp) -> Self {
        HalfBoundedToFutureAbsInterval::from_time(time)
    }
}

impl From<(Timestamp, BoundInclusivity)> for HalfBoundedToFutureAbsInterval {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        HalfBoundedToFutureAbsInterval::from_time_incl(time, inclusivity)
    }
}

impl From<AbsFiniteBoundPos> for HalfBoundedToFutureAbsInterval {
    fn from(start: AbsFiniteBoundPos) -> Self {
        Self::new(start.to_finite_start_bound())
    }
}

impl From<AbsFiniteStartBound> for HalfBoundedToFutureAbsInterval {
    fn from(start: AbsFiniteStartBound) -> Self {
        Self::new(start)
    }
}

impl From<RangeFrom<Timestamp>> for HalfBoundedToFutureAbsInterval {
    fn from(range: RangeFrom<Timestamp>) -> Self {
        HalfBoundedToFutureAbsInterval::from_time_incl(range.start, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`AbsBoundPair`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError;

impl Display for HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsBoundPair` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError {}

impl TryFrom<AbsBoundPair> for HalfBoundedToFutureAbsInterval {
    type Error = HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError;

    fn try_from(value: AbsBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsStartBound::Finite(finite_start), AbsEndBound::InfiniteFuture) => Ok(Self::new(finite_start)),
            _ => Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`AbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError;

impl Display for HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError {}

impl TryFrom<AbsInterval> for HalfBoundedToFutureAbsInterval {
    type Error = HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError;

    fn try_from(value: AbsInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError)?
            .half_bounded_to_future()
            .ok_or(HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError;

impl Display for HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError {}

impl TryFrom<EmptiableAbsInterval> for HalfBoundedToFutureAbsInterval {
    type Error = HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError;

    fn try_from(value: EmptiableAbsInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError)?,
        )
        .or(Err(HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError))
    }
}

//! Absolute half-bounded interval opened to the past
//!
//! A half-bounded interval opened to the past only has an infinite start bound
//! and a finite end bound.
//!
//! Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
//! cannot change.
//!
//! If you are looking for a half-bounded absolute interval that doesn't keep the
//! [opening direction](OpeningDirection) invariant, see [`HalfBoundedAbsInterval`].

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
    HasIntervalTypeWithRel,
    HasOpeningDirection,
    HasOpenness,
    HasRelativity,
    Interval,
    IntervalTypeWithRel,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};

/// Absolute half-bounded interval opened to the past
///
/// A half-bounded interval opened to the past only has an infinite start bound
/// and a finite end bound.
///
/// Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
/// cannot change.
///
/// If you are looking for a half-bounded absolute interval that doesn't keep the
/// [opening direction](OpeningDirection) invariant, see [`HalfBoundedAbsInterval`].
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastAbsInterval(pub(crate) AbsFiniteEndBound);

impl HalfBoundedToPastAbsInterval {
    /// Creates a new half-bounded interval opened to the past
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsFiniteBoundPos,
    /// #     HalfBoundedToPastAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToPastAbsInterval::new(AbsFiniteBoundPos::new(time).to_finite_end_bound());
    ///
    /// assert_eq!(half_bounded.end_time(), time);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new(end: AbsFiniteEndBound) -> Self {
        HalfBoundedToPastAbsInterval(end)
    }

    /// Creates a new half-bounded interval opened to the past from a time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToPastAbsInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedToPastAbsInterval::from_time(time);
    ///
    /// assert_eq!(half_bounded.end_time(), time);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_time(reference: Timestamp) -> Self {
        Self::new(AbsFiniteBoundPos::new(reference).to_finite_end_bound())
    }

    /// Creates a new half-bounded interval opened to the past from a time
    /// and a bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToPastAbsInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToPastAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.end_time(), time);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_time_incl(reference: Timestamp, reference_inclusivity: BoundInclusivity) -> Self {
        HalfBoundedToPastAbsInterval::new(
            AbsFiniteBoundPos::new_with_incl(reference, reference_inclusivity).to_finite_end_bound(),
        )
    }

    /// Attempts to create a [`HalfBoundedAbsInterval`] from a [`Timestamp`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedToPastAbsIntervalTryFromRangeError`] if the range's end bound
    /// is not [`Unbounded`](Bound::Unbounded).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToPastAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedToPastAbsInterval::try_from_range(..time)?;
    ///
    /// assert_eq!(half_bounded.end_time(), time);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToPastAbsIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Unbounded, Bound::Included(&reference)) => {
                Ok(Self::from_time_incl(reference, BoundInclusivity::Inclusive))
            },
            (Bound::Unbounded, Bound::Excluded(&reference)) => {
                Ok(Self::from_time_incl(reference, BoundInclusivity::Exclusive))
            },
            _ => Err(HalfBoundedToPastAbsIntervalTryFromRangeError),
        }
    }

    /// Returns the infinite start bound
    #[must_use]
    pub fn start(&self) -> AbsStartBound {
        AbsStartBound::InfinitePast
    }

    /// Returns the finite end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     HalfBoundedToPastAbsInterval,
    /// #     AbsFiniteBoundPos,
    /// # };
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToPastAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.end(),
    ///     AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_finite_end_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(&self) -> AbsFiniteEndBound {
        self.0
    }

    /// Returns the end time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToPastAbsInterval;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedToPastAbsInterval::from_time(time);
    ///
    /// assert_eq!(half_bounded.end_time(), time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end_time(&self) -> Timestamp {
        self.end().pos().time()
    }

    /// Returns the end bound's inclusivity
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToPastAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded =
    ///     HalfBoundedToPastAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end_inclusivity(&self) -> BoundInclusivity {
        self.end().pos().inclusivity()
    }

    /// Returns a mutable pointer to the finite end bound
    ///
    /// This is used for mutating which position the end bound represents.
    pub fn end_mut(&mut self) -> &mut AbsFiniteEndBound {
        &mut self.0
    }

    /// Sets the finite end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsFiniteBoundPos,
    /// #     HalfBoundedToPastAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let new_end = AbsFiniteBoundPos::new_with_incl(
    ///     "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_finite_end_bound();
    /// let mut half_bounded =
    ///     HalfBoundedToPastAbsInterval::from_time("2020-01-01 00:00:00Z".parse::<Timestamp>()?);
    ///
    /// half_bounded.set_end(new_end);
    ///
    /// assert_eq!(half_bounded.end(), new_end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end(&mut self, new_end: AbsFiniteEndBound) {
        self.0 = new_end;
    }

    /// Sets the end time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToPastAbsInterval;
    /// let mut half_bounded =
    ///     HalfBoundedToPastAbsInterval::from_time("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
    ///
    /// let new_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// half_bounded.set_end_time(new_time);
    ///
    /// assert_eq!(half_bounded.end_time(), new_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end_time(&mut self, new_end_time: Timestamp) {
        self.end_mut().pos_mut().set_time(new_end_time);
    }

    /// Sets the end bound's inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedToPastAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut half_bounded =
    ///     HalfBoundedToPastAbsInterval::from_time("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
    ///
    /// half_bounded.set_end_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.end_mut().pos_mut().set_inclusivity(new_inclusivity);
    }

    /// Returns the opposite half-bounded interval opened to the future
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
    /// let half_bounded = HalfBoundedToPastAbsInterval::from_time(time);
    ///
    /// assert_eq!(
    ///     half_bounded.opposite(),
    ///     HalfBoundedToFutureAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(self) -> HalfBoundedToFutureAbsInterval {
        HalfBoundedToFutureAbsInterval(self.end().opposite())
    }

    /// Wraps `self` in [`HalfBoundedAbsInterval`]
    #[must_use]
    pub fn to_half_bounded_interval(self) -> HalfBoundedAbsInterval {
        HalfBoundedAbsInterval::ToPast(self)
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
        Relativity::Absolute
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

impl HasIntervalTypeWithRel for HalfBoundedToPastAbsInterval {
    fn interval_type_with_rel(&self) -> IntervalTypeWithRel {
        IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)
    }
}

impl From<Timestamp> for HalfBoundedToPastAbsInterval {
    fn from(time: Timestamp) -> Self {
        HalfBoundedToPastAbsInterval::from_time(time)
    }
}

impl From<(Timestamp, BoundInclusivity)> for HalfBoundedToPastAbsInterval {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        HalfBoundedToPastAbsInterval::from_time_incl(time, inclusivity)
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
        HalfBoundedToPastAbsInterval::from_time_incl(range.end, BoundInclusivity::Exclusive)
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedToPastAbsInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedToPastAbsInterval::from_time_incl(range.end, BoundInclusivity::Inclusive)
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

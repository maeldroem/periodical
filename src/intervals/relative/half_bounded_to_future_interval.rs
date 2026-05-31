use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeFrom};

use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

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
use crate::intervals::relative::{
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HalfBoundedToPastRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteStartBound,
    RelativeInterval,
    RelativeStartBound,
};

/// A half-bounded relative interval
///
/// A half-bounded interval has a reference offset and an opening direction.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a half-bounded interval must remain a
/// half-bounded interval. It cannot mutate from being a half-bounded interval
/// to a bounded interval.
///
/// Instead, if you are looking for an relative interval that doesn't keep the
/// [openness](Openness) invariant, see [`RelativeBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct HalfBoundedToFutureRelativeInterval(pub(crate) RelativeFiniteStartBound);

impl HalfBoundedToFutureRelativeInterval {
    pub fn new(start: RelativeFiniteStartBound) -> Self {
        HalfBoundedToFutureRelativeInterval(start)
    }

    /// Creates a new [`HalfBoundedRelativeInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(ref_offset, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_offset);
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
    pub fn new_from_offset(reference: SignedDuration) -> Self {
        Self::new(RelativeFiniteBoundPosition::new(reference).to_finite_start_bound())
    }

    /// Creates a new [`HalfBoundedRelativeInterval`] with the given bound
    /// inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     ref_offset,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_offset);
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
    pub fn new_from_offset_and_inclusivity(reference: SignedDuration, reference_inclusivity: BoundInclusivity) -> Self {
        HalfBoundedToFutureRelativeInterval::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(reference, reference_inclusivity).to_finite_start_bound(),
        )
    }

    /// Attempts to create a [`HalfBoundedRelativeInterval`] from a [`SignedDuration`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedRelativeIntervalTryFromRangeError`] if there is not exactly
    /// one [unbounded](Bound::Unbounded) range bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{HalfBoundedRelativeInterval, HalfBoundedRelativeIntervalTryFromRangeError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let reference = "2026-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let interval = HalfBoundedRelativeInterval::try_from_range(..reference)?;
    ///
    /// assert_eq!(interval.reference(), reference);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToFutureRelativeIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(&reference), Bound::Unbounded) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
            )),
            (Bound::Excluded(&reference), Bound::Unbounded) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
            )),
            _ => Err(HalfBoundedToFutureRelativeIntervalTryFromRangeError),
        }
    }

    pub fn start(&self) -> RelativeFiniteStartBound {
        self.0
    }

    pub fn start_mut(&mut self) -> &mut RelativeFiniteStartBound {
        &mut self.0
    }

    pub fn end(&self) -> RelativeEndBound {
        RelativeEndBound::InfiniteFuture
    }

    /// Returns the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(ref_offset, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_offset);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start_offset(&self) -> SignedDuration {
        self.start().pos().offset()
    }

    /// Returns the inclusivity of the reference offset
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     ref_offset,
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

    pub fn set_start(&mut self, new_start: RelativeFiniteStartBound) {
        self.0 = new_start;
    }

    /// Sets the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(ref_offset, OpeningDirection::ToFuture);
    ///
    /// let new_ref_offset = "2025-01-01 16:00:00Z".parse::<SignedDuration>()?;
    ///
    /// half_bounded_interval.set_reference(new_ref_offset);
    ///
    /// assert_eq!(half_bounded_interval.reference(), new_ref_offset);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start_offset(&mut self, new_start_offset: SignedDuration) {
        self.start_mut().pos_mut().set_offset(new_start_offset);
    }

    /// Sets the inclusivity of the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(ref_offset, OpeningDirection::ToFuture);
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

    pub fn opposite(self) -> HalfBoundedToPastRelativeInterval {
        HalfBoundedToPastRelativeInterval::new(self.start().opposite())
    }

    pub fn to_half_bounded_interval(self) -> HalfBoundedRelativeInterval {
        HalfBoundedRelativeInterval::ToFuture(self)
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedToFutureRelativeIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeStart,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToFutureRelativeIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStart => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToFutureRelativeIntervalCreationError {}

/// Error that can occur when trying to convert a [`SignedDuration`] range into a [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelativeIntervalTryFromRangeError;

impl Display for HalfBoundedToFutureRelativeIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `SignedDuration` range into a `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelativeIntervalTryFromRangeError {}

impl Interval for HalfBoundedToFutureRelativeInterval {}

impl HasOpenness for HalfBoundedToFutureRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToFutureRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for HalfBoundedToFutureRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToFutureRelativeInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToFuture
    }
}

impl HasRelativeBoundPair for HalfBoundedToFutureRelativeInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        RelativeBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        self.start().to_start_bound()
    }

    fn rel_end(&self) -> RelativeEndBound {
        self.end()
    }
}

impl IsEmpty for HalfBoundedToFutureRelativeInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<SignedDuration> for HalfBoundedToFutureRelativeInterval {
    fn from(offset: SignedDuration) -> Self {
        HalfBoundedToFutureRelativeInterval::new_from_offset(offset)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for HalfBoundedToFutureRelativeInterval {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        HalfBoundedToFutureRelativeInterval::new_from_offset_and_inclusivity(offset, inclusivity)
    }
}

impl From<RelativeFiniteBoundPosition> for HalfBoundedToFutureRelativeInterval {
    fn from(start: RelativeFiniteBoundPosition) -> Self {
        Self::new(start.to_finite_start_bound())
    }
}

impl From<RelativeFiniteStartBound> for HalfBoundedToFutureRelativeInterval {
    fn from(start: RelativeFiniteStartBound) -> Self {
        Self::new(start)
    }
}

impl From<RangeFrom<SignedDuration>> for HalfBoundedToFutureRelativeInterval {
    fn from(range: RangeFrom<SignedDuration>) -> Self {
        HalfBoundedToFutureRelativeInterval::new_from_offset_and_inclusivity(range.start, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`RelativeBoundPair`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelativeIntervalTryFromRelativeBoundPairError;

impl Display for HalfBoundedToFutureRelativeIntervalTryFromRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeBoundPair` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelativeIntervalTryFromRelativeBoundPairError {}

impl TryFrom<RelativeBoundPair> for HalfBoundedToFutureRelativeInterval {
    type Error = HalfBoundedToFutureRelativeIntervalTryFromRelativeBoundPairError;

    fn try_from(value: RelativeBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::InfiniteFuture) => Ok(Self::new(finite_start)),
            _ => Err(HalfBoundedToFutureRelativeIntervalTryFromRelativeBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelativeInterval`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelativeIntervalTryFromRelativeIntervalError;

impl Display for HalfBoundedToFutureRelativeIntervalTryFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeInterval` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelativeIntervalTryFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for HalfBoundedToFutureRelativeInterval {
    type Error = HalfBoundedToFutureRelativeIntervalTryFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToFutureRelativeIntervalTryFromRelativeIntervalError)?
            .half_bounded_to_future()
            .ok_or(HalfBoundedToFutureRelativeIntervalTryFromRelativeIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeInterval`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelativeIntervalTryFromEmptiableRelativeIntervalError;

impl Display for HalfBoundedToFutureRelativeIntervalTryFromEmptiableRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeInterval` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelativeIntervalTryFromEmptiableRelativeIntervalError {}

impl TryFrom<EmptiableRelativeInterval> for HalfBoundedToFutureRelativeInterval {
    type Error = HalfBoundedToFutureRelativeIntervalTryFromEmptiableRelativeIntervalError;

    fn try_from(value: EmptiableRelativeInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToFutureRelativeIntervalTryFromEmptiableRelativeIntervalError)?,
        )
        .or(Err(
            HalfBoundedToFutureRelativeIntervalTryFromEmptiableRelativeIntervalError,
        ))
    }
}

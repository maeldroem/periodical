use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeTo, RangeToInclusive};

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
    HalfBoundedToFutureRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteEndBound,
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
pub struct HalfBoundedToPastRelativeInterval(pub(crate) RelativeFiniteEndBound);

impl HalfBoundedToPastRelativeInterval {
    pub fn new(end: RelativeFiniteEndBound) -> Self {
        HalfBoundedToPastRelativeInterval(end)
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
        Self::new(RelativeFiniteBoundPosition::new(reference).to_finite_end_bound())
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
        HalfBoundedToPastRelativeInterval::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(reference, reference_inclusivity).to_finite_end_bound(),
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
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToPastRelativeIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Unbounded, Bound::Included(&reference)) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
            )),
            (Bound::Unbounded, Bound::Excluded(&reference)) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
            )),
            _ => Err(HalfBoundedToPastRelativeIntervalTryFromRangeError),
        }
    }

    pub fn start(&self) -> RelativeStartBound {
        RelativeStartBound::InfinitePast
    }

    pub fn end(&self) -> RelativeFiniteEndBound {
        self.0
    }

    pub fn end_mut(&mut self) -> &mut RelativeFiniteEndBound {
        &mut self.0
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
    pub fn end_offset(&self) -> SignedDuration {
        self.end().pos().offset()
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
    pub fn end_inclusivity(&self) -> BoundInclusivity {
        self.end().pos().inclusivity()
    }

    pub fn set_end(&mut self, new_end: RelativeFiniteEndBound) {
        self.0 = new_end;
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
    pub fn set_end_offset(&mut self, new_end_offset: SignedDuration) {
        self.end_mut().pos_mut().set_offset(new_end_offset);
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
    pub fn set_reference_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.end_mut().pos_mut().set_inclusivity(new_inclusivity);
    }

    pub fn opposite(self) -> HalfBoundedToFutureRelativeInterval {
        HalfBoundedToFutureRelativeInterval(self.end().opposite())
    }

    pub fn to_half_bounded_interval(self) -> HalfBoundedRelativeInterval {
        HalfBoundedRelativeInterval::ToPast(self)
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
pub enum HalfBoundedToPastRelativeIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeEnd,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToPastRelativeIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeEnd => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToPastRelativeIntervalCreationError {}

/// Error that can occur when trying to convert a [`SignedDuration`] range into a [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelativeIntervalTryFromRangeError;

impl Display for HalfBoundedToPastRelativeIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `SignedDuration` range into a `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelativeIntervalTryFromRangeError {}

impl Interval for HalfBoundedToPastRelativeInterval {}

impl HasOpenness for HalfBoundedToPastRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToPastRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for HalfBoundedToPastRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToPastRelativeInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToPast
    }
}

impl HasRelativeBoundPair for HalfBoundedToPastRelativeInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        RelativeBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        self.start()
    }

    fn rel_end(&self) -> RelativeEndBound {
        self.end().to_end_bound()
    }
}

impl IsEmpty for HalfBoundedToPastRelativeInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<SignedDuration> for HalfBoundedToPastRelativeInterval {
    fn from(offset: SignedDuration) -> Self {
        HalfBoundedToPastRelativeInterval::new_from_offset(offset)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for HalfBoundedToPastRelativeInterval {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        HalfBoundedToPastRelativeInterval::new_from_offset_and_inclusivity(offset, inclusivity)
    }
}

impl From<RelativeFiniteBoundPosition> for HalfBoundedToPastRelativeInterval {
    fn from(end: RelativeFiniteBoundPosition) -> Self {
        Self::new(end.to_finite_end_bound())
    }
}

impl From<RelativeFiniteEndBound> for HalfBoundedToPastRelativeInterval {
    fn from(end: RelativeFiniteEndBound) -> Self {
        Self::new(end)
    }
}

impl From<RangeTo<SignedDuration>> for HalfBoundedToPastRelativeInterval {
    fn from(range: RangeTo<SignedDuration>) -> Self {
        HalfBoundedToPastRelativeInterval::new_from_offset_and_inclusivity(range.end, BoundInclusivity::Exclusive)
    }
}

impl From<RangeToInclusive<SignedDuration>> for HalfBoundedToPastRelativeInterval {
    fn from(range: RangeToInclusive<SignedDuration>) -> Self {
        HalfBoundedToPastRelativeInterval::new_from_offset_and_inclusivity(range.end, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`RelativeBoundPair`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelativeIntervalTryFromRelativeBoundPairError;

impl Display for HalfBoundedToPastRelativeIntervalTryFromRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeBoundPair` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelativeIntervalTryFromRelativeBoundPairError {}

impl TryFrom<RelativeBoundPair> for HalfBoundedToPastRelativeInterval {
    type Error = HalfBoundedToPastRelativeIntervalTryFromRelativeBoundPairError;

    fn try_from(value: RelativeBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(finite_end)) => Ok(Self::new(finite_end)),
            _ => Err(HalfBoundedToPastRelativeIntervalTryFromRelativeBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelativeInterval`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelativeIntervalTryFromRelativeIntervalError;

impl Display for HalfBoundedToPastRelativeIntervalTryFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeInterval` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelativeIntervalTryFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for HalfBoundedToPastRelativeInterval {
    type Error = HalfBoundedToPastRelativeIntervalTryFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToPastRelativeIntervalTryFromRelativeIntervalError)?
            .half_bounded_to_past()
            .ok_or(HalfBoundedToPastRelativeIntervalTryFromRelativeIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeInterval`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelativeIntervalTryFromEmptiableRelativeIntervalError;

impl Display for HalfBoundedToPastRelativeIntervalTryFromEmptiableRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeInterval` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelativeIntervalTryFromEmptiableRelativeIntervalError {}

impl TryFrom<EmptiableRelativeInterval> for HalfBoundedToPastRelativeInterval {
    type Error = HalfBoundedToPastRelativeIntervalTryFromEmptiableRelativeIntervalError;

    fn try_from(value: EmptiableRelativeInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToPastRelativeIntervalTryFromEmptiableRelativeIntervalError)?,
        )
        .or(Err(
            HalfBoundedToPastRelativeIntervalTryFromEmptiableRelativeIntervalError,
        ))
    }
}

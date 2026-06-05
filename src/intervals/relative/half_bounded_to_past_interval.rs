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
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HalfBoundedToFutureRelInterval,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelInterval,
    RelStartBound,
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
/// [openness](Openness) invariant, see [`RelBoundPair`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct HalfBoundedToPastRelInterval(pub(crate) RelFiniteEndBound);

impl HalfBoundedToPastRelInterval {
    pub fn new(end: RelFiniteEndBound) -> Self {
        HalfBoundedToPastRelInterval(end)
    }

    /// Creates a new [`HalfBoundedRelInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval = HalfBoundedRelInterval::new(ref_offset, OpeningDirection::ToPast);
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
    pub fn from_offset(reference: SignedDuration) -> Self {
        Self::new(RelFiniteBoundPos::new(reference).to_finite_end_bound())
    }

    /// Creates a new [`HalfBoundedRelInterval`] with the given bound
    /// inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval = HalfBoundedRelInterval::new_with_incl(
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
    pub fn from_offset_incl(reference: SignedDuration, reference_inclusivity: BoundInclusivity) -> Self {
        HalfBoundedToPastRelInterval::new(
            RelFiniteBoundPos::new_with_incl(reference, reference_inclusivity).to_finite_end_bound(),
        )
    }

    /// Attempts to create a [`HalfBoundedRelInterval`] from a [`SignedDuration`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedRelIntervalTryFromRangeError`] if there is not exactly
    /// one [unbounded](Bound::Unbounded) range bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{HalfBoundedRelInterval, HalfBoundedRelIntervalTryFromRangeError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let reference = "2026-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let interval = HalfBoundedRelInterval::try_from_range(..reference)?;
    ///
    /// assert_eq!(interval.reference(), reference);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToPastRelIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Unbounded, Bound::Included(&reference)) => {
                Ok(Self::from_offset_incl(reference, BoundInclusivity::Inclusive))
            },
            (Bound::Unbounded, Bound::Excluded(&reference)) => {
                Ok(Self::from_offset_incl(reference, BoundInclusivity::Exclusive))
            },
            _ => Err(HalfBoundedToPastRelIntervalTryFromRangeError),
        }
    }

    pub fn start(&self) -> RelStartBound {
        RelStartBound::InfinitePast
    }

    pub fn end(&self) -> RelFiniteEndBound {
        self.0
    }

    pub fn end_mut(&mut self) -> &mut RelFiniteEndBound {
        &mut self.0
    }

    /// Returns the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval = HalfBoundedRelInterval::new(ref_offset, OpeningDirection::ToPast);
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
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let half_bounded_interval = HalfBoundedRelInterval::new_with_incl(
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

    pub fn set_end(&mut self, new_end: RelFiniteEndBound) {
        self.0 = new_end;
    }

    /// Sets the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedRelInterval::new(ref_offset, OpeningDirection::ToFuture);
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
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedRelInterval::new(ref_offset, OpeningDirection::ToFuture);
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

    pub fn opposite(self) -> HalfBoundedToFutureRelInterval {
        HalfBoundedToFutureRelInterval(self.end().opposite())
    }

    pub fn to_half_bounded_interval(self) -> HalfBoundedRelInterval {
        HalfBoundedRelInterval::ToPast(self)
    }

    /// Wraps the interval in [`RelInterval`]
    #[must_use]
    pub fn to_interval(self) -> RelInterval {
        RelInterval::from(self)
    }

    /// Wraps the interval in [`EmptiableRelInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableRelInterval {
        EmptiableRelInterval::from(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedToPastRelIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeEnd,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToPastRelIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeEnd => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToPastRelIntervalCreationError {}

/// Error that can occur when trying to convert a [`SignedDuration`] range into a [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelIntervalTryFromRangeError;

impl Display for HalfBoundedToPastRelIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `SignedDuration` range into a `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelIntervalTryFromRangeError {}

impl Interval for HalfBoundedToPastRelInterval {}

impl HasOpenness for HalfBoundedToPastRelInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToPastRelInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Rel
    }
}

impl HasDuration for HalfBoundedToPastRelInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToPastRelInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToPast
    }
}

impl HasRelBoundPair for HalfBoundedToPastRelInterval {
    fn rel_bound_pair(&self) -> RelBoundPair {
        RelBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelStartBound {
        self.start()
    }

    fn rel_end(&self) -> RelEndBound {
        self.end().to_end_bound()
    }
}

impl IsEmpty for HalfBoundedToPastRelInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<SignedDuration> for HalfBoundedToPastRelInterval {
    fn from(offset: SignedDuration) -> Self {
        HalfBoundedToPastRelInterval::from_offset(offset)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for HalfBoundedToPastRelInterval {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        HalfBoundedToPastRelInterval::from_offset_incl(offset, inclusivity)
    }
}

impl From<RelFiniteBoundPos> for HalfBoundedToPastRelInterval {
    fn from(end: RelFiniteBoundPos) -> Self {
        Self::new(end.to_finite_end_bound())
    }
}

impl From<RelFiniteEndBound> for HalfBoundedToPastRelInterval {
    fn from(end: RelFiniteEndBound) -> Self {
        Self::new(end)
    }
}

impl From<RangeTo<SignedDuration>> for HalfBoundedToPastRelInterval {
    fn from(range: RangeTo<SignedDuration>) -> Self {
        HalfBoundedToPastRelInterval::from_offset_incl(range.end, BoundInclusivity::Exclusive)
    }
}

impl From<RangeToInclusive<SignedDuration>> for HalfBoundedToPastRelInterval {
    fn from(range: RangeToInclusive<SignedDuration>) -> Self {
        HalfBoundedToPastRelInterval::from_offset_incl(range.end, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`RelBoundPair`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelIntervalTryFromRelBoundPairError;

impl Display for HalfBoundedToPastRelIntervalTryFromRelBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelBoundPair` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelIntervalTryFromRelBoundPairError {}

impl TryFrom<RelBoundPair> for HalfBoundedToPastRelInterval {
    type Error = HalfBoundedToPastRelIntervalTryFromRelBoundPairError;

    fn try_from(value: RelBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelStartBound::InfinitePast, RelEndBound::Finite(finite_end)) => Ok(Self::new(finite_end)),
            _ => Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelInterval`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelIntervalTryFromRelIntervalError;

impl Display for HalfBoundedToPastRelIntervalTryFromRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelInterval` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelIntervalTryFromRelIntervalError {}

impl TryFrom<RelInterval> for HalfBoundedToPastRelInterval {
    type Error = HalfBoundedToPastRelIntervalTryFromRelIntervalError;

    fn try_from(value: RelInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToPastRelIntervalTryFromRelIntervalError)?
            .half_bounded_to_past()
            .ok_or(HalfBoundedToPastRelIntervalTryFromRelIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelInterval`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError;

impl Display for HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelInterval` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError {}

impl TryFrom<EmptiableRelInterval> for HalfBoundedToPastRelInterval {
    type Error = HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError;

    fn try_from(value: EmptiableRelInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError)?,
        )
        .or(Err(HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError))
    }
}

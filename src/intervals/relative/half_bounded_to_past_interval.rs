//! Relative half-bounded interval opened to the past
//!
//! A half-bounded interval opened to the past only has an infinite start bound
//! and a finite end bound.
//!
//! Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
//! cannot change.
//!
//! If you are looking for a half-bounded absolute interval that doesn't keep the
//! [opening direction](OpeningDirection) invariant, see [`HalfBoundedRelInterval`].

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

/// Relative half-bounded interval opened to the past
///
/// A half-bounded interval opened to the past only has an infinite start bound
/// and a finite end bound.
///
/// Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
/// cannot change.
///
/// If you are looking for a half-bounded absolute interval that doesn't keep the
/// [opening direction](OpeningDirection) invariant, see [`HalfBoundedRelInterval`].
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HalfBoundedToPastRelInterval(pub(crate) RelFiniteEndBound);

impl HalfBoundedToPastRelInterval {
    /// Creates a new half-bounded interval opened to the past
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelFiniteBoundPos,
    /// #     HalfBoundedToPastRelInterval,
    /// # };
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToPastRelInterval::new(RelFiniteBoundPos::new(offset).to_finite_end_bound());
    ///
    /// assert_eq!(half_bounded.end_offset(), offset);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// ```
    #[must_use]
    pub fn new(end: RelFiniteEndBound) -> Self {
        HalfBoundedToPastRelInterval(end)
    }

    /// Creates a new half-bounded interval opened to the future from an offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToPastRelInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToPastRelInterval::from_offset(offset);
    ///
    /// assert_eq!(half_bounded.end_offset(), offset);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// ```
    #[must_use]
    pub fn from_offset(reference: SignedDuration) -> Self {
        Self::new(RelFiniteBoundPos::new(reference).to_finite_end_bound())
    }

    /// Creates a new half-bounded interval opened to the past from an offset
    /// and a bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToPastRelInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToPastRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.end_offset(), offset);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
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
    /// Returns [`HalfBoundedToPastRelIntervalTryFromRangeError`] if the range's end bound
    /// is not [`Unbounded`](Bound::Unbounded).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToPastRelInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToPastRelInterval::try_from_range(..offset)?;
    ///
    /// assert_eq!(half_bounded.end_offset(), offset);
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
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

    /// Returns the infinite start bound
    #[must_use]
    pub fn start(&self) -> RelStartBound {
        RelStartBound::InfinitePast
    }

    /// Returns the finite start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     HalfBoundedToPastRelInterval,
    /// #     RelFiniteBoundPos,
    /// # };
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToPastRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.end(),
    ///     RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive).to_finite_end_bound()
    /// );
    /// ```
    #[must_use]
    pub fn end(&self) -> RelFiniteEndBound {
        self.0
    }

    /// Returns the end offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToPastRelInterval;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToPastRelInterval::from_offset(offset);
    ///
    /// assert_eq!(half_bounded.end_offset(), offset);
    /// ```
    #[must_use]
    pub fn end_offset(&self) -> SignedDuration {
        self.end().pos().offset()
    }

    /// Returns the end bound's inclusivity
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToPastRelInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToPastRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
    /// ```
    #[must_use]
    pub fn end_inclusivity(&self) -> BoundInclusivity {
        self.end().pos().inclusivity()
    }

    /// Returns a mutable pointer to the finite end bound
    ///
    /// This is used for mutating which position the end bound represents.
    pub fn end_mut(&mut self) -> &mut RelFiniteEndBound {
        &mut self.0
    }

    /// Sets the finite end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelFiniteBoundPos,
    /// #     HalfBoundedToPastRelInterval,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let new_end = RelFiniteBoundPos::new_with_incl(
    ///     SignedDuration::from_hours(10),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_finite_end_bound();
    /// let mut half_bounded = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(2));
    ///
    /// half_bounded.set_end(new_end);
    ///
    /// assert_eq!(half_bounded.end(), new_end);
    /// ```
    pub fn set_end(&mut self, new_end: RelFiniteEndBound) {
        self.0 = new_end;
    }

    /// Sets the end offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToPastRelInterval;
    /// let mut half_bounded = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(2));
    ///
    /// let new_offset = SignedDuration::from_hours(10);
    ///
    /// half_bounded.set_end_offset(new_offset);
    ///
    /// assert_eq!(half_bounded.end_offset(), new_offset);
    /// ```
    pub fn set_end_offset(&mut self, new_end_offset: SignedDuration) {
        self.end_mut().pos_mut().set_offset(new_end_offset);
    }

    /// Sets the end bound's inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToPastRelInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut half_bounded =
    ///     HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(10));
    ///
    /// half_bounded.set_end_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.end_inclusivity(), BoundInclusivity::Exclusive);
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
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     HalfBoundedToFutureRelInterval,
    /// #     HalfBoundedToPastRelInterval,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToPastRelInterval::from_offset(offset);
    ///
    /// assert_eq!(
    ///     half_bounded.opposite(),
    ///     HalfBoundedToFutureRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive),
    /// );
    /// ```
    #[must_use]
    pub fn opposite(self) -> HalfBoundedToFutureRelInterval {
        HalfBoundedToFutureRelInterval(self.end().opposite())
    }

    /// Wraps `self` in [`HalfBoundedRelInterval`]
    #[must_use]
    pub fn to_half_bounded_interval(self) -> HalfBoundedRelInterval {
        HalfBoundedRelInterval::ToPast(self)
    }

    /// Converts `self` into [`RelInterval`]
    #[must_use]
    pub fn to_interval(self) -> RelInterval {
        RelInterval::from(self)
    }

    /// Converts `self` into [`EmptiableRelInterval`]
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

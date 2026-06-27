//! Relative half-bounded interval opened to the future
//!
//! A half-bounded interval opened to the future only has finite start bound
//! and an infinite end bound.
//!
//! Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
//! cannot change.
//!
//! If you are looking for a half-bounded absolute interval that doesn't keep the
//! [opening direction](OpeningDirection) invariant, see [`HalfBoundedRelInterval`].

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
use crate::intervals::relative::{
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HalfBoundedToPastRelInterval,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelFiniteStartBound,
    RelInterval,
    RelStartBound,
};

/// Relative half-bounded interval opened to the future
///
/// A half-bounded interval opened to the future only has finite start bound
/// and an infinite end bound.
///
/// Its invariants are that its [openness](Openness) and its [opening direction](OpeningDirection)
/// cannot change.
///
/// If you are looking for a half-bounded absolute interval that doesn't keep the
/// [opening direction](OpeningDirection) invariant, see [`HalfBoundedRelInterval`].
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelInterval(pub(crate) RelFiniteStartBound);

impl HalfBoundedToFutureRelInterval {
    /// Creates a new half-bounded interval opened to the future
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelFiniteBoundPos,
    /// #     HalfBoundedToFutureRelInterval,
    /// # };
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToFutureRelInterval::new(RelFiniteBoundPos::new(offset).to_finite_start_bound());
    ///
    /// assert_eq!(half_bounded.start_offset(), offset);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToFuture);
    /// ```
    #[must_use]
    pub fn new(start: RelFiniteStartBound) -> Self {
        HalfBoundedToFutureRelInterval(start)
    }

    /// Creates a new half-bounded interval opened to the future from an offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToFutureRelInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToFutureRelInterval::from_offset(offset);
    ///
    /// assert_eq!(half_bounded.start_offset(), offset);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToFuture);
    /// ```
    #[must_use]
    pub fn from_offset(start: SignedDuration) -> Self {
        Self::new(RelFiniteBoundPos::new(start).to_finite_start_bound())
    }

    /// Creates a new half-bounded interval opened to the future from an offset
    /// and a bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToFutureRelInterval;
    /// # use periodical::intervals::meta::{
    /// #     BoundInclusivity,
    /// #     OpeningDirection,
    /// #     HasOpeningDirection,
    /// # };
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToFutureRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded.start_offset(), offset);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToFuture);
    /// ```
    #[must_use]
    pub fn from_offset_incl(reference: SignedDuration, reference_inclusivity: BoundInclusivity) -> Self {
        HalfBoundedToFutureRelInterval::new(
            RelFiniteBoundPos::new_with_incl(reference, reference_inclusivity).to_finite_start_bound(),
        )
    }

    /// Attempts to create a [`HalfBoundedRelInterval`] from a [`SignedDuration`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedToFutureRelIntervalTryFromRangeError`] if the range's end bound
    /// is not [`Unbounded`](Bound::Unbounded).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToFutureRelInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToFutureRelInterval::try_from_range(offset..)?;
    ///
    /// assert_eq!(half_bounded.start_offset(), offset);
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedToFutureRelIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(&reference), Bound::Unbounded) => {
                Ok(Self::from_offset_incl(reference, BoundInclusivity::Inclusive))
            },
            (Bound::Excluded(&reference), Bound::Unbounded) => {
                Ok(Self::from_offset_incl(reference, BoundInclusivity::Exclusive))
            },
            _ => Err(HalfBoundedToFutureRelIntervalTryFromRangeError),
        }
    }

    /// Returns the finite start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     HalfBoundedToFutureRelInterval,
    /// #     RelFiniteBoundPos,
    /// # };
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToFutureRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.start(),
    ///     RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive)
    ///         .to_finite_start_bound()
    /// );
    /// ```
    #[must_use]
    pub fn start(&self) -> RelFiniteStartBound {
        self.0
    }

    /// Returns the infinite end bound
    #[must_use]
    pub fn end(&self) -> RelEndBound {
        RelEndBound::InfiniteFuture
    }

    /// Returns the start offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToFutureRelInterval;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToFutureRelInterval::from_offset(offset);
    ///
    /// assert_eq!(half_bounded.start_offset(), offset);
    /// ```
    #[must_use]
    pub fn start_offset(&self) -> SignedDuration {
        self.start().pos().offset()
    }

    /// Returns the start bound's inclusivity
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToFutureRelInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded =
    ///     HalfBoundedToFutureRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    #[must_use]
    pub fn start_inclusivity(&self) -> BoundInclusivity {
        self.start().pos().inclusivity()
    }

    /// Returns a mutable pointer to the finite start bound
    ///
    /// This is used for mutating which position the start bound represents.
    #[must_use]
    pub fn start_mut(&mut self) -> &mut RelFiniteStartBound {
        &mut self.0
    }

    /// Sets the finite start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelFiniteBoundPos,
    /// #     HalfBoundedToFutureRelInterval,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let new_start = RelFiniteBoundPos::new_with_incl(
    ///     SignedDuration::from_hours(10),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_finite_start_bound();
    /// let mut half_bounded =
    ///     HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(2));
    ///
    /// half_bounded.set_start(new_start);
    ///
    /// assert_eq!(half_bounded.start(), new_start);
    /// ```
    pub fn set_start(&mut self, new_start: RelFiniteStartBound) {
        self.0 = new_start;
    }

    /// Sets the start offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToFutureRelInterval;
    /// let mut half_bounded =
    ///     HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(2));
    ///
    /// let new_offset = SignedDuration::from_hours(10);
    ///
    /// half_bounded.set_start_offset(new_offset);
    ///
    /// assert_eq!(half_bounded.start_offset(), new_offset);
    /// ```
    pub fn set_start_offset(&mut self, new_start_offset: SignedDuration) {
        self.start_mut().pos_mut().set_offset(new_start_offset);
    }

    /// Sets the start bound's inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedToFutureRelInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let mut half_bounded =
    ///     HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(10));
    ///
    /// half_bounded.set_start_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.start_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
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
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     HalfBoundedToFutureRelInterval,
    /// #     HalfBoundedToPastRelInterval,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedToFutureRelInterval::from_offset(offset);
    ///
    /// assert_eq!(
    ///     half_bounded.opposite(),
    ///     HalfBoundedToPastRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive),
    /// );
    /// ```
    #[must_use]
    pub fn opposite(self) -> HalfBoundedToPastRelInterval {
        HalfBoundedToPastRelInterval::new(self.start().opposite())
    }

    /// Wraps `self` in [`HalfBoundedRelInterval`]
    #[must_use]
    pub fn to_half_bounded_interval(self) -> HalfBoundedRelInterval {
        HalfBoundedRelInterval::ToFuture(self)
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
pub enum HalfBoundedToFutureRelIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeStart,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedToFutureRelIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStart => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedToFutureRelIntervalCreationError {}

/// Error that can occur when trying to convert a [`SignedDuration`] range into a [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelIntervalTryFromRangeError;

impl Display for HalfBoundedToFutureRelIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `SignedDuration` range into a `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelIntervalTryFromRangeError {}

impl Interval for HalfBoundedToFutureRelInterval {}

impl HasOpenness for HalfBoundedToFutureRelInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedToFutureRelInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for HalfBoundedToFutureRelInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedToFutureRelInterval {
    fn opening_direction(&self) -> OpeningDirection {
        OpeningDirection::ToFuture
    }
}

impl HasRelBoundPair for HalfBoundedToFutureRelInterval {
    fn rel_bound_pair(&self) -> RelBoundPair {
        RelBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelStartBound {
        self.start().to_start_bound()
    }

    fn rel_end(&self) -> RelEndBound {
        self.end()
    }
}

impl IsEmpty for HalfBoundedToFutureRelInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl HasIntervalTypeWithRel for HalfBoundedToFutureRelInterval {
    fn interval_type_with_rel(&self) -> IntervalTypeWithRel {
        IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture)
    }
}

impl From<SignedDuration> for HalfBoundedToFutureRelInterval {
    fn from(offset: SignedDuration) -> Self {
        HalfBoundedToFutureRelInterval::from_offset(offset)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for HalfBoundedToFutureRelInterval {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        HalfBoundedToFutureRelInterval::from_offset_incl(offset, inclusivity)
    }
}

impl From<RelFiniteBoundPos> for HalfBoundedToFutureRelInterval {
    fn from(start: RelFiniteBoundPos) -> Self {
        Self::new(start.to_finite_start_bound())
    }
}

impl From<RelFiniteStartBound> for HalfBoundedToFutureRelInterval {
    fn from(start: RelFiniteStartBound) -> Self {
        Self::new(start)
    }
}

impl From<RangeFrom<SignedDuration>> for HalfBoundedToFutureRelInterval {
    fn from(range: RangeFrom<SignedDuration>) -> Self {
        HalfBoundedToFutureRelInterval::from_offset_incl(range.start, BoundInclusivity::Inclusive)
    }
}

/// Error that can occur when trying to convert [`RelBoundPair`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelIntervalTryFromRelBoundPairError;

impl Display for HalfBoundedToFutureRelIntervalTryFromRelBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelBoundPair` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelIntervalTryFromRelBoundPairError {}

impl TryFrom<RelBoundPair> for HalfBoundedToFutureRelInterval {
    type Error = HalfBoundedToFutureRelIntervalTryFromRelBoundPairError;

    fn try_from(value: RelBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelStartBound::Finite(finite_start), RelEndBound::InfiniteFuture) => Ok(Self::new(finite_start)),
            _ => Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelInterval`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelIntervalTryFromRelIntervalError;

impl Display for HalfBoundedToFutureRelIntervalTryFromRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelInterval` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelIntervalTryFromRelIntervalError {}

impl TryFrom<RelInterval> for HalfBoundedToFutureRelInterval {
    type Error = HalfBoundedToFutureRelIntervalTryFromRelIntervalError;

    fn try_from(value: RelInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedToFutureRelIntervalTryFromRelIntervalError)?
            .half_bounded_to_future()
            .ok_or(HalfBoundedToFutureRelIntervalTryFromRelIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelInterval`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError;

impl Display for HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelInterval` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError {}

impl TryFrom<EmptiableRelInterval> for HalfBoundedToFutureRelInterval {
    type Error = HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError;

    fn try_from(value: EmptiableRelInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError)?,
        )
        .or(Err(HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError))
    }
}

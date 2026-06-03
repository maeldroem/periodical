//! Relative half-bounded interval
//!
//! A half-bounded interval has a reference offset and an opening direction.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a half-bounded interval must remain a
//! half-bounded interval. It cannot mutate from being a half-bounded interval
//! to a bounded interval.
//!
//! Instead, if you are looking for an relative interval that doesn't keep the
//! [openness](Openness) invariant, see [`RelBoundPair`].

use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeFrom, RangeTo, RangeToInclusive};

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
    HalfBoundedToFutureRelInterval,
    HalfBoundedToPastRelInterval,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBound,
    RelFiniteBoundPos,
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
pub enum HalfBoundedRelInterval {
    ToFuture(HalfBoundedToFutureRelInterval),
    ToPast(HalfBoundedToPastRelInterval),
}

impl HalfBoundedRelInterval {
    pub fn new(reference: RelFiniteBoundPos, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => {
                Self::ToFuture(HalfBoundedToFutureRelInterval::new(reference.to_finite_start_bound()))
            },
            OpeningDirection::ToPast => {
                Self::ToPast(HalfBoundedToPastRelInterval::new(reference.to_finite_end_bound()))
            },
        }
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
    /// let half_bounded_interval =
    ///     HalfBoundedRelInterval::new(ref_offset, OpeningDirection::ToPast);
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
    pub fn new_from_offset(reference: SignedDuration, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureRelInterval::new_from_offset(reference)),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastRelInterval::new_from_offset(reference)),
        }
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
    /// let half_bounded_interval = HalfBoundedRelInterval::new_with_inclusivity(
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
    pub fn new_from_offset_and_inclusivity(
        reference: SignedDuration,
        reference_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(
                HalfBoundedToFutureRelInterval::new_from_offset_and_inclusivity(reference, reference_inclusivity),
            ),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastRelInterval::new_from_offset_and_inclusivity(
                reference,
                reference_inclusivity,
            )),
        }
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
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedRelIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(_) | Bound::Excluded(_), Bound::Included(_) | Bound::Excluded(_))
            | (Bound::Unbounded, Bound::Unbounded) => Err(HalfBoundedRelIntervalTryFromRangeError),
            (Bound::Unbounded, Bound::Included(&reference)) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Unbounded, Bound::Excluded(&reference)) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Included(&reference), Bound::Unbounded) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
            (Bound::Excluded(&reference), Bound::Unbounded) => Ok(Self::new_from_offset_and_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        }
    }

    pub fn reference(&self) -> RelFiniteBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_finite_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_finite_bound(),
        }
    }

    pub fn reference_pos(&self) -> RelFiniteBoundPos {
        self.reference().pos()
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
    /// let half_bounded_interval =
    ///     HalfBoundedRelInterval::new(ref_offset, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.reference(), ref_offset);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference_offset(&self) -> SignedDuration {
        self.reference().pos().offset()
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
    /// let half_bounded_interval = HalfBoundedRelInterval::new_with_inclusivity(
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
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference().pos().inclusivity()
    }

    pub fn set_reference(&mut self, new_reference: RelFiniteBound) {
        match new_reference {
            RelFiniteBound::Start(finite_start) => {
                *self = Self::ToFuture(HalfBoundedToFutureRelInterval::new(finite_start))
            },
            RelFiniteBound::End(finite_end) => *self = Self::ToPast(HalfBoundedToPastRelInterval::new(finite_end)),
        }
    }

    pub fn set_reference_pos(&mut self, new_reference_pos: RelFiniteBoundPos) {
        match self {
            Self::ToFuture(hb_to_future) => *hb_to_future.start_mut().pos_mut() = new_reference_pos,
            Self::ToPast(hb_to_past) => *hb_to_past.end_mut().pos_mut() = new_reference_pos,
        }
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
    pub fn set_reference_offset(&mut self, new_reference_offset: SignedDuration) {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start_mut().pos_mut().set_offset(new_reference_offset),
            Self::ToPast(hb_to_past) => hb_to_past.end_mut().pos_mut().set_offset(new_reference_offset),
        }
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
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start_mut().pos_mut().set_inclusivity(new_inclusivity),
            Self::ToPast(hb_to_past) => hb_to_past.end_mut().pos_mut().set_inclusivity(new_inclusivity),
        }
    }

    /// Sets the opening direction
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
    /// half_bounded_interval.set_opening_direction(OpeningDirection::ToPast);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToPast
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        match new_opening_direction {
            OpeningDirection::ToFuture => {
                *self = Self::ToFuture(HalfBoundedToFutureRelInterval::new(
                    self.reference_pos().to_finite_start_bound(),
                ));
            },
            OpeningDirection::ToPast => {
                *self = Self::ToPast(HalfBoundedToPastRelInterval::new(
                    self.reference_pos().to_finite_end_bound(),
                ));
            },
        }
    }

    pub fn opposite(self) -> Self {
        match self {
            Self::ToFuture(hb_to_future) => Self::ToPast(hb_to_future.opposite()),
            Self::ToPast(hb_to_past) => Self::ToFuture(hb_to_past.opposite()),
        }
    }

    pub fn half_bounded_to_future(self) -> Option<HalfBoundedToFutureRelInterval> {
        match self {
            Self::ToFuture(hb_to_future) => Some(hb_to_future),
            Self::ToPast(_) => None,
        }
    }

    pub fn half_bounded_to_past(self) -> Option<HalfBoundedToPastRelInterval> {
        match self {
            Self::ToFuture(_) => None,
            Self::ToPast(hb_to_past) => Some(hb_to_past),
        }
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
pub enum HalfBoundedRelIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeReference,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedRelIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeReference => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedRelIntervalCreationError {}

/// Error that can occur when trying to convert a [`SignedDuration`] range into a [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelIntervalTryFromRangeError;

impl Display for HalfBoundedRelIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `SignedDuration` range into a `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedRelIntervalTryFromRangeError {}

impl Interval for HalfBoundedRelInterval {}

impl HasOpenness for HalfBoundedRelInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedRelInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Rel
    }
}

impl HasDuration for HalfBoundedRelInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedRelInterval {
    fn opening_direction(&self) -> OpeningDirection {
        match self {
            Self::ToFuture(_) => OpeningDirection::ToFuture,
            Self::ToPast(_) => OpeningDirection::ToPast,
        }
    }
}

impl HasRelBoundPair for HalfBoundedRelInterval {
    fn rel_bound_pair(&self) -> RelBoundPair {
        RelBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelStartBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_start_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.start(),
        }
    }

    fn rel_end(&self) -> RelEndBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.end(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_end_bound(),
        }
    }
}

impl IsEmpty for HalfBoundedRelInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<(SignedDuration, OpeningDirection)> for HalfBoundedRelInterval {
    fn from((offset, direction): (SignedDuration, OpeningDirection)) -> Self {
        HalfBoundedRelInterval::new_from_offset(offset, direction)
    }
}

impl From<(SignedDuration, BoundInclusivity, OpeningDirection)> for HalfBoundedRelInterval {
    fn from((offset, inclusivity, direction): (SignedDuration, BoundInclusivity, OpeningDirection)) -> Self {
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(offset, inclusivity, direction)
    }
}

impl From<(RelFiniteBoundPos, OpeningDirection)> for HalfBoundedRelInterval {
    fn from((reference, opening_direction): (RelFiniteBoundPos, OpeningDirection)) -> Self {
        Self::new_from_offset_and_inclusivity(reference.offset(), reference.inclusivity(), opening_direction)
    }
}

impl From<RangeFrom<SignedDuration>> for HalfBoundedRelInterval {
    fn from(range: RangeFrom<SignedDuration>) -> Self {
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<SignedDuration>> for HalfBoundedRelInterval {
    fn from(range: RangeTo<SignedDuration>) -> Self {
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<SignedDuration>> for HalfBoundedRelInterval {
    fn from(range: RangeToInclusive<SignedDuration>) -> Self {
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<HalfBoundedToFutureRelInterval> for HalfBoundedRelInterval {
    fn from(value: HalfBoundedToFutureRelInterval) -> Self {
        HalfBoundedRelInterval::ToFuture(value)
    }
}

impl From<HalfBoundedToPastRelInterval> for HalfBoundedRelInterval {
    fn from(value: HalfBoundedToPastRelInterval) -> Self {
        HalfBoundedRelInterval::ToPast(value)
    }
}

/// Error that can occur when trying to convert [`RelBoundPair`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelIntervalTryFromRelBoundPairError;

impl Display for HalfBoundedRelIntervalTryFromRelBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelBoundPair` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedRelIntervalTryFromRelBoundPairError {}

impl TryFrom<RelBoundPair> for HalfBoundedRelInterval {
    type Error = HalfBoundedRelIntervalTryFromRelBoundPairError;

    fn try_from(value: RelBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelStartBound::InfinitePast, RelEndBound::Finite(finite_end)) => {
                Ok(Self::ToPast(HalfBoundedToPastRelInterval::new(finite_end)))
            },
            (RelStartBound::Finite(finite_start), RelEndBound::InfiniteFuture) => {
                Ok(Self::ToFuture(HalfBoundedToFutureRelInterval::new(finite_start)))
            },
            _ => Err(HalfBoundedRelIntervalTryFromRelBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelInterval`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelIntervalTryFromRelIntervalError;

impl Display for HalfBoundedRelIntervalTryFromRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelInterval` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedRelIntervalTryFromRelIntervalError {}

impl TryFrom<RelInterval> for HalfBoundedRelInterval {
    type Error = HalfBoundedRelIntervalTryFromRelIntervalError;

    fn try_from(value: RelInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedRelIntervalTryFromRelIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelInterval`] into [`HalfBoundedRelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelIntervalTryFromEmptiableRelIntervalError;

impl Display for HalfBoundedRelIntervalTryFromEmptiableRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelInterval` into `HalfBoundedRelInterval`"
        )
    }
}

impl Error for HalfBoundedRelIntervalTryFromEmptiableRelIntervalError {}

impl TryFrom<EmptiableRelInterval> for HalfBoundedRelInterval {
    type Error = HalfBoundedRelIntervalTryFromEmptiableRelIntervalError;

    fn try_from(value: EmptiableRelInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedRelIntervalTryFromEmptiableRelIntervalError)?,
        )
        .or(Err(HalfBoundedRelIntervalTryFromEmptiableRelIntervalError))
    }
}

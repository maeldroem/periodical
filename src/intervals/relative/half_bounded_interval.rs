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
//! [openness](Openness) invariant, see [`RelativeBoundPair`].

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
    EmptiableRelativeInterval,
    HalfBoundedToFutureRelativeInterval,
    HalfBoundedToPastRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeFiniteBoundPosition,
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
pub enum HalfBoundedRelativeInterval {
    ToFuture(HalfBoundedToFutureRelativeInterval),
    ToPast(HalfBoundedToPastRelativeInterval),
}

impl HalfBoundedRelativeInterval {
    pub fn new(reference: RelativeFiniteBoundPosition, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureRelativeInterval::new(
                reference.to_finite_start_bound(),
            )),
            OpeningDirection::ToPast => {
                Self::ToPast(HalfBoundedToPastRelativeInterval::new(reference.to_finite_end_bound()))
            },
        }
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
    pub fn new_from_offset(reference: SignedDuration, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => {
                Self::ToFuture(HalfBoundedToFutureRelativeInterval::new_from_offset(reference))
            },
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastRelativeInterval::new_from_offset(reference)),
        }
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
    pub fn new_from_offset_and_inclusivity(
        reference: SignedDuration,
        reference_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(
                HalfBoundedToFutureRelativeInterval::new_from_offset_and_inclusivity(reference, reference_inclusivity),
            ),
            OpeningDirection::ToPast => Self::ToPast(
                HalfBoundedToPastRelativeInterval::new_from_offset_and_inclusivity(reference, reference_inclusivity),
            ),
        }
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
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedRelativeIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(_) | Bound::Excluded(_), Bound::Included(_) | Bound::Excluded(_))
            | (Bound::Unbounded, Bound::Unbounded) => Err(HalfBoundedRelativeIntervalTryFromRangeError),
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

    pub fn reference(&self) -> RelativeFiniteBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_finite_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_finite_bound(),
        }
    }

    pub fn reference_pos(&self) -> RelativeFiniteBoundPosition {
        self.reference().pos()
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
    pub fn reference_offset(&self) -> SignedDuration {
        self.reference().pos().offset()
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
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference().pos().inclusivity()
    }

    pub fn set_reference(&mut self, new_reference: RelativeFiniteBound) {
        match new_reference {
            RelativeFiniteBound::Start(finite_start) => {
                *self = Self::ToFuture(HalfBoundedToFutureRelativeInterval::new(finite_start))
            },
            RelativeFiniteBound::End(finite_end) => {
                *self = Self::ToPast(HalfBoundedToPastRelativeInterval::new(finite_end))
            },
        }
    }

    pub fn set_reference_pos(&mut self, new_reference_pos: RelativeFiniteBoundPosition) {
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
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_offset = "2025-01-01 08:00:00Z".parse::<SignedDuration>()?;
    ///
    /// let mut half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(ref_offset, OpeningDirection::ToFuture);
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
                *self = Self::ToFuture(HalfBoundedToFutureRelativeInterval::new(
                    self.reference_pos().to_finite_start_bound(),
                ));
            },
            OpeningDirection::ToPast => {
                *self = Self::ToPast(HalfBoundedToPastRelativeInterval::new(
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

    pub fn half_bounded_to_future(self) -> Option<HalfBoundedToFutureRelativeInterval> {
        match self {
            Self::ToFuture(hb_to_future) => Some(hb_to_future),
            Self::ToPast(_) => None,
        }
    }

    pub fn half_bounded_to_past(self) -> Option<HalfBoundedToPastRelativeInterval> {
        match self {
            Self::ToFuture(_) => None,
            Self::ToPast(hb_to_past) => Some(hb_to_past),
        }
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
pub enum HalfBoundedRelativeIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeReference,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedRelativeIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeReference => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedRelativeIntervalCreationError {}

/// Error that can occur when trying to convert a [`SignedDuration`] range into a [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelativeIntervalTryFromRangeError;

impl Display for HalfBoundedRelativeIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `SignedDuration` range into a `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedRelativeIntervalTryFromRangeError {}

impl Interval for HalfBoundedRelativeInterval {}

impl HasOpenness for HalfBoundedRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for HalfBoundedRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedRelativeInterval {
    fn opening_direction(&self) -> OpeningDirection {
        match self {
            Self::ToFuture(_) => OpeningDirection::ToFuture,
            Self::ToPast(_) => OpeningDirection::ToPast,
        }
    }
}

impl HasRelativeBoundPair for HalfBoundedRelativeInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        RelativeBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_start_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.start(),
        }
    }

    fn rel_end(&self) -> RelativeEndBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.end(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_end_bound(),
        }
    }
}

impl IsEmpty for HalfBoundedRelativeInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<(SignedDuration, OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from((offset, direction): (SignedDuration, OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new_from_offset(offset, direction)
    }
}

impl From<(SignedDuration, BoundInclusivity, OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from((offset, inclusivity, direction): (SignedDuration, BoundInclusivity, OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(offset, inclusivity, direction)
    }
}

impl From<(RelativeFiniteBoundPosition, OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from((reference, opening_direction): (RelativeFiniteBoundPosition, OpeningDirection)) -> Self {
        Self::new_from_offset_and_inclusivity(reference.offset(), reference.inclusivity(), opening_direction)
    }
}

impl From<RangeFrom<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeFrom<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeTo<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeToInclusive<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<HalfBoundedToFutureRelativeInterval> for HalfBoundedRelativeInterval {
    fn from(value: HalfBoundedToFutureRelativeInterval) -> Self {
        HalfBoundedRelativeInterval::ToFuture(value)
    }
}

impl From<HalfBoundedToPastRelativeInterval> for HalfBoundedRelativeInterval {
    fn from(value: HalfBoundedToPastRelativeInterval) -> Self {
        HalfBoundedRelativeInterval::ToPast(value)
    }
}

/// Error that can occur when trying to convert [`RelativeBoundPair`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelativeIntervalTryFromRelativeBoundPairError;

impl Display for HalfBoundedRelativeIntervalTryFromRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeBoundPair` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedRelativeIntervalTryFromRelativeBoundPairError {}

impl TryFrom<RelativeBoundPair> for HalfBoundedRelativeInterval {
    type Error = HalfBoundedRelativeIntervalTryFromRelativeBoundPairError;

    fn try_from(value: RelativeBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(finite_end)) => {
                Ok(Self::ToPast(HalfBoundedToPastRelativeInterval::new(finite_end)))
            },
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::InfiniteFuture) => {
                Ok(Self::ToFuture(HalfBoundedToFutureRelativeInterval::new(finite_start)))
            },
            _ => Err(HalfBoundedRelativeIntervalTryFromRelativeBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelativeInterval`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelativeIntervalTryFromRelativeIntervalError;

impl Display for HalfBoundedRelativeIntervalTryFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeInterval` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedRelativeIntervalTryFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for HalfBoundedRelativeInterval {
    type Error = HalfBoundedRelativeIntervalTryFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedRelativeIntervalTryFromRelativeIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeInterval`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError;

impl Display for HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeInterval` into `HalfBoundedRelativeInterval`"
        )
    }
}

impl Error for HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError {}

impl TryFrom<EmptiableRelativeInterval> for HalfBoundedRelativeInterval {
    type Error = HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError;

    fn try_from(value: EmptiableRelativeInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)?,
        )
        .or(Err(HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError))
    }
}

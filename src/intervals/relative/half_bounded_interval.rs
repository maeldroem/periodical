//! Relative half-bounded interval
//!
//! A half-bounded interval has a reference offset and an opening direction.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a half-bounded interval must remain a
//! half-bounded interval.
//!
//! However, similar to [`RelInterval`], you can switch between one variant
//! and another, but the contained half-bounded interval must retain its own
//! [opening direction](OpeningDirection) invariant.
//!
//! Usually this structure is for dealing with half-bounded intervals, regardless
//! of their opening direction, as a single type.
//!
//! If you are looking for an absolute interval that doesn't keep the
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

/// Relative half-bounded interval
///
/// A half-bounded interval has a reference offset and an opening direction.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a half-bounded interval must remain a
/// half-bounded interval.
///
/// However, similar to [`RelInterval`], you can switch between one variant
/// and another, but the contained half-bounded interval must retain its own
/// [opening direction](OpeningDirection) invariant.
///
/// Usually this structure is for dealing with half-bounded intervals, regardless
/// of their opening direction, as a single type.
///
/// If you are looking for an absolute interval that doesn't keep the
/// [openness](Openness) invariant, see [`RelBoundPair`].
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HalfBoundedRelInterval {
    ToFuture(HalfBoundedToFutureRelInterval),
    ToPast(HalfBoundedToPastRelInterval),
}

impl HalfBoundedRelInterval {
    /// Creates a new half-bounded relative interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelFiniteBoundPos,
    /// #     HalfBoundedRelInterval,
    /// #     HalfBoundedToFutureRelInterval,
    /// # };
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(10));
    /// let half_bounded = HalfBoundedRelInterval::new(pos, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(
    ///     half_bounded,
    ///     HalfBoundedRelInterval::ToFuture(HalfBoundedToFutureRelInterval::new(
    ///         pos.to_finite_start_bound()
    ///     ))
    /// );
    /// ```
    #[must_use]
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

    /// Creates a new half-bounded relative interval from a given offset and opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection, HasOpeningDirection};
    /// let ref_offset = SignedDuration::from_hours(10);
    /// let half_bounded_interval =
    ///     HalfBoundedRelInterval::from_offset(ref_offset, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.reference_offset(), ref_offset);
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToPast
    /// );
    /// ```
    #[must_use]
    pub fn from_offset(reference: SignedDuration, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureRelInterval::from_offset(reference)),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastRelInterval::from_offset(reference)),
        }
    }

    /// Creates a new [`HalfBoundedRelInterval`] from a given offset, bound inclusivity, and opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection, HasOpeningDirection};
    /// let ref_offset = SignedDuration::from_hours(10);
    /// let half_bounded_interval = HalfBoundedRelInterval::from_offset_incl(
    ///     ref_offset,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_offset(), ref_offset);
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToFuture
    /// );
    /// ```
    #[must_use]
    pub fn from_offset_incl(
        reference: SignedDuration,
        reference_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureRelInterval::from_offset_incl(
                reference,
                reference_inclusivity,
            )),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastRelInterval::from_offset_incl(
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
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection, HasOpeningDirection};
    /// let reference = SignedDuration::from_hours(10);
    /// let interval = HalfBoundedRelInterval::try_from_range(..reference)?;
    ///
    /// assert_eq!(interval.reference_offset(), reference);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedRelIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(_) | Bound::Excluded(_), Bound::Included(_) | Bound::Excluded(_))
            | (Bound::Unbounded, Bound::Unbounded) => Err(HalfBoundedRelIntervalTryFromRangeError),
            (Bound::Unbounded, Bound::Included(&reference)) => Ok(Self::from_offset_incl(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Unbounded, Bound::Excluded(&reference)) => Ok(Self::from_offset_incl(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Included(&reference), Bound::Unbounded) => Ok(Self::from_offset_incl(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
            (Bound::Excluded(&reference), Bound::Unbounded) => Ok(Self::from_offset_incl(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        }
    }

    /// Returns the reference's finite bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, HalfBoundedRelInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(
    ///     half_bounded.reference(),
    ///     RelFiniteBoundPos::new(offset)
    ///         .to_finite_start_bound()
    ///         .to_finite_bound()
    /// );
    /// ```
    #[must_use]
    pub fn reference(&self) -> RelFiniteBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_finite_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_finite_bound(),
        }
    }

    /// Returns the reference's finite bound position
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, HalfBoundedRelInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(10));
    /// let half_bounded = HalfBoundedRelInterval::new(ref_pos, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(half_bounded.reference_pos(), ref_pos);
    /// ```
    #[must_use]
    pub fn reference_pos(&self) -> RelFiniteBoundPos {
        self.reference().pos()
    }

    /// Returns the reference's offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedRelInterval::from_offset(ref_offset, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded.reference_offset(), ref_offset);
    /// ```
    #[must_use]
    pub fn reference_offset(&self) -> SignedDuration {
        self.reference().pos().offset()
    }

    /// Returns the reference's inclusivity
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedRelInterval::from_offset_incl(
    ///     ref_offset,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(
    ///     half_bounded.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference().pos().inclusivity()
    }

    /// Sets the reference to a new finite bound
    ///
    /// Since [`RelFiniteBound`] contains information about extremality, this operation can change
    /// the opening direction of the stored half-bounded interval.
    /// For example, if a finite bound of [`Start`](RelFiniteBound::Start) variant is given, it will
    /// result in this instance becoming a half-bounded interval of [`ToFuture`](OpeningDirection::ToFuture)
    /// opening direction.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{HalfBoundedRelInterval, RelFiniteBoundPos};
    /// # use periodical::intervals::meta::{OpeningDirection, HasOpeningDirection};
    /// let mut half_bounded = HalfBoundedRelInterval::from_offset(
    ///     SignedDuration::from_hours(10),
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_offset = SignedDuration::from_hours(20);
    /// half_bounded.set_reference(
    ///     RelFiniteBoundPos::new(new_offset)
    ///         .to_finite_end_bound()
    ///         .to_finite_bound(),
    /// );
    ///
    /// assert_eq!(half_bounded.reference_offset(), new_offset);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// ```
    pub fn set_reference(&mut self, new_reference: RelFiniteBound) {
        match new_reference {
            RelFiniteBound::Start(finite_start) => {
                *self = Self::ToFuture(HalfBoundedToFutureRelInterval::new(finite_start));
            },
            RelFiniteBound::End(finite_end) => *self = Self::ToPast(HalfBoundedToPastRelInterval::new(finite_end)),
        }
    }

    /// Sets the reference's bound position
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, HalfBoundedRelInterval};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let mut half_bounded = HalfBoundedRelInterval::from_offset(
    ///     SignedDuration::from_hours(10),
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_offset = SignedDuration::from_hours(20);
    /// half_bounded.set_reference_pos(RelFiniteBoundPos::new_with_incl(
    ///     new_offset,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert_eq!(half_bounded.reference_offset(), new_offset);
    /// assert_eq!(
    ///     half_bounded.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    pub fn set_reference_pos(&mut self, new_reference_pos: RelFiniteBoundPos) {
        match self {
            Self::ToFuture(hb_to_future) => *hb_to_future.start_mut().pos_mut() = new_reference_pos,
            Self::ToPast(hb_to_past) => *hb_to_past.end_mut().pos_mut() = new_reference_pos,
        }
    }

    /// Sets the reference's offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let mut half_bounded = HalfBoundedRelInterval::from_offset(
    ///     SignedDuration::from_hours(10),
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_offset = SignedDuration::from_hours(20);
    /// half_bounded.set_reference_offset(new_offset);
    ///
    /// assert_eq!(half_bounded.reference_offset(), new_offset);
    /// ```
    pub fn set_reference_offset(&mut self, new_reference_offset: SignedDuration) {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start_mut().pos_mut().set_offset(new_reference_offset),
            Self::ToPast(hb_to_past) => hb_to_past.end_mut().pos_mut().set_offset(new_reference_offset),
        }
    }

    /// Sets the reference's bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let mut half_bounded = HalfBoundedRelInterval::from_offset(
    ///     SignedDuration::from_hours(10),
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded.set_reference_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
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
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::{OpeningDirection, HasOpeningDirection};
    /// let mut half_bounded = HalfBoundedRelInterval::from_offset(
    ///     SignedDuration::from_hours(10),
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded.set_opening_direction(OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
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

    /// Returns the opposite half-bounded interval
    ///
    /// Returns a half-bounded interval of opposite opening direction and opposite bound inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, HalfBoundedRelInterval};
    /// # use periodical::intervals::meta::{OpeningDirection, BoundInclusivity};
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded = HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(
    ///     half_bounded.opposite(),
    ///     HalfBoundedRelInterval::from_offset_incl(
    ///         offset,
    ///         BoundInclusivity::Exclusive,
    ///         OpeningDirection::ToPast
    ///     )
    /// );
    /// ```
    #[must_use]
    pub fn opposite(self) -> Self {
        match self {
            Self::ToFuture(hb_to_future) => Self::ToPast(hb_to_future.opposite()),
            Self::ToPast(hb_to_past) => Self::ToFuture(hb_to_past.opposite()),
        }
    }

    /// Returns the content of the [`ToFuture`](HalfBoundedRelInterval::ToFuture) variant
    ///
    /// Consumes `self` and puts the content of the [`ToFuture`](HalfBoundedRelInterval::ToFuture)
    /// variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     HalfBoundedRelInterval,
    /// #     HalfBoundedToFutureRelInterval,
    /// #     HalfBoundedToPastRelInterval,
    /// # };
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded_to_future = HalfBoundedToFutureRelInterval::from_offset(offset);
    /// let half_bounded_to_past = HalfBoundedToPastRelInterval::from_offset(offset);
    ///
    /// assert_eq!(
    ///     half_bounded_to_future
    ///         .clone()
    ///         .to_half_bounded_interval()
    ///         .half_bounded_to_future(),
    ///     Some(half_bounded_to_future)
    /// );
    /// assert_eq!(
    ///     half_bounded_to_past
    ///         .to_half_bounded_interval()
    ///         .half_bounded_to_future(),
    ///     None
    /// );
    /// ```
    #[must_use]
    pub fn half_bounded_to_future(self) -> Option<HalfBoundedToFutureRelInterval> {
        match self {
            Self::ToFuture(hb_to_future) => Some(hb_to_future),
            Self::ToPast(_) => None,
        }
    }

    /// Returns the content of the [`ToPast`](HalfBoundedRelInterval::ToPast) variant
    ///
    /// Consumes `self` and puts the content of the [`ToPast`](HalfBoundedRelInterval::ToPast)
    /// variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     HalfBoundedRelInterval,
    /// #     HalfBoundedToFutureRelInterval,
    /// #     HalfBoundedToPastRelInterval,
    /// # };
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let offset = SignedDuration::from_hours(10);
    /// let half_bounded_to_future = HalfBoundedToFutureRelInterval::from_offset(offset);
    /// let half_bounded_to_past = HalfBoundedToPastRelInterval::from_offset(offset);
    ///
    /// assert_eq!(
    ///     half_bounded_to_future
    ///         .to_half_bounded_interval()
    ///         .half_bounded_to_past(),
    ///     None
    /// );
    /// assert_eq!(
    ///     half_bounded_to_past
    ///         .clone()
    ///         .to_half_bounded_interval()
    ///         .half_bounded_to_past(),
    ///     Some(half_bounded_to_past)
    /// );
    /// ```
    #[must_use]
    pub fn half_bounded_to_past(self) -> Option<HalfBoundedToPastRelInterval> {
        match self {
            Self::ToFuture(_) => None,
            Self::ToPast(hb_to_past) => Some(hb_to_past),
        }
    }

    /// Wraps `self` in [`RelInterval`]
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
        Relativity::Relative
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

impl HasIntervalTypeWithRel for HalfBoundedRelInterval {
    fn interval_type_with_rel(&self) -> IntervalTypeWithRel {
        IntervalTypeWithRel::RelHalfBounded(self.opening_direction())
    }
}

impl From<(SignedDuration, OpeningDirection)> for HalfBoundedRelInterval {
    fn from((offset, direction): (SignedDuration, OpeningDirection)) -> Self {
        HalfBoundedRelInterval::from_offset(offset, direction)
    }
}

impl From<(SignedDuration, BoundInclusivity, OpeningDirection)> for HalfBoundedRelInterval {
    fn from((offset, inclusivity, direction): (SignedDuration, BoundInclusivity, OpeningDirection)) -> Self {
        HalfBoundedRelInterval::from_offset_incl(offset, inclusivity, direction)
    }
}

impl From<(RelFiniteBoundPos, OpeningDirection)> for HalfBoundedRelInterval {
    fn from((reference, opening_direction): (RelFiniteBoundPos, OpeningDirection)) -> Self {
        Self::new(reference, opening_direction)
    }
}

impl From<RangeFrom<SignedDuration>> for HalfBoundedRelInterval {
    fn from(range: RangeFrom<SignedDuration>) -> Self {
        HalfBoundedRelInterval::from_offset_incl(range.start, BoundInclusivity::Inclusive, OpeningDirection::ToFuture)
    }
}

impl From<RangeTo<SignedDuration>> for HalfBoundedRelInterval {
    fn from(range: RangeTo<SignedDuration>) -> Self {
        HalfBoundedRelInterval::from_offset_incl(range.end, BoundInclusivity::Exclusive, OpeningDirection::ToPast)
    }
}

impl From<RangeToInclusive<SignedDuration>> for HalfBoundedRelInterval {
    fn from(range: RangeToInclusive<SignedDuration>) -> Self {
        HalfBoundedRelInterval::from_offset_incl(range.end, BoundInclusivity::Inclusive, OpeningDirection::ToPast)
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

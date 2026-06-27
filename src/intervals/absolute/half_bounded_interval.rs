//! Absolute half-bounded interval
//!
//! A half-bounded interval has a reference time and an opening direction.
//!
//! Similar to the other specific interval types, its [openness](Openness)
//! cannot change. That is to say a half-bounded interval must remain a
//! half-bounded interval.
//!
//! However, similar to [`AbsInterval`], you can switch between one variant
//! and another, but the contained half-bounded interval must retain its own
//! [opening direction](OpeningDirection) invariant.
//!
//! Usually this structure is for dealing with half-bounded intervals, regardless
//! of their opening direction, as a single type.
//!
//! If you are looking for an absolute interval that doesn't keep the
//! [openness](Openness) invariant, see [`AbsBoundPair`].

use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds, RangeFrom, RangeTo, RangeToInclusive};

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
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

/// Absolute half-bounded interval
///
/// A half-bounded interval has a reference time and an opening direction.
///
/// Similar to the other specific interval types, its [openness](Openness)
/// cannot change. That is to say a half-bounded interval must remain a
/// half-bounded interval.
///
/// However, similar to [`AbsInterval`], you can switch between one variant
/// and another, but the contained half-bounded interval must retain its own
/// [opening direction](OpeningDirection) invariant.
///
/// Usually this structure is for dealing with half-bounded intervals, regardless
/// of their opening direction, as a single type.
///
/// If you are looking for an absolute interval that doesn't keep the
/// [openness](Openness) invariant, see [`AbsBoundPair`].
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsInterval {
    ToFuture(HalfBoundedToFutureAbsInterval),
    ToPast(HalfBoundedToPastAbsInterval),
}

impl HalfBoundedAbsInterval {
    /// Creates a new half-bounded absolute interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsFiniteBoundPos,
    /// #     HalfBoundedAbsInterval,
    /// #     HalfBoundedToFutureAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let pos = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?);
    /// let half_bounded = HalfBoundedAbsInterval::new(pos, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(
    ///     half_bounded,
    ///     HalfBoundedAbsInterval::ToFuture(HalfBoundedToFutureAbsInterval::new(
    ///         pos.to_finite_start_bound()
    ///     ))
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new(reference: AbsFiniteBoundPos, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => {
                Self::ToFuture(HalfBoundedToFutureAbsInterval::new(reference.to_finite_start_bound()))
            },
            OpeningDirection::ToPast => {
                Self::ToPast(HalfBoundedToPastAbsInterval::new(reference.to_finite_end_bound()))
            },
        }
    }

    /// Creates a new half-bounded absolute interval from a given time and opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection, HasOpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded_interval =
    ///     HalfBoundedAbsInterval::from_time(ref_time, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
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
    pub fn from_time(reference: Timestamp, opening_direction: OpeningDirection) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureAbsInterval::from_time(reference)),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastAbsInterval::from_time(reference)),
        }
    }

    /// Creates a new [`HalfBoundedAbsInterval`] from a given time, bound inclusivity, and opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection, HasOpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded_interval = HalfBoundedAbsInterval::from_time_incl(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
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
    pub fn from_time_incl(
        reference: Timestamp,
        reference_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        match opening_direction {
            OpeningDirection::ToFuture => Self::ToFuture(HalfBoundedToFutureAbsInterval::from_time_incl(
                reference,
                reference_inclusivity,
            )),
            OpeningDirection::ToPast => Self::ToPast(HalfBoundedToPastAbsInterval::from_time_incl(
                reference,
                reference_inclusivity,
            )),
        }
    }

    /// Attempts to create a [`HalfBoundedAbsInterval`] from a [`Timestamp`] range
    ///
    /// # Errors
    ///
    /// Returns [`HalfBoundedAbsIntervalTryFromRangeError`] if there is not exactly
    /// one [unbounded](Bound::Unbounded) range bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection, HasOpeningDirection};
    /// let reference = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let interval = HalfBoundedAbsInterval::try_from_range(..reference)?;
    ///
    /// assert_eq!(interval.reference_time(), reference);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedAbsIntervalTryFromRangeError>
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(_) | Bound::Excluded(_), Bound::Included(_) | Bound::Excluded(_))
            | (Bound::Unbounded, Bound::Unbounded) => Err(HalfBoundedAbsIntervalTryFromRangeError),
            (Bound::Unbounded, Bound::Included(&reference)) => Ok(Self::from_time_incl(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Unbounded, Bound::Excluded(&reference)) => Ok(Self::from_time_incl(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Included(&reference), Bound::Unbounded) => Ok(Self::from_time_incl(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
            (Bound::Excluded(&reference), Bound::Unbounded) => Ok(Self::from_time_incl(
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
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, HalfBoundedAbsInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(
    ///     half_bounded.reference(),
    ///     AbsFiniteBoundPos::new(time)
    ///         .to_finite_start_bound()
    ///         .to_finite_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference(&self) -> AbsFiniteBound {
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
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, HalfBoundedAbsInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_pos = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?);
    /// let half_bounded = HalfBoundedAbsInterval::new(ref_pos, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(half_bounded.reference_pos(), ref_pos);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference_pos(&self) -> AbsFiniteBoundPos {
        self.reference().pos()
    }

    /// Returns the reference's time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedAbsInterval::from_time(ref_time, OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded.reference_time(), ref_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference_time(&self) -> Timestamp {
        self.reference().pos().time()
    }

    /// Returns the reference's inclusivity
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedAbsInterval::from_time_incl(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(
    ///     half_bounded.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference().pos().inclusivity()
    }

    /// Sets the reference to a new finite bound
    ///
    /// Since [`AbsFiniteBound`] contains information about extremality, this operation can change
    /// the opening direction of the stored half-bounded interval.
    /// For example, if a finite bound of [`Start`](AbsFiniteBound::Start) variant is given, it will
    /// result in this instance becoming a half-bounded interval of [`ToFuture`](OpeningDirection::ToFuture)
    /// opening direction.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{HalfBoundedAbsInterval, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::{OpeningDirection, HasOpeningDirection};
    /// let mut half_bounded = HalfBoundedAbsInterval::from_time(
    ///     "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_time = "2027-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// half_bounded.set_reference(
    ///     AbsFiniteBoundPos::new(new_time)
    ///         .to_finite_end_bound()
    ///         .to_finite_bound(),
    /// );
    ///
    /// assert_eq!(half_bounded.reference_time(), new_time);
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_reference(&mut self, new_reference: AbsFiniteBound) {
        match new_reference {
            AbsFiniteBound::Start(finite_start) => {
                *self = Self::ToFuture(HalfBoundedToFutureAbsInterval::new(finite_start));
            },
            AbsFiniteBound::End(finite_end) => *self = Self::ToPast(HalfBoundedToPastAbsInterval::new(finite_end)),
        }
    }

    /// Sets the reference's bound position
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, HalfBoundedAbsInterval};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let mut half_bounded = HalfBoundedAbsInterval::from_time(
    ///     "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_time = "2027-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// half_bounded.set_reference_pos(AbsFiniteBoundPos::new_with_incl(
    ///     new_time,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert_eq!(half_bounded.reference_time(), new_time);
    /// assert_eq!(
    ///     half_bounded.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_reference_pos(&mut self, new_reference_pos: AbsFiniteBoundPos) {
        match self {
            Self::ToFuture(hb_to_future) => *hb_to_future.start_mut().pos_mut() = new_reference_pos,
            Self::ToPast(hb_to_past) => *hb_to_past.end_mut().pos_mut() = new_reference_pos,
        }
    }

    /// Sets the reference's time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let mut half_bounded = HalfBoundedAbsInterval::from_time(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// half_bounded.set_reference_time(new_time);
    ///
    /// assert_eq!(half_bounded.reference_time(), new_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_reference_time(&mut self, new_reference_time: Timestamp) {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start_mut().pos_mut().set_time(new_reference_time),
            Self::ToPast(hb_to_past) => hb_to_past.end_mut().pos_mut().set_time(new_reference_time),
        }
    }

    /// Sets the reference's bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let mut half_bounded = HalfBoundedAbsInterval::from_time(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded.set_reference_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     half_bounded.reference_inclusivity(),
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
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::{OpeningDirection, HasOpeningDirection};
    /// let mut half_bounded = HalfBoundedAbsInterval::from_time(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded.set_opening_direction(OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        match new_opening_direction {
            OpeningDirection::ToFuture => {
                *self = Self::ToFuture(HalfBoundedToFutureAbsInterval::new(
                    self.reference_pos().to_finite_start_bound(),
                ));
            },
            OpeningDirection::ToPast => {
                *self = Self::ToPast(HalfBoundedToPastAbsInterval::new(
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
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, HalfBoundedAbsInterval};
    /// # use periodical::intervals::meta::{OpeningDirection, BoundInclusivity};
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded = HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToFuture);
    ///
    /// assert_eq!(
    ///     half_bounded.opposite(),
    ///     HalfBoundedAbsInterval::from_time_incl(
    ///         time,
    ///         BoundInclusivity::Exclusive,
    ///         OpeningDirection::ToPast
    ///     )
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(self) -> Self {
        match self {
            Self::ToFuture(hb_to_future) => Self::ToPast(hb_to_future.opposite()),
            Self::ToPast(hb_to_past) => Self::ToFuture(hb_to_past.opposite()),
        }
    }

    /// Returns the content of the [`ToFuture`](HalfBoundedAbsInterval::ToFuture) variant
    ///
    /// Consumes `self` and puts the content of the [`ToFuture`](HalfBoundedAbsInterval::ToFuture)
    /// variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     HalfBoundedAbsInterval,
    /// #     HalfBoundedToFutureAbsInterval,
    /// #     HalfBoundedToPastAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded_to_future = HalfBoundedToFutureAbsInterval::from_time(time);
    /// let half_bounded_to_past = HalfBoundedToPastAbsInterval::from_time(time);
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
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn half_bounded_to_future(self) -> Option<HalfBoundedToFutureAbsInterval> {
        match self {
            Self::ToFuture(hb_to_future) => Some(hb_to_future),
            Self::ToPast(_) => None,
        }
    }

    /// Returns the content of the [`ToPast`](HalfBoundedAbsInterval::ToPast) variant
    ///
    /// Consumes `self` and puts the content of the [`ToPast`](HalfBoundedAbsInterval::ToPast)
    /// variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     HalfBoundedAbsInterval,
    /// #     HalfBoundedToFutureAbsInterval,
    /// #     HalfBoundedToPastAbsInterval,
    /// # };
    /// # use periodical::intervals::meta::{OpeningDirection, HasOpeningDirection};
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let half_bounded_to_future = HalfBoundedToFutureAbsInterval::from_time(time);
    /// let half_bounded_to_past = HalfBoundedToPastAbsInterval::from_time(time);
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
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn half_bounded_to_past(self) -> Option<HalfBoundedToPastAbsInterval> {
        match self {
            Self::ToFuture(_) => None,
            Self::ToPast(hb_to_past) => Some(hb_to_past),
        }
    }

    /// Wraps `self` in [`AbsInterval`]
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
pub enum HalfBoundedAbsIntervalCreationError {
    /// Reference could not be created as it was out of range
    OutOfRangeReference,
    /// Something went wrong when computing data for creating the interval
    ///
    /// This can be caused by multiple factors, like numbers overflowing, input
    /// not respecting invariants, etc.
    ComputationError,
}

impl Display for HalfBoundedAbsIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeReference => write!(f, "Reference could not be created as it was out of range"),
            Self::ComputationError => write!(f, "Something went wrong when computing data for creating the interval"),
        }
    }
}

impl Error for HalfBoundedAbsIntervalCreationError {}

/// Error that can occur when trying to convert a [`Timestamp`] range into a [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromRangeError;

impl Display for HalfBoundedAbsIntervalTryFromRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert a `Timestamp` range into a `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromRangeError {}

impl Interval for HalfBoundedAbsInterval {}

impl HasOpenness for HalfBoundedAbsInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedAbsInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for HalfBoundedAbsInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasOpeningDirection for HalfBoundedAbsInterval {
    fn opening_direction(&self) -> OpeningDirection {
        match self {
            Self::ToFuture(_) => OpeningDirection::ToFuture,
            Self::ToPast(_) => OpeningDirection::ToPast,
        }
    }
}

impl HasAbsBoundPair for HalfBoundedAbsInterval {
    fn abs_bound_pair(&self) -> AbsBoundPair {
        AbsBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsStartBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.start().to_start_bound(),
            Self::ToPast(hb_to_past) => hb_to_past.start(),
        }
    }

    fn abs_end(&self) -> AbsEndBound {
        match self {
            Self::ToFuture(hb_to_future) => hb_to_future.end(),
            Self::ToPast(hb_to_past) => hb_to_past.end().to_end_bound(),
        }
    }
}

impl IsEmpty for HalfBoundedAbsInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl HasIntervalTypeWithRel for HalfBoundedAbsInterval {
    fn interval_type_with_rel(&self) -> IntervalTypeWithRel {
        IntervalTypeWithRel::AbsHalfBounded(self.opening_direction())
    }
}

impl From<(Timestamp, OpeningDirection)> for HalfBoundedAbsInterval {
    fn from((time, direction): (Timestamp, OpeningDirection)) -> Self {
        HalfBoundedAbsInterval::from_time(time, direction)
    }
}

impl From<(Timestamp, BoundInclusivity, OpeningDirection)> for HalfBoundedAbsInterval {
    fn from((time, inclusivity, direction): (Timestamp, BoundInclusivity, OpeningDirection)) -> Self {
        HalfBoundedAbsInterval::from_time_incl(time, inclusivity, direction)
    }
}

impl From<(AbsFiniteBoundPos, OpeningDirection)> for HalfBoundedAbsInterval {
    fn from((reference, opening_direction): (AbsFiniteBoundPos, OpeningDirection)) -> Self {
        Self::new(reference, opening_direction)
    }
}

impl From<RangeFrom<Timestamp>> for HalfBoundedAbsInterval {
    fn from(range: RangeFrom<Timestamp>) -> Self {
        HalfBoundedAbsInterval::from_time_incl(range.start, BoundInclusivity::Inclusive, OpeningDirection::ToFuture)
    }
}

impl From<RangeTo<Timestamp>> for HalfBoundedAbsInterval {
    fn from(range: RangeTo<Timestamp>) -> Self {
        HalfBoundedAbsInterval::from_time_incl(range.end, BoundInclusivity::Exclusive, OpeningDirection::ToPast)
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedAbsInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedAbsInterval::from_time_incl(range.end, BoundInclusivity::Inclusive, OpeningDirection::ToPast)
    }
}

impl From<HalfBoundedToFutureAbsInterval> for HalfBoundedAbsInterval {
    fn from(value: HalfBoundedToFutureAbsInterval) -> Self {
        HalfBoundedAbsInterval::ToFuture(value)
    }
}

impl From<HalfBoundedToPastAbsInterval> for HalfBoundedAbsInterval {
    fn from(value: HalfBoundedToPastAbsInterval) -> Self {
        HalfBoundedAbsInterval::ToPast(value)
    }
}

/// Error that can occur when trying to convert [`AbsBoundPair`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromAbsBoundPairError;

impl Display for HalfBoundedAbsIntervalTryFromAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsBoundPair` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromAbsBoundPairError {}

impl TryFrom<AbsBoundPair> for HalfBoundedAbsInterval {
    type Error = HalfBoundedAbsIntervalTryFromAbsBoundPairError;

    fn try_from(value: AbsBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsStartBound::InfinitePast, AbsEndBound::Finite(finite_end)) => {
                Ok(Self::ToPast(HalfBoundedToPastAbsInterval::new(finite_end)))
            },
            (AbsStartBound::Finite(finite_start), AbsEndBound::InfiniteFuture) => {
                Ok(Self::ToFuture(HalfBoundedToFutureAbsInterval::new(finite_start)))
            },
            _ => Err(HalfBoundedAbsIntervalTryFromAbsBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`AbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromAbsIntervalError;

impl Display for HalfBoundedAbsIntervalTryFromAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromAbsIntervalError {}

impl TryFrom<AbsInterval> for HalfBoundedAbsInterval {
    type Error = HalfBoundedAbsIntervalTryFromAbsIntervalError;

    fn try_from(value: AbsInterval) -> Result<Self, Self::Error> {
        value
            .half_bounded()
            .ok_or(HalfBoundedAbsIntervalTryFromAbsIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsInterval`] into [`HalfBoundedAbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError;

impl Display for HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsInterval` into `HalfBoundedAbsInterval`"
        )
    }
}

impl Error for HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError {}

impl TryFrom<EmptiableAbsInterval> for HalfBoundedAbsInterval {
    type Error = HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError;

    fn try_from(value: EmptiableAbsInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError)?,
        )
        .or(Err(HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError))
    }
}

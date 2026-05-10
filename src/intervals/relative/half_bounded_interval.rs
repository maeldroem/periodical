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
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};

/// Relative half-bounded interval
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
pub struct HalfBoundedRelativeInterval {
    reference: SignedDuration,
    opening_direction: OpeningDirection,
    reference_inclusivity: BoundInclusivity,
}

impl HalfBoundedRelativeInterval {
    /// Creates a new [`HalfBoundedRelativeInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(SignedDuration::from_hours(8), OpeningDirection::ToPast);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.reference(),
    ///     SignedDuration::from_hours(8)
    /// );
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
    pub fn new(reference: SignedDuration, opening_direction: OpeningDirection) -> Self {
        HalfBoundedRelativeInterval {
            reference,
            opening_direction,
            reference_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`HalfBoundedRelativeInterval`] with the given bound
    /// inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     SignedDuration::from_hours(8),
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(
    ///     half_bounded_interval.reference(),
    ///     SignedDuration::from_hours(8)
    /// );
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToPast
    /// );
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        reference: SignedDuration,
        reference_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfBoundedRelativeInterval {
            reference,
            opening_direction,
            reference_inclusivity,
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
    /// # use periodical::intervals::relative::{
    /// #     HalfBoundedRelativeInterval, HalfBoundedRelativeIntervalTryFromRangeError,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let reference = SignedDuration::from_hours(8);
    ///
    /// let interval = HalfBoundedRelativeInterval::try_from_range(..reference)?;
    ///
    /// assert_eq!(interval.reference(), reference);
    /// assert_eq!(
    ///     interval.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn try_from_range<R>(range: R) -> Result<Self, HalfBoundedRelativeIntervalTryFromRangeError>
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(_) | Bound::Excluded(_), Bound::Included(_) | Bound::Excluded(_))
            | (Bound::Unbounded, Bound::Unbounded) => Err(HalfBoundedRelativeIntervalTryFromRangeError),
            (Bound::Unbounded, Bound::Included(&reference)) => Ok(Self::new_with_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Unbounded, Bound::Excluded(&reference)) => Ok(Self::new_with_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            (Bound::Included(&reference), Bound::Unbounded) => Ok(Self::new_with_inclusivity(
                reference,
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
            (Bound::Excluded(&reference), Bound::Unbounded) => Ok(Self::new_with_inclusivity(
                reference,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        }
    }

    /// Returns the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(SignedDuration::from_hours(8), OpeningDirection::ToPast);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.reference(),
    ///     SignedDuration::from_hours(8)
    /// );
    /// ```
    #[must_use]
    pub fn reference(&self) -> SignedDuration {
        self.reference
    }

    /// Returns the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(SignedDuration::from_hours(8), OpeningDirection::ToPast);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToPast
    /// );
    /// ```
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     SignedDuration::from_hours(8),
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference_inclusivity
    }

    /// Sets the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let mut half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(SignedDuration::from_hours(8), OpeningDirection::ToPast);
    ///
    /// half_bounded_interval.set_reference(SignedDuration::from_hours(1));
    ///
    /// assert_eq!(
    ///     half_bounded_interval.reference(),
    ///     SignedDuration::from_hours(1)
    /// );
    /// ```
    pub fn set_reference(&mut self, new_reference: SignedDuration) {
        self.reference = new_reference;
    }

    /// Sets the inclusivity of the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let mut half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     SignedDuration::from_hours(8),
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// half_bounded_interval.set_reference_inclusivity(BoundInclusivity::Inclusive);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.reference_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// ```
    pub fn set_reference_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_inclusivity = new_inclusivity;
    }

    /// Sets the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let mut half_bounded_interval =
    ///     HalfBoundedRelativeInterval::new(SignedDuration::from_hours(8), OpeningDirection::ToPast);
    ///
    /// half_bounded_interval.set_opening_direction(OpeningDirection::ToFuture);
    ///
    /// assert_eq!(
    ///     half_bounded_interval.opening_direction(),
    ///     OpeningDirection::ToFuture
    /// );
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        self.opening_direction = new_opening_direction;
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

impl HasRelativeBoundPair for HalfBoundedRelativeInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        RelativeBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        match self.opening_direction {
            OpeningDirection::ToPast => RelativeStartBound::InfinitePast,
            OpeningDirection::ToFuture => {
                RelativeFiniteBound::new_with_inclusivity(self.reference, self.reference_inclusivity).to_start_bound()
            },
        }
    }

    fn rel_end(&self) -> RelativeEndBound {
        match self.opening_direction {
            OpeningDirection::ToPast => {
                RelativeFiniteBound::new_with_inclusivity(self.reference, self.reference_inclusivity).to_end_bound()
            },
            OpeningDirection::ToFuture => RelativeEndBound::InfiniteFuture,
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
        HalfBoundedRelativeInterval::new(offset, direction)
    }
}

impl From<(SignedDuration, BoundInclusivity, OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from((offset, inclusivity, direction): (SignedDuration, BoundInclusivity, OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(offset, inclusivity, direction)
    }
}

impl From<RangeFrom<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeFrom<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeTo<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeToInclusive<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
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
                Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
                    finite_end.offset(),
                    finite_end.inclusivity(),
                    OpeningDirection::ToPast,
                ))
            },
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::InfiniteFuture) => {
                Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity(),
                    OpeningDirection::ToFuture,
                ))
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

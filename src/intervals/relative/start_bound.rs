//! Relative start bound
//!
//! Represents the start bound of a relative interval. It can either be finite,
//! in which case it will contain an [`RelativeFiniteBoundPosition`], or represent an
//! open start bound through
//! the [`InfinitePast`](RelativeStartBound::InfinitePast) variant.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality, HasBoundInclusivity};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundOverlapAmbiguity, BoundPartialEq, BoundPartialOrd};
use crate::intervals::relative::{
    RelativeBound,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteEndBound,
    RelativeFiniteStartBound,
};

/// A relative start bound
///
/// Represents the start bound of an interval, may it be infinitely in the past
/// or at a precise offset, in which case it contains an
/// [`RelativeFiniteBoundPosition`].
///
/// Contrary to specific relative interval types, both [`RelativeStartBound`]
/// and [`RelativeEndBound`] use an offset, and not an offset for the start and
/// a length for the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelativeStartBound {
    Finite(RelativeFiniteStartBound),
    InfinitePast,
}

impl RelativeStartBound {
    /// Wraps the start bound of the corresponding [`RelativeBound`] variant
    #[must_use]
    pub fn to_bound(self) -> RelativeBound {
        RelativeBound::from(self)
    }

    /// Returns whether it is of the [`Finite`](RelativeStartBound::Finite)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, RelativeStartBound};
    /// let infinite_start_bound = RelativeStartBound::InfinitePast;
    /// let finite_start_bound =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound();
    ///
    /// assert!(finite_start_bound.is_finite());
    /// assert!(!infinite_start_bound.is_finite());
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the
    /// [`InfinitePast`](RelativeStartBound::InfinitePast) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, RelativeStartBound};
    /// let infinite_start_bound = RelativeStartBound::InfinitePast;
    /// let finite_start_bound =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound();
    ///
    /// assert!(infinite_start_bound.is_infinite_past());
    /// assert!(!finite_start_bound.is_infinite_past());
    /// ```
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfinitePast)
    }

    /// Returns the content of the [`Finite`](RelativeStartBound::Finite)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Finite`](RelativeStartBound::Finite) variant in an [`Option`]. If
    /// instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, RelativeStartBound};
    /// let infinite_start_bound = RelativeStartBound::InfinitePast;
    /// let finite_start_bound =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound();
    ///
    /// assert_eq!(
    ///     finite_start_bound.finite(),
    ///     Some(RelativeFiniteBoundPosition::new(
    ///         SignedDuration::from_hours(1)
    ///     )),
    /// );
    /// assert_eq!(infinite_start_bound.finite(), None);
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<RelativeFiniteStartBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfinitePast => None,
        }
    }

    /// Returns the opposite [`RelativeEndBound`]
    ///
    /// If the [`RelativeStartBound`] is of the
    /// [`InfinitePast`](RelativeStartBound::InfinitePast) variant, then the
    /// method returns [`None`]. Otherwise, if the [`RelativeStartBound`] is
    /// finite, then an [`RelativeEndBound`] is created with the same time,
    /// but the opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the last point in time before
    /// this bound begins.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, RelativeStartBound};
    /// #
    /// # #[derive(Debug)]
    /// # struct FiniteBoundPositionExpectedError;
    /// #
    /// # impl std::fmt::Display for FiniteBoundPositionExpectedError {
    /// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    /// #         write!(f, "Finite bound expected")
    /// #     }
    /// # }
    /// #
    /// # impl Error for FiniteBoundPositionExpectedError {}
    /// let start_second_part_my_shift =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_start_bound();
    /// let break_end_before_shift = start_second_part_my_shift
    ///     .opposite()
    ///     .ok_or(FiniteBoundPositionExpectedError)?;
    ///
    /// assert_eq!(
    ///     break_end_before_shift.finite(),
    ///     Some(RelativeFiniteBoundPosition::new_with_inclusivity(
    ///         SignedDuration::from_hours(3),
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_end_bound()),
            Self::InfinitePast => None,
        }
    }
}

impl HasBoundExtremality for RelativeStartBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::Start
    }
}

impl PartialOrd for RelativeStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::InfinitePast, Self::InfinitePast) => Ordering::Equal,
            (Self::InfinitePast, Self::Finite(_)) => Ordering::Less,
            (Self::Finite(_), Self::InfinitePast) => Ordering::Greater,
            (Self::Finite(lhs_finite_start), Self::Finite(rhs_finite_start)) => lhs_finite_start.cmp(rhs_finite_start),
        }
    }
}

impl BoundPartialEq for RelativeStartBound {
    fn bound_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl BoundEq for RelativeStartBound {}

impl BoundPartialEq<RelativeFiniteStartBound> for RelativeStartBound {
    fn bound_eq(&self, other: &RelativeFiniteStartBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeFiniteEndBound> for RelativeStartBound {
    fn bound_eq(&self, other: &RelativeFiniteEndBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeFiniteBound> for RelativeStartBound {
    fn bound_eq(&self, other: &RelativeFiniteBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeEndBound> for RelativeStartBound {
    fn bound_eq(&self, other: &RelativeEndBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeBound> for RelativeStartBound {
    fn bound_eq(&self, other: &RelativeBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialOrd for RelativeStartBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for RelativeStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match self.cmp(other) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(self.finite().zip(other.finite()).map(
                |(lhs_finite_start, rhs_finite_start)| {
                    BoundOverlapAmbiguity::BothStarts(
                        lhs_finite_start.inclusivity(),
                        rhs_finite_start.inclusivity(),
                    )
                },
            )),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundPartialOrd<RelativeFiniteStartBound> for RelativeStartBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteEndBound> for RelativeStartBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteBound> for RelativeStartBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<RelativeEndBound> for RelativeStartBound {
    fn bound_partial_cmp(&self, other: &RelativeEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<RelativeBound> for RelativeStartBound {
    fn bound_partial_cmp(&self, other: &RelativeBound) -> Option<BoundOrdering> {
        match other {
            RelativeBound::Start(start) => self.bound_partial_cmp(start),
            RelativeBound::End(end) => self.bound_partial_cmp(end),
        }
    }
}

impl From<RelativeFiniteStartBound> for RelativeStartBound {
    fn from(value: RelativeFiniteStartBound) -> Self {
        Self::Finite(value)
    }
}

impl From<RelativeFiniteBoundPosition> for RelativeStartBound {
    fn from(value: RelativeFiniteBoundPosition) -> Self {
        Self::Finite(RelativeFiniteStartBound::new(value))
    }
}

impl From<Option<SignedDuration>> for RelativeStartBound {
    fn from(value: Option<SignedDuration>) -> Self {
        match value {
            Some(offset) => Self::from(RelativeFiniteBoundPosition::from(offset)),
            None => Self::InfinitePast,
        }
    }
}

impl From<Option<(SignedDuration, BoundInclusivity)>> for RelativeStartBound {
    fn from(value: Option<(SignedDuration, BoundInclusivity)>) -> Self {
        match value {
            Some((offset, inclusivity)) => {
                Self::from(RelativeFiniteBoundPosition::new_with_inclusivity(offset, inclusivity))
            },
            None => Self::InfinitePast,
        }
    }
}

impl From<Bound<SignedDuration>> for RelativeStartBound {
    fn from(bound: Bound<SignedDuration>) -> Self {
        match bound {
            Bound::Included(offset) => {
                RelativeFiniteBoundPosition::new_with_inclusivity(offset, BoundInclusivity::Inclusive).to_start_bound()
            },
            Bound::Excluded(offset) => {
                RelativeFiniteBoundPosition::new_with_inclusivity(offset, BoundInclusivity::Exclusive).to_start_bound()
            },
            Bound::Unbounded => RelativeStartBound::InfinitePast,
        }
    }
}

/// Error that can occur when trying to convert an [`RelativeBound`] into an [`RelativeStartBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelativeStartBoundTryFromRelativeBoundError;

impl Display for RelativeStartBoundTryFromRelativeBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `RelativeBound` into an `RelativeStartBound`"
        )
    }
}

impl Error for RelativeStartBoundTryFromRelativeBoundError {}

impl TryFrom<RelativeBound> for RelativeStartBound {
    type Error = RelativeStartBoundTryFromRelativeBoundError;

    fn try_from(value: RelativeBound) -> Result<Self, Self::Error> {
        value.start().ok_or(RelativeStartBoundTryFromRelativeBoundError)
    }
}

// TODO: impl TryFrom for FiniteBound

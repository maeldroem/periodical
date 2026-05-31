//! Relative end bound
//!
//! Represents the end bound of a relative interval. It can either be finite, in
//! which case it will contain an [`RelativeFiniteBoundPosition`], or represent an open
//! end bound through the [`InfiniteFuture`](RelativeEndBound::InfiniteFuture)
//! variant.

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
    RelativeFiniteBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteEndBound,
    RelativeFiniteStartBound,
    RelativeStartBound,
};

/// A relative end interval bound
///
/// Represents the end bound of an interval, may it be infinitely in the future
/// or at a precise point in time, in which case it contains an
/// [`RelativeFiniteBoundPosition`].
///
/// Contrary to specific relative interval types, both [`RelativeStartBound`]
/// and [`RelativeEndBound`] use an offset, and not an offset for the start and
/// a length for the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelativeEndBound {
    Finite(RelativeFiniteEndBound),
    InfiniteFuture,
}

impl RelativeEndBound {
    /// Wraps the end bound of the corresponding [`RelativeBound`] variant
    #[must_use]
    pub fn to_bound(self) -> RelativeBound {
        RelativeBound::from(self)
    }

    /// Returns whether it is of the [`Finite`](RelativeEndBound::Finite)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBoundPosition};
    /// let infinite_end_bound = RelativeEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound();
    ///
    /// assert!(finite_end_bound.is_finite());
    /// assert!(!infinite_end_bound.is_finite());
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the
    /// [`InfiniteFuture`](RelativeEndBound::InfiniteFuture) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBoundPosition};
    /// let infinite_end_bound = RelativeEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound();
    ///
    /// assert!(infinite_end_bound.is_infinite_future());
    /// assert!(!finite_end_bound.is_infinite_future());
    /// ```
    #[must_use]
    pub fn is_infinite_future(&self) -> bool {
        matches!(self, Self::InfiniteFuture)
    }

    /// Returns the content of the [`Finite`](RelativeEndBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Finite`](RelativeEndBound::Finite) variant in an [`Option`]. If
    /// instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBoundPosition};
    /// let infinite_end_bound = RelativeEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound();
    ///
    /// assert_eq!(
    ///     finite_end_bound.finite(),
    ///     Some(RelativeFiniteBoundPosition::new(
    ///         SignedDuration::from_hours(1)
    ///     )),
    /// );
    /// assert_eq!(infinite_end_bound.finite(), None);
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<RelativeFiniteEndBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfiniteFuture => None,
        }
    }

    /// Returns the opposite [`RelativeStartBound`]
    ///
    /// If the [`RelativeEndBound`] is of the
    /// [`InfiniteFuture`](RelativeEndBound::InfiniteFuture) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`RelativeEndBound`] is finite, then a
    /// [`RelativeStartBound`] is created with the same time, but the
    /// opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the first point in time after
    /// this bound ends.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBoundPosition};
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
    /// let end_first_shift =
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound();
    /// let break_start = end_first_shift
    ///     .opposite()
    ///     .ok_or(FiniteBoundPositionExpectedError)?;
    ///
    /// assert_eq!(
    ///     break_start.finite(),
    ///     Some(RelativeFiniteBoundPosition::new_with_inclusivity(
    ///         SignedDuration::from_hours(1),
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_start_bound()),
            Self::InfiniteFuture => None,
        }
    }
}

impl HasBoundExtremality for RelativeEndBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::End
    }
}

impl PartialOrd for RelativeEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeEndBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::InfiniteFuture, Self::InfiniteFuture) => Ordering::Equal,
            (Self::InfiniteFuture, Self::Finite(_)) => Ordering::Greater,
            (Self::Finite(_), Self::InfiniteFuture) => Ordering::Less,
            (Self::Finite(lhs_finite_end), Self::Finite(rhs_finite_end)) => lhs_finite_end.cmp(rhs_finite_end),
        }
    }
}

impl BoundPartialEq for RelativeEndBound {
    fn bound_eq(&self, other: &Self) -> bool {
        self.finite().is_some_and(|finite_end| finite_end.bound_eq(other))
    }
}

impl BoundEq for RelativeEndBound {}

impl BoundPartialEq<RelativeFiniteStartBound> for RelativeEndBound {
    fn bound_eq(&self, other: &RelativeFiniteStartBound) -> bool {
        self.finite().is_some_and(|finite_end| finite_end.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeFiniteEndBound> for RelativeEndBound {
    fn bound_eq(&self, other: &RelativeFiniteEndBound) -> bool {
        self.finite().is_some_and(|finite_end| finite_end.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeFiniteBound> for RelativeEndBound {
    fn bound_eq(&self, other: &RelativeFiniteBound) -> bool {
        self.finite().is_some_and(|finite_end| finite_end.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeStartBound> for RelativeEndBound {
    fn bound_eq(&self, other: &RelativeStartBound) -> bool {
        self.finite().is_some_and(|finite_end| finite_end.bound_eq(other))
    }
}

impl BoundPartialEq<RelativeBound> for RelativeEndBound {
    fn bound_eq(&self, other: &RelativeBound) -> bool {
        self.finite().is_some_and(|finite_end| finite_end.bound_eq(other))
    }
}

impl BoundPartialOrd for RelativeEndBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for RelativeEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match self.cmp(other) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(self.finite().zip(other.finite()).map(
                |(lhs_finite_end, rhs_finite_end)| {
                    BoundOverlapAmbiguity::BothEnds(
                        lhs_finite_end.inclusivity(),
                        rhs_finite_end.inclusivity(),
                    )
                },
            )),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundPartialOrd<RelativeFiniteStartBound> for RelativeEndBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_end) => finite_end.bound_partial_cmp(other),
            Self::InfiniteFuture => Some(BoundOrdering::Greater),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteEndBound> for RelativeEndBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_end) => finite_end.bound_partial_cmp(other),
            Self::InfiniteFuture => Some(BoundOrdering::Greater),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteBound> for RelativeEndBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_end) => finite_end.bound_partial_cmp(other),
            Self::InfiniteFuture => Some(BoundOrdering::Greater),
        }
    }
}

impl BoundPartialOrd<RelativeStartBound> for RelativeEndBound {
    fn bound_partial_cmp(&self, other: &RelativeStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_end) => finite_end.bound_partial_cmp(other),
            Self::InfiniteFuture => Some(BoundOrdering::Greater),
        }
    }
}

impl BoundPartialOrd<RelativeBound> for RelativeEndBound {
    fn bound_partial_cmp(&self, other: &RelativeBound) -> Option<BoundOrdering> {
        match other {
            RelativeBound::Start(start) => self.bound_partial_cmp(start),
            RelativeBound::End(end) => self.bound_partial_cmp(end),
        }
    }
}

impl From<RelativeFiniteEndBound> for RelativeEndBound {
    fn from(value: RelativeFiniteEndBound) -> Self {
        Self::Finite(value)
    }
}

impl From<RelativeFiniteBoundPosition> for RelativeEndBound {
    fn from(value: RelativeFiniteBoundPosition) -> Self {
        Self::Finite(RelativeFiniteEndBound::new(value))
    }
}

impl From<Option<SignedDuration>> for RelativeEndBound {
    fn from(value: Option<SignedDuration>) -> Self {
        match value {
            Some(offset) => Self::from(RelativeFiniteBoundPosition::from(offset)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Option<(SignedDuration, BoundInclusivity)>> for RelativeEndBound {
    fn from(value: Option<(SignedDuration, BoundInclusivity)>) -> Self {
        match value {
            Some((offset, inclusivity)) => {
                Self::from(RelativeFiniteBoundPosition::new_with_inclusivity(offset, inclusivity))
            },
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Bound<SignedDuration>> for RelativeEndBound {
    fn from(bound: Bound<SignedDuration>) -> Self {
        match bound {
            Bound::Included(offset) => {
                RelativeFiniteBoundPosition::new_with_inclusivity(offset, BoundInclusivity::Inclusive).to_end_bound()
            },
            Bound::Excluded(offset) => {
                RelativeFiniteBoundPosition::new_with_inclusivity(offset, BoundInclusivity::Exclusive).to_end_bound()
            },
            Bound::Unbounded => RelativeEndBound::InfiniteFuture,
        }
    }
}

/// Error that can occur when trying to convert an [`RelativeBound`] into an [`RelativeEndBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelativeEndBoundTryFromRelativeBoundError;

impl Display for RelativeEndBoundTryFromRelativeBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `RelativeBound` into an `RelativeEndBound`"
        )
    }
}

impl Error for RelativeEndBoundTryFromRelativeBoundError {}

impl TryFrom<RelativeBound> for RelativeEndBound {
    type Error = RelativeEndBoundTryFromRelativeBoundError;

    fn try_from(value: RelativeBound) -> Result<Self, Self::Error> {
        value.end().ok_or(RelativeEndBoundTryFromRelativeBoundError)
    }
}

// TODO: impl TryFrom for FiniteBound

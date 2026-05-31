//! Absolute start bound
//!
//! Represents the start bound of an absolute interval. It can either be finite,
//! in which case it will contain an [`AbsoluteFiniteBoundPosition`], or represent an
//! open start bound through
//! the [`InfinitePast`](AbsoluteStartBound::InfinitePast) variant.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteFiniteEndBound,
    AbsoluteFiniteStartBound,
};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality, HasBoundInclusivity};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundOverlapAmbiguity, BoundPartialEq, BoundPartialOrd};

/// An absolute start bound
///
/// Represents the start bound of an interval, may it be infinitely in the past
/// or at a precise point in time, in which case it contains an
/// [`AbsoluteFiniteStartBound`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsoluteStartBound {
    Finite(AbsoluteFiniteStartBound),
    InfinitePast,
}

impl AbsoluteStartBound {
    /// Wraps the start bound in the corresponding [`AbsoluteBound`] variant
    #[must_use]
    pub fn to_bound(self) -> AbsoluteBound {
        AbsoluteBound::from(self)
    }

    /// Returns whether it is of the [`Finite`](AbsoluteStartBound::Finite)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBoundPosition, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_start_bound = AbsoluteFiniteBoundPosition::new(time).to_start_bound();
    ///
    /// assert!(finite_start_bound.is_finite());
    /// assert!(!infinite_start_bound.is_finite());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the
    /// [`InfinitePast`](AbsoluteStartBound::InfinitePast) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBoundPosition, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_start_bound = AbsoluteFiniteBoundPosition::new(time).to_start_bound();
    ///
    /// assert!(infinite_start_bound.is_infinite_past());
    /// assert!(!finite_start_bound.is_infinite_past());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfinitePast)
    }

    /// Returns the content of the [`Finite`](AbsoluteStartBound::Finite)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Finite`](AbsoluteStartBound::Finite) variant in an [`Option`]. If
    /// instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBoundPosition, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_start_bound = AbsoluteFiniteBoundPosition::new(time).to_start_bound();
    ///
    /// assert_eq!(
    ///     finite_start_bound.finite(),
    ///     Some(AbsoluteFiniteBoundPosition::new(time))
    /// );
    /// assert_eq!(infinite_start_bound.finite(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<AbsoluteFiniteStartBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfinitePast => None,
        }
    }

    /// Returns the opposite [`AbsoluteEndBound`]
    ///
    /// If the [`AbsoluteStartBound`] is of the
    /// [`InfinitePast`](AbsoluteStartBound::InfinitePast) variant, then the
    /// method returns [`None`]. Otherwise, if the [`AbsoluteStartBound`] is
    /// finite, then an [`AbsoluteEndBound`] is created with the same time,
    /// but the opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the last point in time before
    /// this bound begins.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBoundPosition, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
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
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start_second_part_my_shift = AbsoluteFiniteBoundPosition::new(time).to_start_bound();
    /// let break_end_before_shift = start_second_part_my_shift
    ///     .opposite()
    ///     .ok_or(FiniteBoundPositionExpectedError)?;
    ///
    /// assert_eq!(
    ///     break_end_before_shift.finite(),
    ///     Some(AbsoluteFiniteBoundPosition::new_with_inclusivity(
    ///         time,
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_end_bound()),
            Self::InfinitePast => None,
        }
    }
}

impl HasBoundExtremality for AbsoluteStartBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::Start
    }
}

impl PartialOrd for AbsoluteStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::InfinitePast, Self::InfinitePast) => Ordering::Equal,
            (Self::InfinitePast, Self::Finite(_)) => Ordering::Less,
            (Self::Finite(_), Self::InfinitePast) => Ordering::Greater,
            (Self::Finite(lhs_finite_start), Self::Finite(rhs_finite_start)) => lhs_finite_start.cmp(rhs_finite_start),
        }
    }
}

impl BoundPartialEq for AbsoluteStartBound {
    fn bound_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl BoundEq for AbsoluteStartBound {}

impl BoundPartialEq<AbsoluteFiniteStartBound> for AbsoluteStartBound {
    fn bound_eq(&self, other: &AbsoluteFiniteStartBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<AbsoluteFiniteEndBound> for AbsoluteStartBound {
    fn bound_eq(&self, other: &AbsoluteFiniteEndBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<AbsoluteFiniteBound> for AbsoluteStartBound {
    fn bound_eq(&self, other: &AbsoluteFiniteBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<AbsoluteEndBound> for AbsoluteStartBound {
    fn bound_eq(&self, other: &AbsoluteEndBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialEq<AbsoluteBound> for AbsoluteStartBound {
    fn bound_eq(&self, other: &AbsoluteBound) -> bool {
        self.finite().is_some_and(|finite_start| finite_start.bound_eq(other))
    }
}

impl BoundPartialOrd for AbsoluteStartBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for AbsoluteStartBound {
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

impl BoundPartialOrd<AbsoluteFiniteStartBound> for AbsoluteStartBound {
    fn bound_partial_cmp(&self, other: &AbsoluteFiniteStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<AbsoluteFiniteEndBound> for AbsoluteStartBound {
    fn bound_partial_cmp(&self, other: &AbsoluteFiniteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<AbsoluteFiniteBound> for AbsoluteStartBound {
    fn bound_partial_cmp(&self, other: &AbsoluteFiniteBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<AbsoluteEndBound> for AbsoluteStartBound {
    fn bound_partial_cmp(&self, other: &AbsoluteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Finite(finite_start) => finite_start.bound_partial_cmp(other),
            Self::InfinitePast => Some(BoundOrdering::Less),
        }
    }
}

impl BoundPartialOrd<AbsoluteBound> for AbsoluteStartBound {
    fn bound_partial_cmp(&self, other: &AbsoluteBound) -> Option<BoundOrdering> {
        match other {
            AbsoluteBound::Start(start) => self.bound_partial_cmp(start),
            AbsoluteBound::End(end) => self.bound_partial_cmp(end),
        }
    }
}

impl From<AbsoluteFiniteStartBound> for AbsoluteStartBound {
    fn from(value: AbsoluteFiniteStartBound) -> Self {
        Self::Finite(value)
    }
}

impl From<AbsoluteFiniteBoundPosition> for AbsoluteStartBound {
    fn from(value: AbsoluteFiniteBoundPosition) -> Self {
        Self::Finite(AbsoluteFiniteStartBound::new(value))
    }
}

impl From<Option<Timestamp>> for AbsoluteStartBound {
    fn from(value: Option<Timestamp>) -> Self {
        match value {
            Some(timestamp) => Self::from(AbsoluteFiniteBoundPosition::from(timestamp)),
            None => Self::InfinitePast,
        }
    }
}

impl From<Option<(Timestamp, BoundInclusivity)>> for AbsoluteStartBound {
    fn from(value: Option<(Timestamp, BoundInclusivity)>) -> Self {
        match value {
            Some((timestamp, inclusivity)) => Self::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                timestamp,
                inclusivity,
            )),
            None => Self::InfinitePast,
        }
    }
}

impl From<Bound<Timestamp>> for AbsoluteStartBound {
    fn from(bound: Bound<Timestamp>) -> Self {
        match bound {
            Bound::Included(time) => {
                AbsoluteFiniteBoundPosition::new_with_inclusivity(time, BoundInclusivity::Inclusive).to_start_bound()
            },
            Bound::Excluded(time) => {
                AbsoluteFiniteBoundPosition::new_with_inclusivity(time, BoundInclusivity::Exclusive).to_start_bound()
            },
            Bound::Unbounded => AbsoluteStartBound::InfinitePast,
        }
    }
}

/// Error that can occur when trying to convert an [`AbsoluteBound`] into an [`AbsoluteStartBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsoluteStartBoundTryFromAbsoluteBoundError;

impl Display for AbsoluteStartBoundTryFromAbsoluteBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `AbsoluteBound` into an `AbsoluteStartBound`"
        )
    }
}

impl Error for AbsoluteStartBoundTryFromAbsoluteBoundError {}

impl TryFrom<AbsoluteBound> for AbsoluteStartBound {
    type Error = AbsoluteStartBoundTryFromAbsoluteBoundError;

    fn try_from(value: AbsoluteBound) -> Result<Self, Self::Error> {
        value.start().ok_or(AbsoluteStartBoundTryFromAbsoluteBoundError)
    }
}

// TODO: impl TryFrom for FiniteBound

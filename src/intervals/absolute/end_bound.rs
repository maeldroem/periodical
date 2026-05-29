//! Absolute end bound
//!
//! Represents the end bound of an absolute interval. It can either be finite,
//! in which case it will contain an [`AbsoluteFiniteBoundPosition`], or represent an
//! open end bound through
//! the [`InfiniteFuture`](AbsoluteEndBound::InfiniteFuture) variant.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality, HasBoundInclusivity};
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
    DisambiguatedBoundOverlap,
};

/// An absolute end bound
///
/// Represents the end bound of an interval, may it be infinitely in the future
/// or at a precise point in time, in which case it contains an
/// [`AbsoluteFiniteBoundPosition`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsoluteEndBound {
    Finite(AbsoluteFiniteBoundPosition),
    InfiniteFuture,
}

impl AbsoluteEndBound {
    /// Wraps the end bound in the corresponding [`AbsoluteBound`] variant
    #[must_use]
    pub fn to_bound(self) -> AbsoluteBound {
        AbsoluteBound::from(self)
    }

    /// Returns whether it is of the [`Finite`](AbsoluteEndBound::Finite)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBoundPosition};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_end_bound = AbsoluteFiniteBoundPosition::new(time).to_end_bound();
    ///
    /// assert!(finite_end_bound.is_finite());
    /// assert!(!infinite_end_bound.is_finite());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the
    /// [`InfiniteFuture`](AbsoluteEndBound::InfiniteFuture) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBoundPosition};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_end_bound = AbsoluteFiniteBoundPosition::new(time).to_end_bound();
    ///
    /// assert!(infinite_end_bound.is_infinite_future());
    /// assert!(!finite_end_bound.is_infinite_future());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_infinite_future(&self) -> bool {
        matches!(self, Self::InfiniteFuture)
    }

    /// Returns the content of the [`Finite`](AbsoluteEndBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Finite`](AbsoluteEndBound::Finite) variant in an [`Option`]. If
    /// instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBoundPosition};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_end_bound = AbsoluteFiniteBoundPosition::new(time).to_end_bound();
    ///
    /// assert_eq!(
    ///     finite_end_bound.finite(),
    ///     Some(AbsoluteFiniteBoundPosition::new(time))
    /// );
    /// assert_eq!(infinite_end_bound.finite(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<AbsoluteFiniteBoundPosition> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfiniteFuture => None,
        }
    }

    /// Returns the opposite [`AbsoluteStartBound`]
    ///
    /// If the [`AbsoluteEndBound`] is of the
    /// [`InfiniteFuture`](AbsoluteEndBound::InfiniteFuture) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`AbsoluteEndBound`] is finite, then an
    /// [`AbsoluteStartBound`] is created with the same time, but the
    /// opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the first point in time after
    /// this bound ends.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBoundPosition};
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
    /// let end_first_shift = AbsoluteFiniteBoundPosition::new(time).to_end_bound();
    /// let break_start = end_first_shift.opposite().ok_or(FiniteBoundPositionExpectedError)?;
    ///
    /// assert_eq!(
    ///     break_start.finite(),
    ///     Some(AbsoluteFiniteBoundPosition::new_with_inclusivity(
    ///         time,
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Finite(finite) => Some(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(finite.time(), finite.inclusivity().opposite())
                    .to_start_bound(),
            ),
            Self::InfiniteFuture => None,
        }
    }
}

impl HasBoundExtremality for AbsoluteEndBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::End
    }
}

impl PartialOrd for AbsoluteEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteEndBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::InfiniteFuture) => Ordering::Equal,
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::Finite(_)) => Ordering::Greater,
            (AbsoluteEndBound::Finite(_), AbsoluteEndBound::InfiniteFuture) => Ordering::Less,
            (
                AbsoluteEndBound::Finite(AbsoluteFiniteBoundPosition {
                    time: time_og,
                    inclusivity: inclusivity_og,
                }),
                AbsoluteEndBound::Finite(AbsoluteFiniteBoundPosition {
                    time: time_other,
                    inclusivity: inclusivity_other,
                }),
            ) => {
                let time_cmp = time_og.cmp(time_other);

                if matches!(time_cmp, Ordering::Less | Ordering::Greater) {
                    return time_cmp;
                }

                match (inclusivity_og, inclusivity_other) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Greater,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Less,
                }
            },
        }
    }
}

impl PartialEq<AbsoluteStartBound> for AbsoluteEndBound {
    fn eq(&self, other: &AbsoluteStartBound) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<AbsoluteStartBound> for AbsoluteEndBound {
    fn partial_cmp(&self, other: &AbsoluteStartBound) -> Option<Ordering> {
        match (self, other) {
            (AbsoluteEndBound::InfiniteFuture, _) | (_, AbsoluteStartBound::InfinitePast) => Some(Ordering::Greater),
            (
                AbsoluteEndBound::Finite(AbsoluteFiniteBoundPosition {
                    time: end_time,
                    inclusivity: end_inclusivity,
                }),
                AbsoluteStartBound::Finite(AbsoluteFiniteBoundPosition {
                    time: start_time,
                    inclusivity: start_inclusivity,
                }),
            ) => match end_time.cmp(start_time) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Equal => {
                    let disambiguated_bound_overlap =
                        BoundOverlapAmbiguity::EndStart(*end_inclusivity, *start_inclusivity)
                            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict);

                    match disambiguated_bound_overlap {
                        DisambiguatedBoundOverlap::Before => Some(Ordering::Greater), // Unreachable, safe fallback
                        DisambiguatedBoundOverlap::Equal => Some(Ordering::Equal),
                        DisambiguatedBoundOverlap::After => Some(Ordering::Less),
                    }
                },
                Ordering::Greater => Some(Ordering::Greater),
            },
        }
    }
}

impl From<AbsoluteFiniteBoundPosition> for AbsoluteEndBound {
    fn from(value: AbsoluteFiniteBoundPosition) -> Self {
        Self::Finite(value)
    }
}

impl From<Option<Timestamp>> for AbsoluteEndBound {
    fn from(value: Option<Timestamp>) -> Self {
        match value {
            Some(timestamp) => Self::Finite(AbsoluteFiniteBoundPosition::from(timestamp)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Option<(Timestamp, BoundInclusivity)>> for AbsoluteEndBound {
    fn from(value: Option<(Timestamp, BoundInclusivity)>) -> Self {
        match value {
            Some((timestamp, inclusivity)) => Self::Finite(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                timestamp,
                inclusivity,
            )),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Bound<Timestamp>> for AbsoluteEndBound {
    fn from(bound: Bound<Timestamp>) -> Self {
        match bound {
            Bound::Included(time) => {
                AbsoluteFiniteBoundPosition::new_with_inclusivity(time, BoundInclusivity::Inclusive).to_end_bound()
            },
            Bound::Excluded(time) => {
                AbsoluteFiniteBoundPosition::new_with_inclusivity(time, BoundInclusivity::Exclusive).to_end_bound()
            },
            Bound::Unbounded => AbsoluteEndBound::InfiniteFuture,
        }
    }
}

/// Error that can occur when trying to convert an [`AbsoluteBound`] into an [`AbsoluteEndBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsoluteEndBoundTryFromAbsoluteBoundError;

impl Display for AbsoluteEndBoundTryFromAbsoluteBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `AbsoluteBound` into an `AbsoluteEndBound`"
        )
    }
}

impl Error for AbsoluteEndBoundTryFromAbsoluteBoundError {}

impl TryFrom<AbsoluteBound> for AbsoluteEndBound {
    type Error = AbsoluteEndBoundTryFromAbsoluteBoundError;

    fn try_from(value: AbsoluteBound) -> Result<Self, Self::Error> {
        value.end().ok_or(AbsoluteEndBoundTryFromAbsoluteBoundError)
    }
}

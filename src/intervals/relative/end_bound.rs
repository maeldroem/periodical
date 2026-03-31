//! Relative end bound
//!
//! Represents the end bound of a relative interval. It can either be finite, in
//! which case it will contain an [`RelativeFiniteBound`], or represent an open
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

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
    DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{RelativeBound, RelativeFiniteBound, RelativeStartBound};

/// A relative end interval bound
///
/// Represents the end bound of an interval, may it be infinitely in the future
/// or at a precise point in time, in which case it contains an
/// [`RelativeFiniteBound`].
///
/// Contrary to specific relative interval types, both [`RelativeStartBound`]
/// and [`RelativeEndBound`] use an offset, and not an offset for the start and
/// a length for the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelativeEndBound {
    Finite(RelativeFiniteBound),
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
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound};
    /// let infinite_end_bound = RelativeEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
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
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound};
    /// let infinite_end_bound = RelativeEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
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
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound};
    /// let infinite_end_bound = RelativeEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
    ///
    /// assert_eq!(
    ///     finite_end_bound.finite(),
    ///     Some(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
    /// );
    /// assert_eq!(infinite_end_bound.finite(), None);
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<RelativeFiniteBound> {
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
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound};
    /// #
    /// # #[derive(Debug)]
    /// # struct FiniteBoundExpectedError;
    /// #
    /// # impl std::fmt::Display for FiniteBoundExpectedError {
    /// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    /// #         write!(f, "Finite bound expected")
    /// #     }
    /// # }
    /// #
    /// # impl Error for FiniteBoundExpectedError {}
    /// let end_first_shift =
    ///     RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
    /// let break_start = end_first_shift.opposite().ok_or(FiniteBoundExpectedError)?;
    ///
    /// assert_eq!(
    ///     break_start.finite(),
    ///     Some(RelativeFiniteBound::new_with_inclusivity(
    ///         SignedDuration::from_hours(1),
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Finite(finite) => Some(
                RelativeFiniteBound::new_with_inclusivity(finite.offset(), finite.inclusivity().opposite())
                    .to_start_bound(),
            ),
            Self::InfiniteFuture => None,
        }
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
            (RelativeEndBound::InfiniteFuture, RelativeEndBound::InfiniteFuture) => Ordering::Equal,
            (RelativeEndBound::InfiniteFuture, RelativeEndBound::Finite(_)) => Ordering::Greater,
            (RelativeEndBound::Finite(_), RelativeEndBound::InfiniteFuture) => Ordering::Less,
            (
                RelativeEndBound::Finite(RelativeFiniteBound {
                    offset: offset_og,
                    inclusivity: inclusivity_og,
                }),
                RelativeEndBound::Finite(RelativeFiniteBound {
                    offset: offset_other,
                    inclusivity: inclusivity_other,
                }),
            ) => {
                let offset_cmp = offset_og.cmp(offset_other);

                if matches!(offset_cmp, Ordering::Less | Ordering::Greater) {
                    return offset_cmp;
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

impl PartialEq<RelativeStartBound> for RelativeEndBound {
    fn eq(&self, other: &RelativeStartBound) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<RelativeStartBound> for RelativeEndBound {
    fn partial_cmp(&self, other: &RelativeStartBound) -> Option<Ordering> {
        match (self, other) {
            (RelativeEndBound::InfiniteFuture, _) | (_, RelativeStartBound::InfinitePast) => Some(Ordering::Greater),
            (
                RelativeEndBound::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                }),
                RelativeStartBound::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                }),
            ) => match end_offset.cmp(start_offset) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Equal => {
                    let disambiguated_bound_overlap =
                        BoundOverlapAmbiguity::EndStart(*end_inclusivity, *start_inclusivity)
                            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict);

                    match disambiguated_bound_overlap {
                        DisambiguatedBoundOverlap::Before => Some(Ordering::Greater),
                        DisambiguatedBoundOverlap::Equal => Some(Ordering::Equal),
                        DisambiguatedBoundOverlap::After => Some(Ordering::Less),
                    }
                },
                Ordering::Greater => Some(Ordering::Greater),
            },
        }
    }
}

impl From<RelativeFiniteBound> for RelativeEndBound {
    fn from(value: RelativeFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Option<SignedDuration>> for RelativeEndBound {
    fn from(value: Option<SignedDuration>) -> Self {
        match value {
            Some(offset) => Self::Finite(RelativeFiniteBound::from(offset)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Option<(SignedDuration, BoundInclusivity)>> for RelativeEndBound {
    fn from(value: Option<(SignedDuration, BoundInclusivity)>) -> Self {
        match value {
            Some((offset, inclusivity)) => Self::Finite(RelativeFiniteBound::new_with_inclusivity(offset, inclusivity)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Bound<SignedDuration>> for RelativeEndBound {
    fn from(bound: Bound<SignedDuration>) -> Self {
        match bound {
            Bound::Included(offset) => RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(offset) => RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Exclusive,
            )),
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

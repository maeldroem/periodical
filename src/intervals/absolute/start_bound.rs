//! Absolute start bound
//!
//! Represents the start bound of an absolute interval. It can either be finite,
//! in which case it will contain an [`AbsoluteFiniteBound`], or represent an
//! open start bound through
//! the [`InfinitePast`](AbsoluteStartBound::InfinitePast) variant.

use std::cmp::Ordering;
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
    DisambiguatedBoundOverlap,
};

/// An absolute start bound
///
/// Represents the start bound of an interval, may it be infinitely in the past
/// or at a precise point in time, in which case it contains an
/// [`AbsoluteFiniteBound`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsoluteStartBound {
    Finite(AbsoluteFiniteBound),
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
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_start_bound = AbsoluteFiniteBound::new(time).to_start_bound();
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
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_start_bound = AbsoluteFiniteBound::new(time).to_start_bound();
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
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_start_bound = AbsoluteFiniteBound::new(time).to_start_bound();
    ///
    /// assert_eq!(
    ///     finite_start_bound.finite(),
    ///     Some(AbsoluteFiniteBound::new(time))
    /// );
    /// assert_eq!(infinite_start_bound.finite(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<AbsoluteFiniteBound> {
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
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
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
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start_second_part_my_shift = AbsoluteFiniteBound::new(time).to_start_bound();
    /// let break_end_before_shift = start_second_part_my_shift
    ///     .opposite()
    ///     .ok_or(FiniteBoundExpectedError)?;
    ///
    /// assert_eq!(
    ///     break_end_before_shift.finite(),
    ///     Some(AbsoluteFiniteBound::new_with_inclusivity(
    ///         time,
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Finite(finite) => Some(
                AbsoluteFiniteBound::new_with_inclusivity(finite.time(), finite.inclusivity().opposite())
                    .to_end_bound(),
            ),
            Self::InfinitePast => None,
        }
    }
}

impl PartialEq<AbsoluteEndBound> for AbsoluteStartBound {
    fn eq(&self, other: &AbsoluteEndBound) -> bool {
        if let AbsoluteStartBound::Finite(AbsoluteFiniteBound {
            time: start_time,
            inclusivity: start_inclusivity,
        }) = self
            && let AbsoluteEndBound::Finite(AbsoluteFiniteBound {
                time: end_time,
                inclusivity: end_inclusivity,
            }) = other
        {
            // If the times are equal, anything other than double inclusive bounds is
            // invalid
            start_time == end_time
                && *start_inclusivity == BoundInclusivity::Inclusive
                && *end_inclusivity == BoundInclusivity::Inclusive
        } else {
            false
        }
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
            (AbsoluteStartBound::InfinitePast, AbsoluteStartBound::InfinitePast) => Ordering::Equal,
            (AbsoluteStartBound::InfinitePast, AbsoluteStartBound::Finite(_)) => Ordering::Less,
            (AbsoluteStartBound::Finite(_), AbsoluteStartBound::InfinitePast) => Ordering::Greater,
            (
                AbsoluteStartBound::Finite(AbsoluteFiniteBound {
                    time: time_og,
                    inclusivity: inclusivity_og,
                }),
                AbsoluteStartBound::Finite(AbsoluteFiniteBound {
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
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Less,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Greater,
                }
            },
        }
    }
}

impl PartialOrd<AbsoluteEndBound> for AbsoluteStartBound {
    fn partial_cmp(&self, other: &AbsoluteEndBound) -> Option<Ordering> {
        match (self, other) {
            (AbsoluteStartBound::InfinitePast, _) | (_, AbsoluteEndBound::InfiniteFuture) => Some(Ordering::Less),
            (
                AbsoluteStartBound::Finite(AbsoluteFiniteBound {
                    time: start_time,
                    inclusivity: start_inclusivity,
                }),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                }),
            ) => match start_time.cmp(end_time) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Equal => {
                    let disambiguated_bound_overlap =
                        BoundOverlapAmbiguity::StartEnd(*start_inclusivity, *end_inclusivity)
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

impl From<AbsoluteFiniteBound> for AbsoluteStartBound {
    fn from(value: AbsoluteFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Bound<Timestamp>> for AbsoluteStartBound {
    fn from(bound: Bound<Timestamp>) -> Self {
        match bound {
            Bound::Included(time) => AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(time) => AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => AbsoluteStartBound::InfinitePast,
        }
    }
}

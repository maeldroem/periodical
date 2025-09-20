//! Absolute intervals
//!
//! Absolute intervals are pinned to time, that is to say they have a start datetime and an end datetime.
//!
//! The most common absolute interval objects you will encounter are
//!
//! - [`AbsoluteBounds`]
//! - [`EmptiableAbsoluteBounds`]
//! - [`BoundedAbsoluteInterval`]
//! - [`HalfBoundedAbsoluteInterval`]

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::{Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use chrono::{DateTime, Duration, Utc};

use crate::intervals::meta::Interval;

use super::meta::{BoundInclusivity, Duration as IntervalDuration, OpeningDirection, Openness, Relativity};
use super::prelude::*;
use super::special::{EmptyInterval, UnboundedInterval};

/// An absolute finite bound
///
/// Contains a time and an ambiguous [`BoundInclusivity`]: if it is [`Exclusive`](BoundInclusivity::Exclusive),
/// then we additionally need the _source_ (whether it acts as the start or end of an interval) in order to know
/// what this bound truly encompasses.
///
/// This is why when comparing finite bounds, only its position (for absolute bounds, its time) is used.
///
/// # Examples
///
/// ## Basic use
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::AbsoluteFiniteBound;
/// let finite_bound = AbsoluteFiniteBound::new("2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?);
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
///
/// ## Creating an [`AbsoluteFiniteBound`] with an explicit [`BoundInclusivity`]
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::AbsoluteFiniteBound;
/// # use periodical::intervals::meta::BoundInclusivity;
/// let finite_bound = AbsoluteFiniteBound::new_with_inclusivity(
///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     BoundInclusivity::Exclusive,
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub struct AbsoluteFiniteBound {
    time: DateTime<Utc>,
    inclusivity: BoundInclusivity,
}

impl AbsoluteFiniteBound {
    /// Creates a new [`AbsoluteFiniteBound`] using the given time
    ///
    /// This creates a finite bound using the [default `BoundInclusivity`](BoundInclusivity::default).
    #[must_use]
    pub fn new(time: DateTime<Utc>) -> Self {
        Self::new_with_inclusivity(time, BoundInclusivity::default())
    }

    /// Creates a new [`AbsoluteFiniteBound`] using the given time and [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_inclusivity(time: DateTime<Utc>, inclusivity: BoundInclusivity) -> Self {
        AbsoluteFiniteBound { time, inclusivity }
    }

    /// Returns the time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let finite_bound = AbsoluteFiniteBound::new(time);
    ///
    /// assert_eq!(finite_bound.time(), time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn time(&self) -> DateTime<Utc> {
        self.time
    }

    /// Sets the time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let new_time = "2025-01-02 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut finite_bound = AbsoluteFiniteBound::new(time);
    /// finite_bound.set_time(new_time);
    ///
    /// assert_eq!(finite_bound.time(), new_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_time(&mut self, new_time: DateTime<Utc>) {
        self.time = new_time;
    }

    /// Sets the bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::prelude::*;
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut finite_bound = AbsoluteFiniteBound::new(time);
    /// finite_bound.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(finite_bound.inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.inclusivity = new_inclusivity;
    }
}

impl HasBoundInclusivity for AbsoluteFiniteBound {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl PartialOrd for AbsoluteFiniteBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteFiniteBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time.cmp(&other.time)
    }
}

impl Display for AbsoluteFiniteBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Absolute finite bound at {} ({})", self.time, self.inclusivity)
    }
}

impl From<DateTime<Utc>> for AbsoluteFiniteBound {
    fn from(value: DateTime<Utc>) -> Self {
        AbsoluteFiniteBound::new(value)
    }
}

impl From<(DateTime<Utc>, BoundInclusivity)> for AbsoluteFiniteBound {
    fn from((time, inclusivity): (DateTime<Utc>, BoundInclusivity)) -> Self {
        AbsoluteFiniteBound::new_with_inclusivity(time, inclusivity)
    }
}

/// Conversion from the tuple `(DateTime<Utc>, bool)` to [`AbsoluteFiniteBound`]
///
/// Interprets the boolean as _is it inclusive?_
impl From<(DateTime<Utc>, bool)> for AbsoluteFiniteBound {
    fn from((time, is_inclusive): (DateTime<Utc>, bool)) -> Self {
        AbsoluteFiniteBound::new_with_inclusivity(time, BoundInclusivity::from(is_inclusive))
    }
}

/// Errors that can occur when trying to convert a [`Bound<DateTime<Utc>>`] into an [`AbsoluteFiniteBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteFiniteBoundFromBoundError {
    /// The given bound was of the [`Unbounded`](Bound::Unbounded) variant
    IsUnbounded,
}

impl Display for AbsoluteFiniteBoundFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IsUnbounded => {
                write!(
                    f,
                    "The given bound was of the `Unbounded` variant, \
                    and therefore could not be converted to an `AbsoluteFiniteBound`"
                )
            },
        }
    }
}

impl Error for AbsoluteFiniteBoundFromBoundError {}

impl TryFrom<Bound<DateTime<Utc>>> for AbsoluteFiniteBound {
    type Error = AbsoluteFiniteBoundFromBoundError;

    fn try_from(value: Bound<DateTime<Utc>>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(time) => Ok(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(time) => Ok(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => Err(AbsoluteFiniteBoundFromBoundError::IsUnbounded),
        }
    }
}

/// An absolute start bound
///
/// Represents the start bound of an interval, may it be infinitely in the past or at a precise point in time,
/// in which case it contains an [`AbsoluteFiniteBound`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum AbsoluteStartBound {
    Finite(AbsoluteFiniteBound),
    InfinitePast,
}

impl AbsoluteStartBound {
    /// Returns whether it is of the [`Finite`](AbsoluteStartBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let finite_start_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert!(finite_start_bound.is_finite());
    /// assert!(!infinite_start_bound.is_finite());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfinitePast`](AbsoluteStartBound::InfinitePast) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let finite_start_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert!(infinite_start_bound.is_infinite_past());
    /// assert!(!finite_start_bound.is_infinite_past());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfinitePast)
    }

    /// Returns the content of the [`Finite`](AbsoluteStartBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](AbsoluteStartBound::Finite) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// let infinite_start_bound = AbsoluteStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let finite_start_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert_eq!(finite_start_bound.finite(), Some(AbsoluteFiniteBound::new(time)));
    /// assert_eq!(infinite_start_bound.finite(), None);
    /// # Ok::<(), chrono::format::ParseError>(())
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
    /// If the [`AbsoluteStartBound`] is of the [`InfinitePast`](AbsoluteStartBound::InfinitePast) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`AbsoluteStartBound`] is finite, then an [`AbsoluteEndBound`] is created
    /// with the same time, but the opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the last point in time before this bound begins.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start_second_part_my_shift = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(time));
    /// let break_end_before_shift = start_second_part_my_shift
    ///     .opposite()
    ///     .expect("provided a finite bound");
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Finite(finite) => Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                finite.time(),
                finite.inclusivity().opposite(),
            ))),
            Self::InfinitePast => None,
        }
    }
}

impl PartialEq<AbsoluteEndBound> for AbsoluteStartBound {
    fn eq(&self, other: &AbsoluteEndBound) -> bool {
        let AbsoluteStartBound::Finite(AbsoluteFiniteBound {
            time: start_time,
            inclusivity: start_inclusivity,
        }) = self
        else {
            return false;
        };
        let AbsoluteEndBound::Finite(AbsoluteFiniteBound {
            time: end_time,
            inclusivity: end_inclusivity,
        }) = other
        else {
            return false;
        };

        // If the times are equal, anything other than double inclusive bounds is invalid
        start_time == end_time
            && *start_inclusivity == BoundInclusivity::Inclusive
            && *end_inclusivity == BoundInclusivity::Inclusive
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

impl Display for AbsoluteStartBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());
        result = result.and(write!(f, "Absolute start: "));

        match self {
            Self::Finite(AbsoluteFiniteBound { time, inclusivity }) => {
                result = result.and(write!(f, "{time} ({inclusivity})"));
            },
            Self::InfinitePast => {
                result = result.and(write!(f, "Infinite past"));
            },
        }

        result
    }
}

impl From<AbsoluteFiniteBound> for AbsoluteStartBound {
    fn from(value: AbsoluteFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Bound<DateTime<Utc>>> for AbsoluteStartBound {
    fn from(bound: Bound<DateTime<Utc>>) -> Self {
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

/// An absolute end bound
///
/// Represents the end bound of an interval, may it be infinitely in the future or at a precise point in time,
/// in which case it contains an [`AbsoluteFiniteBound`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum AbsoluteEndBound {
    Finite(AbsoluteFiniteBound),
    InfiniteFuture,
}

impl AbsoluteEndBound {
    /// Returns whether it is of the [`Finite`](AbsoluteEndBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let finite_end_bound = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert!(finite_end_bound.is_finite());
    /// assert!(!infinite_end_bound.is_finite());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfiniteFuture`](AbsoluteEndBound::InfiniteFuture) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let finite_end_bound = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert!(infinite_end_bound.is_infinite_future());
    /// assert!(!finite_end_bound.is_infinite_future());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_infinite_future(&self) -> bool {
        matches!(self, Self::InfiniteFuture)
    }

    /// Returns the content of the [`Finite`](AbsoluteEndBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](AbsoluteEndBound::Finite) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let finite_end_bound = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert_eq!(finite_end_bound.finite(), Some(AbsoluteFiniteBound::new(time)));
    /// assert_eq!(infinite_end_bound.finite(), None);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<AbsoluteFiniteBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfiniteFuture => None,
        }
    }

    /// Returns the opposite [`AbsoluteStartBound`]
    ///
    /// If the [`AbsoluteEndBound`] is of the [`InfiniteFuture`](AbsoluteEndBound::InfiniteFuture) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`AbsoluteEndBound`] is finite, then an [`AbsoluteStartBound`] is created
    /// with the same time, but the opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the first point in time after this bound ends.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let end_first_shift = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    /// let break_start = end_first_shift
    ///     .opposite()
    ///     .expect("provided a finite bound");
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Finite(finite) => Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                finite.time(),
                finite.inclusivity().opposite(),
            ))),
            Self::InfiniteFuture => None,
        }
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
                AbsoluteEndBound::Finite(AbsoluteFiniteBound {
                    time: time_og,
                    inclusivity: inclusivity_og,
                }),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound {
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
                AbsoluteEndBound::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                }),
                AbsoluteStartBound::Finite(AbsoluteFiniteBound {
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

impl Display for AbsoluteEndBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());
        result = result.and(write!(f, "Absolute end: "));

        match self {
            Self::Finite(AbsoluteFiniteBound { time, inclusivity }) => {
                result = result.and(write!(f, "{time} ({inclusivity})"));
            },
            Self::InfiniteFuture => {
                result = result.and(write!(f, "Infinite future"));
            },
        }

        result
    }
}

impl From<AbsoluteFiniteBound> for AbsoluteEndBound {
    fn from(value: AbsoluteFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Bound<DateTime<Utc>>> for AbsoluteEndBound {
    fn from(bound: Bound<DateTime<Utc>>) -> Self {
        match bound {
            Bound::Included(time) => AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(time) => AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => AbsoluteEndBound::InfiniteFuture,
        }
    }
}

/// Swaps an absolute start bound with an absolute end bound
///
/// This method is primarily used in the case where a start bound and an end bound are not in chronological order.
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, swap_absolute_bounds,
/// # };
/// let start_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
/// let end_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
///
/// let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
/// let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
///
/// swap_absolute_bounds(&mut start, &mut end);
///
/// assert_eq!(
///     start,
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(end_time)),
/// );
/// assert_eq!(
///     end,
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(start_time)),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub fn swap_absolute_bounds(start: &mut AbsoluteStartBound, end: &mut AbsoluteEndBound) {
    // We temporarily reborrow start and end for the match arms so that when a pattern matches, they move out of their
    // temporary scope and we can use the original mutable references without guard patterns shenanigans.
    // When destructuring, however, the scope of the reborrowed value extends up to where it is used within the body,
    // So we always finish our business with the reborrowed values first before accessing the original ones.
    match (&mut *start, &mut *end) {
        (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture) => {},
        (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(finite_end)) => {
            *start = AbsoluteStartBound::Finite(*finite_end);
            *end = AbsoluteEndBound::InfiniteFuture;
        },
        (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::InfiniteFuture) => {
            *end = AbsoluteEndBound::Finite(*finite_start);
            *start = AbsoluteStartBound::InfinitePast;
        },
        (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
            std::mem::swap(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteBoundsCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same time but don't have only inclusive bound inclusivities
    SameTimeButNotDoublyInclusive,
}

impl Display for AbsoluteBoundsCheckForIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StartPastEnd => write!(f, "Start bound is past the end bound"),
            Self::SameTimeButNotDoublyInclusive => write!(
                f,
                "Both bounds are on the same time but don't have only inclusive bound inclusivities"
            ),
        }
    }
}

impl Error for AbsoluteBoundsCheckForIntervalCreationError {}

/// Checks if the given start and end bound are ready for creating an interval
///
/// This method is used as part of [`prepare_absolute_bounds_for_interval_creation`], which is used by
/// [`AbsoluteBounds::new`], but also in other places where we want to make sure that a start and end bound
/// are ready to be used as part of the interval without using methods like [`AbsoluteBounds::new`] that
/// already go through this process.
///
/// # Errors
///
/// If the start bound is past the end bound,
/// it returns [`StartPastEnd`](AbsoluteBoundsCheckForIntervalCreationError::StartPastEnd).
///
/// If both bounds have the same time, but at least one of them has an exclusive bound inclusivity, it returns
/// [`SameTimeButNotDoublyInclusive`](AbsoluteBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive).
///
/// # Examples
///
/// ```
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBoundsCheckForIntervalCreationError, AbsoluteEndBound, AbsoluteStartBound,
/// #     check_absolute_bounds_for_interval_creation,
/// # };
/// fn validate_bounds_from_user(
///     start: &AbsoluteStartBound,
///     end: &AbsoluteEndBound,
/// ) -> Result<(), String> {
///     type IntervalCreaErr = AbsoluteBoundsCheckForIntervalCreationError;
///     match check_absolute_bounds_for_interval_creation(start, end) {
///         Ok(()) => Ok(()),
///         Err(IntervalCreaErr::StartPastEnd) => Err(
///             "Start and end must be in chronological order!".to_string()
///         ),
///         Err(IntervalCreaErr::SameTimeButNotDoublyInclusive) => Err(
///             "To represent a single point in time, both inclusivities must be inclusive!".to_string()
///         ),
///     }
/// }
/// ```
pub fn check_absolute_bounds_for_interval_creation(
    start: &AbsoluteStartBound,
    end: &AbsoluteEndBound,
) -> Result<(), AbsoluteBoundsCheckForIntervalCreationError> {
    match (start, end) {
        (AbsoluteStartBound::InfinitePast, _) | (_, AbsoluteEndBound::InfiniteFuture) => Ok(()),
        (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
            match finite_start.time().cmp(&finite_end.time()) {
                Ordering::Less => Ok(()),
                Ordering::Equal => {
                    if finite_start.inclusivity() == BoundInclusivity::Inclusive
                        && finite_end.inclusivity() == BoundInclusivity::Inclusive
                    {
                        Ok(())
                    } else {
                        Err(AbsoluteBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive)
                    }
                },
                Ordering::Greater => Err(AbsoluteBoundsCheckForIntervalCreationError::StartPastEnd),
            }
        },
    }
}

/// Prepares a start and end bound for being used as part of an interval
///
/// If some problems are present, see [`check_absolute_bounds_for_interval_creation`], it resolves them automatically
/// by modifying the passed mutable references for the start and end bound.
///
/// The returned boolean indicates whether a change was operated in order to fix the given bounds.
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, prepare_absolute_bounds_for_interval_creation,
/// # };
/// let start_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
/// let end_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
///
/// // Warning: not in chronological order!
/// let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
/// let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
///
/// let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);
///
/// if was_changed {
///     // Prompt the user for confirmation regarding the fixed bounds
/// }
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub fn prepare_absolute_bounds_for_interval_creation(
    start_mut: &mut AbsoluteStartBound,
    end_mut: &mut AbsoluteEndBound,
) -> bool {
    match check_absolute_bounds_for_interval_creation(start_mut, end_mut) {
        Ok(()) => false,
        Err(AbsoluteBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_absolute_bounds(start_mut, end_mut);
            true
        },
        Err(AbsoluteBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive) => {
            if let AbsoluteStartBound::Finite(finite_start_mut) = start_mut {
                finite_start_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            if let AbsoluteEndBound::Finite(finite_end_mut) = end_mut {
                finite_end_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            true
        },
    }
}

/// Enum for absolute start and end bounds
///
/// This enumerator is useful for storing both start and end bounds, usually for processing bounds individually.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum AbsoluteBound {
    Start(AbsoluteStartBound),
    End(AbsoluteEndBound),
}

impl AbsoluteBound {
    /// Returns whether it is of the [`Start`](AbsoluteBound::Start) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time))
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time))
    /// );
    ///
    /// assert!(start.is_start());
    /// assert!(!end.is_start());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    /// Returns whether it is of the [`End`](AbsoluteBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time))
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time))
    /// );
    ///
    /// assert!(end.is_end());
    /// assert!(!start.is_end());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    /// Returns the content of the [`Start`](AbsoluteBound::Start) variant
    ///
    /// Consumes `self` and puts the content of the [`Start`](AbsoluteBound::Start) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time))
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time))
    /// );
    ///
    /// assert_eq!(
    ///     start.start(),
    ///     Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time))),
    /// );
    /// assert_eq!(
    ///     end.start(),
    ///     None,
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn start(self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](AbsoluteBound::End) variant
    ///
    /// Consumes `self` and puts the content of the [`End`](AbsoluteBound::End) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time))
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time))
    /// );
    ///
    /// assert_eq!(
    ///     end.end(),
    ///     Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time))),
    /// );
    /// assert_eq!(
    ///     start.end(),
    ///     None,
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn end(self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the opposite bound type with the opposite inclusivity
    ///
    /// Simply use [`AbsoluteStartBound::opposite`] for start bounds,
    /// and [`AbsoluteEndBound::opposite`] for end bounds, and then wraps the result in [`AbsoluteBound`].
    ///
    /// If the bound is infinite, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteBound;
    /// # let bounds: [AbsoluteBound; 0] = [];
    /// struct BoundChange {
    ///     new_bound: AbsoluteBound,
    ///     before_new_bound: Option<AbsoluteBound>,
    /// }
    ///
    /// bounds.into_iter().map(|bound| BoundChange {
    ///     new_bound: bound,
    ///     before_new_bound: bound.opposite(),
    /// });
    /// ```
    ///
    /// A similar process is used in
    /// [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds).
    #[must_use]
    pub fn opposite(&self) -> Option<Self> {
        match self {
            Self::Start(start) => start.opposite().map(Self::End),
            Self::End(end) => end.opposite().map(Self::Start),
        }
    }
}

impl PartialEq for AbsoluteBound {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AbsoluteBound::Start(og_start), AbsoluteBound::Start(other_start)) => og_start.eq(other_start),
            (AbsoluteBound::End(og_end), AbsoluteBound::End(other_end)) => og_end.eq(other_end),
            (AbsoluteBound::Start(start), AbsoluteBound::End(end))
            | (AbsoluteBound::End(end), AbsoluteBound::Start(start)) => start.eq(end),
        }
    }
}

impl Eq for AbsoluteBound {}

impl PartialOrd for AbsoluteBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (AbsoluteBound::Start(og_start), AbsoluteBound::Start(other_start)) => og_start.cmp(other_start),
            (AbsoluteBound::End(og_end), AbsoluteBound::End(other_end)) => og_end.cmp(other_end),
            (AbsoluteBound::Start(og_start), AbsoluteBound::End(other_end)) => og_start.partial_cmp(other_end).unwrap(),
            (AbsoluteBound::End(og_end), AbsoluteBound::Start(other_start)) => og_end.partial_cmp(other_start).unwrap(),
        }
    }
}

impl Hash for AbsoluteBound {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Start(AbsoluteStartBound::InfinitePast) => {
                AbsoluteStartBound::InfinitePast.hash(state);
            },
            Self::Start(AbsoluteStartBound::Finite(finite)) | Self::End(AbsoluteEndBound::Finite(finite)) => {
                finite.hash(state);
            },
            Self::End(AbsoluteEndBound::InfiniteFuture) => {
                AbsoluteEndBound::InfiniteFuture.hash(state);
            },
        }
    }
}

impl From<AbsoluteStartBound> for AbsoluteBound {
    fn from(value: AbsoluteStartBound) -> Self {
        AbsoluteBound::Start(value)
    }
}

impl From<AbsoluteEndBound> for AbsoluteBound {
    fn from(value: AbsoluteEndBound) -> Self {
        AbsoluteBound::End(value)
    }
}

/// Possession of **non-empty** absolute bounds
pub trait HasAbsoluteBounds {
    /// Returns the absolute bounds of the object
    #[must_use]
    fn abs_bounds(&self) -> AbsoluteBounds;

    /// Returns the absolute start bound of the object
    #[must_use]
    fn abs_start(&self) -> AbsoluteStartBound;

    /// Returns the absolute end bound of the object
    #[must_use]
    fn abs_end(&self) -> AbsoluteEndBound;
}

/// Possession of possibly empty absolute bounds
pub trait HasEmptiableAbsoluteBounds {
    /// Returns the [`EmptiableAbsoluteBounds`] of the object
    #[must_use]
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds;

    /// Returns an [`Option`] of [the absolute start bound](AbsoluteStartBound) of the object
    #[must_use]
    fn partial_abs_start(&self) -> Option<AbsoluteStartBound>;

    /// Returns an [`Option`] of [the absolute end bound](AbsoluteEndBound) of the object
    #[must_use]
    fn partial_abs_end(&self) -> Option<AbsoluteEndBound>;
}

/// All implementors of [`HasAbsoluteBounds`] implement [`HasEmptiableAbsoluteBounds`].
/// This could change in the future to separate emptiable from non-emptiable bounds.
impl<T> HasEmptiableAbsoluteBounds for T
where
    T: HasAbsoluteBounds,
{
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        EmptiableAbsoluteBounds::Bound(self.abs_bounds())
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        Some(self.abs_start())
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        Some(self.abs_end())
    }
}

/// Pair of [`AbsoluteStartBound`] and [`AbsoluteEndBound`]
///
/// This pair conserves the invariants required for an interval:
///
/// 1. The bounds are in chronological order
/// 2. If the bounds have the same time, their inclusivities should be [inclusive] for both
///
/// [`AbsoluteBounds`] should be used when you want a non-empty interval which don't need to conserve
/// a given [`Openness`].
///
/// [inclusive]: BoundInclusivity::Inclusive
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBounds {
    start: AbsoluteStartBound,
    end: AbsoluteEndBound,
}

impl AbsoluteBounds {
    /// Creates a new [`AbsoluteBounds`] without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// // Start and end are not in chronological order!
    /// let start_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::unchecked_new(start, end);
    ///
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn unchecked_new(start: AbsoluteStartBound, end: AbsoluteEndBound) -> Self {
        AbsoluteBounds { start, end }
    }

    /// Creates a new [`AbsoluteBounds`]
    ///
    /// Uses [`prepare_absolute_bounds_for_interval_creation`] under the hood for making sure the bounds respect
    /// the invariants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// // Start and end are not in chronological order!
    /// let start_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::new(start, end);
    ///
    /// // Now the start and end are in chronological order
    /// assert_eq!(bounds.start(), &end);
    /// assert_eq!(bounds.end(), &start);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new(mut start: AbsoluteStartBound, mut end: AbsoluteEndBound) -> Self {
        prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);
        Self::unchecked_new(start, end)
    }

    /// Returns the absolute start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::new(start, end);
    ///
    /// assert_eq!(bounds.start(), &start);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn start(&self) -> &AbsoluteStartBound {
        &self.start
    }

    /// Returns the absolute end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::new(start, end);
    ///
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn end(&self) -> &AbsoluteEndBound {
        &self.end
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_start_time = "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?;
    /// let new_start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(new_start_time));
    ///
    /// // New start is past the end
    /// bounds.unchecked_set_start(new_start);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), &new_start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: AbsoluteStartBound) {
        self.start = new_start;
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_end_time = "2025-01-01 06:00:00Z".parse::<DateTime<Utc>>()?;
    /// let new_end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(new_end_time));
    ///
    /// // New end is before the start
    /// bounds.unchecked_set_end(new_end);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &new_end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: AbsoluteEndBound) {
        self.end = new_end;
    }

    /// Sets the start bound
    ///
    /// Returns whether the operation was successful and the start bound modified.
    /// If the given new start bound violates the invariants, the method simply returns `false`
    /// without changing the start bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_start_time = "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?;
    /// let new_start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(new_start_time));
    ///
    /// // New start is past the end, and therefore gets ignored
    /// let was_successful = bounds.set_start(new_start);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_start(&mut self, new_start: AbsoluteStartBound) -> bool {
        match check_absolute_bounds_for_interval_creation(&new_start, self.end()) {
            Ok(()) => {
                self.unchecked_set_start(new_start);
                true
            },
            Err(_) => false,
        }
    }

    /// Sets the end bound
    ///
    /// Returns whether the operation was successful and the end bound modified.
    /// If the given new end bound violates the invariants, the method simply returns `false`
    /// without changing the end bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_end_time = "2025-01-01 06:00:00Z".parse::<DateTime<Utc>>()?;
    /// let new_end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(new_end_time));
    ///
    /// // New end is before the start, and therefore gets ignored
    /// let was_successful = bounds.set_end(new_end);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_end(&mut self, new_end: AbsoluteEndBound) -> bool {
        match check_absolute_bounds_for_interval_creation(self.start(), &new_end) {
            Ok(()) => {
                self.unchecked_set_end(new_end);
                true
            },
            Err(_) => false,
        }
    }

    /// Compares two [`AbsoluteBounds`], but if they have the same start, order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteBounds;
    /// # let mut bounds: [AbsoluteBounds; 0] = [];
    /// bounds.sort_by(AbsoluteBounds::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match self.cmp(other) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.end.cmp(&other.end).reverse(),
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl Interval for AbsoluteBounds {}

impl HasAbsoluteBounds for AbsoluteBounds {
    fn abs_bounds(&self) -> AbsoluteBounds {
        self.clone()
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        *self.start()
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        *self.end()
    }
}

impl HasDuration for AbsoluteBounds {
    fn duration(&self) -> IntervalDuration {
        match (self.start(), self.end()) {
            (AbsoluteStartBound::InfinitePast, _) | (_, AbsoluteEndBound::InfiniteFuture) => IntervalDuration::Infinite,
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
                IntervalDuration::Finite(finite_end.time().signed_duration_since(finite_start.time()))
            },
        }
    }
}

impl HasOpenness for AbsoluteBounds {
    fn openness(&self) -> Openness {
        match (self.start(), self.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture) => Openness::Unbounded,
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(_))
            | (AbsoluteStartBound::Finite(_), AbsoluteEndBound::InfiniteFuture) => Openness::HalfBounded,
            (AbsoluteStartBound::Finite(_), AbsoluteEndBound::Finite(_)) => Openness::Bounded,
        }
    }
}

impl HasRelativity for AbsoluteBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl PartialOrd for AbsoluteBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        // using the comparison of self.end and other.end as a way to disambiguate when the two starts are equal
        // leads to side-effects, like when we store absolute bounds inside a BTreeSet, then if we use `range()`,
        // one can be considered out of the range when it shouldn't.
        self.start.cmp(&other.start)
    }
}

impl Display for AbsoluteBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());

        result = result.and(write!(f, "Absolute bounds: "));

        match self.start() {
            AbsoluteStartBound::Finite(AbsoluteFiniteBound { time, inclusivity }) => {
                result = result.and(write!(f, "{time} ({inclusivity})"));
            },
            AbsoluteStartBound::InfinitePast => {
                result = result.and(write!(f, "Infinite past"));
            },
        }

        result = result.and(write!(f, " to "));

        match self.end() {
            AbsoluteEndBound::Finite(AbsoluteFiniteBound { time, inclusivity }) => {
                result = result.and(write!(f, "{time} ({inclusivity})"));
            },
            AbsoluteEndBound::InfiniteFuture => {
                result = result.and(write!(f, "Infinite future"));
            },
        }

        result
    }
}

impl<R> From<R> for AbsoluteBounds
where
    R: RangeBounds<DateTime<Utc>>,
{
    fn from(range: R) -> Self {
        AbsoluteBounds::new(
            AbsoluteStartBound::from(range.start_bound().cloned()),
            AbsoluteEndBound::from(range.end_bound().cloned()),
        )
    }
}

/// Errors that can occur when trying to convert [`EmptiableAbsoluteBounds`] into [`AbsoluteBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbsoluteBoundsFromEmptiableAbsoluteBoundsError {
    EmptyVariant,
}

impl Display for AbsoluteBoundsFromEmptiableAbsoluteBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyVariant => write!(f, "Provided EmptiableAbsoluteBounds was empty"),
        }
    }
}

impl Error for AbsoluteBoundsFromEmptiableAbsoluteBoundsError {}

impl TryFrom<EmptiableAbsoluteBounds> for AbsoluteBounds {
    type Error = AbsoluteBoundsFromEmptiableAbsoluteBoundsError;

    fn try_from(value: EmptiableAbsoluteBounds) -> Result<Self, Self::Error> {
        match value {
            EmptiableAbsoluteBounds::Empty => Err(AbsoluteBoundsFromEmptiableAbsoluteBoundsError::EmptyVariant),
            EmptiableAbsoluteBounds::Bound(bounds) => Ok(bounds),
        }
    }
}

/// Enum containing [`AbsoluteBounds`] but with support for [empty intervals](EmptyInterval)
///
/// For more information, check [`AbsoluteBounds`], [`EmptyInterval`],
/// or [`crate::intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum EmptiableAbsoluteBounds {
    Empty,
    Bound(AbsoluteBounds),
}

impl EmptiableAbsoluteBounds {
    /// Returns the content of the [`Bound`](EmptiableAbsoluteBounds::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableAbsoluteBounds::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    /// # };
    /// let bounds = AbsoluteBounds::new(
    ///     AbsoluteStartBound::InfinitePast,
    ///     AbsoluteEndBound::InfiniteFuture,
    /// );
    /// // Cloning is only for making the use of `bounds` okay in the following assertions
    /// let bound_emptiable_bounds = EmptiableAbsoluteBounds::Bound(bounds.clone());
    /// let empty_emptiable_bounds = EmptiableAbsoluteBounds::Empty;
    ///
    /// assert_eq!(bound_emptiable_bounds.bound(), Some(bounds));
    /// assert_eq!(empty_emptiable_bounds.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<AbsoluteBounds> {
        match self {
            EmptiableAbsoluteBounds::Empty => None,
            EmptiableAbsoluteBounds::Bound(bound) => Some(bound),
        }
    }

    /// Compares two [`EmptiableAbsoluteBounds`], but if they have the same start, order by decreasing length
    ///
    /// Uses [`AbsoluteBounds::ord_by_start_and_inv_length`] under the hood for
    /// the [`Bound`](EmptiableAbsoluteBounds::Bound) variants and [`EmptiableAbsoluteBounds::cmp`]
    /// for the [`Empty`](EmptiableAbsoluteBounds::Empty) variants (which will just place all empty bounds before
    /// any bound bounds).
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::EmptiableAbsoluteBounds;
    /// # let mut bounds: [EmptiableAbsoluteBounds; 0] = [];
    /// bounds.sort_by(EmptiableAbsoluteBounds::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableAbsoluteBounds::Bound(og_abs_bounds), EmptiableAbsoluteBounds::Bound(other_abs_bounds)) => {
                og_abs_bounds.ord_by_start_and_inv_length(other_abs_bounds)
            },
            _ => self.cmp(other),
        }
    }
}

impl Interval for EmptiableAbsoluteBounds {}

impl HasEmptiableAbsoluteBounds for EmptiableAbsoluteBounds {
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        self.clone()
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.start()),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.end()),
        }
    }
}

impl Emptiable for EmptiableAbsoluteBounds {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableAbsoluteBounds {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(Duration::zero()),
        }
    }
}

impl HasOpenness for EmptiableAbsoluteBounds {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableAbsoluteBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl PartialOrd for EmptiableAbsoluteBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableAbsoluteBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Empty) => Ordering::Equal,
            (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Bound(_)) => Ordering::Less,
            (EmptiableAbsoluteBounds::Bound(_), EmptiableAbsoluteBounds::Empty) => Ordering::Greater,
            (EmptiableAbsoluteBounds::Bound(og_abs_bounds), EmptiableAbsoluteBounds::Bound(other_abs_bounds)) => {
                og_abs_bounds.cmp(other_abs_bounds)
            },
        }
    }
}

impl Display for EmptiableAbsoluteBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "Empty absolute interval bounds"),
            Self::Bound(bounds) => write!(f, "{bounds}"),
        }
    }
}

impl From<AbsoluteBounds> for EmptiableAbsoluteBounds {
    fn from(value: AbsoluteBounds) -> Self {
        EmptiableAbsoluteBounds::Bound(value)
    }
}

/// A bounded absolute interval
///
/// An interval with a set start and end. Like all specific absolute interval types, it conserves the invariant
/// of its bounds being in chronological order and if the bounds have the same time, they must be inclusive.
///
/// However, like the other specific interval types, it conserves an additional invariant:
/// Its [openness](Openness) cannot change. That is to say a bounded interval must remain a bounded interval.
/// It cannot mutate from being a bounded interval to a half-bounded interval.
///
/// Instead, if you are looking for an absolute interval that doesn't keep the [openness](Openness) invariant,
/// see [`AbsoluteBounds`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoundedAbsoluteInterval {
    from: DateTime<Utc>,
    to: DateTime<Utc>,
    from_inclusivity: BoundInclusivity,
    to_inclusivity: BoundInclusivity,
}

impl BoundedAbsoluteInterval {
    /// Creates a new [`BoundedAbsoluteInterval`] without checking if it violates the invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// // Even though the times are not in chronological order
    /// let bounded_interval = BoundedAbsoluteInterval::unchecked_new(from_time, to_time);
    ///
    /// // They remain that way
    /// assert_eq!(bounded_interval.from_time(), from_time);
    /// assert_eq!(bounded_interval.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn unchecked_new(from: DateTime<Utc>, to: DateTime<Utc>) -> Self {
        BoundedAbsoluteInterval {
            from,
            to,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with default bound inclusivities
    ///
    /// If the from time is past the to time, it swaps them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// // Times that are not in chronological order
    /// let bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // Are swapped
    /// assert_eq!(bounded_interval.from_time(), to_time);
    /// assert_eq!(bounded_interval.to_time(), from_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new(mut from: DateTime<Utc>, mut to: DateTime<Utc>) -> Self {
        if from > to {
            std::mem::swap(&mut from, &mut to);
        }

        Self::unchecked_new(from, to)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with the given bound inclusivities without checking
    /// if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// // Same time, not doubly inclusive
    /// let bounded_interval = BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
    ///     time,
    ///     BoundInclusivity::Inclusive,
    ///     time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn unchecked_new_with_inclusivity(
        from: DateTime<Utc>,
        from_inclusivity: BoundInclusivity,
        to: DateTime<Utc>,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        BoundedAbsoluteInterval {
            from,
            to,
            from_inclusivity,
            to_inclusivity,
        }
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with the given bound inclusivities
    ///
    /// If the given times are not in chronological order, we swap them so they are in chronological order.
    ///
    /// If the given times are equal but have bound inclusivities other than inclusive,
    /// we set them to [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// // Same time, not doubly inclusive
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     time,
    ///     BoundInclusivity::Inclusive,
    ///     time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// // Therefore gets reset to inclusive for both bounds
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Inclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        from: DateTime<Utc>,
        from_inclusivity: BoundInclusivity,
        to: DateTime<Utc>,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        match from.cmp(&to) {
            Ordering::Less => Self::unchecked_new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            Ordering::Equal => Self::unchecked_new(from, to),
            Ordering::Greater => Self::unchecked_new_with_inclusivity(to, to_inclusivity, from, from_inclusivity),
        }
    }

    /// Returns the start time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let bounded_inclusivity = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// assert_eq!(bounded_inclusivity.from_time(), from_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn from_time(&self) -> DateTime<Utc> {
        self.from
    }

    /// Returns the end time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let bounded_inclusivity = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// assert_eq!(bounded_inclusivity.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn to_time(&self) -> DateTime<Utc> {
        self.to
    }

    /// Returns the inclusivity of the start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     from_time,
    ///     BoundInclusivity::Exclusive,
    ///     to_time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn from_inclusivity(&self) -> BoundInclusivity {
        self.from_inclusivity
    }

    /// Returns the inclusivity of the end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     from_time,
    ///     BoundInclusivity::Exclusive,
    ///     to_time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn to_inclusivity(&self) -> BoundInclusivity {
        self.to_inclusivity
    }

    /// Sets the from time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New from is not in chronological order
    /// let new_from_time = "2025-01-01 17:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// bounded_interval.unchecked_set_from(new_from_time);
    ///
    /// // And yet is stays that way
    /// assert_eq!(bounded_interval.from_time(), new_from_time);
    /// assert_eq!(bounded_interval.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_from(&mut self, new_from: DateTime<Utc>) {
        self.from = new_from;
    }

    /// Sets the to time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New to is not in chronological order
    /// let new_to_time = "2025-01-01 06:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// bounded_interval.unchecked_set_to(new_to_time);
    ///
    /// // And yet is stays that way
    /// assert_eq!(bounded_interval.from_time(), from_time);
    /// assert_eq!(bounded_interval.to_time(), new_to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_to(&mut self, new_to: DateTime<Utc>) {
        self.to = new_to;
    }

    /// Sets the from time
    ///
    /// Returns whether the operation was successful and the from time modified.
    /// If the given new from time violates the invariants, the method simply returns `false`
    /// without changing the from time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New from is not in chronological order
    /// let new_from_time = "2025-01-01 17:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let was_successful = bounded_interval.set_from(new_from_time);
    ///
    /// // Therefore gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.from_time(), from_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_from(&mut self, new_from: DateTime<Utc>) -> bool {
        match new_from.cmp(&self.to) {
            Ordering::Less => {
                self.unchecked_set_from(new_from);
                true
            },
            Ordering::Equal => {
                if self.from_inclusivity != BoundInclusivity::Inclusive
                    || self.to_inclusivity != BoundInclusivity::Inclusive
                {
                    return false;
                }

                self.unchecked_set_from(new_from);
                true
            },
            Ordering::Greater => false,
        }
    }

    /// Sets the to time
    ///
    /// Returns whether the operation was successful and the to time modified.
    /// If the given new to time violates the invariants, the method simply returns `false`
    /// without changing the to time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New to is not in chronological order
    /// let new_to_time = "2025-01-01 06:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let was_successful = bounded_interval.set_to(new_to_time);
    ///
    /// // Therefore gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_to(&mut self, new_to: DateTime<Utc>) -> bool {
        match self.from.cmp(&new_to) {
            Ordering::Less => {
                self.unchecked_set_to(new_to);
                true
            },
            Ordering::Equal => {
                if self.from_inclusivity != BoundInclusivity::Inclusive
                    || self.to_inclusivity != BoundInclusivity::Inclusive
                {
                    return false;
                }

                self.unchecked_set_to(new_to);
                true
            },
            Ordering::Greater => false,
        }
    }

    /// Sets the inclusivity of the start bound
    ///
    /// Returns whether the operation was successful and the start bound's inclusivity modified.
    /// If the given new start bound inclusivity violates the invariants, the method simply returns `false`
    /// without changing the start bound's inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(time, time);
    ///
    /// // Interval has same times, therefore cannot be other than doubly inclusive
    /// let was_successful = bounded_interval.set_from_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Therefore new inclusivity gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.from == self.to && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.from_inclusivity = new_inclusivity;
        true
    }

    /// Sets the inclusivity of the end bound
    ///
    /// Returns whether the operation was successful and the end bound's inclusivity modified.
    /// If the given new end bound inclusivity violates the invariants, the method simply returns `false`
    /// without changing the end bound's inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(time, time);
    ///
    /// // Interval has same times, therefore cannot be other than doubly inclusive
    /// let was_successful = bounded_interval.set_to_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Therefore new inclusivity gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Inclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.from == self.to && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.to_inclusivity = new_inclusivity;
        true
    }
}

impl Interval for BoundedAbsoluteInterval {}

impl HasOpenness for BoundedAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::Bounded
    }
}

impl HasRelativity for BoundedAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for BoundedAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(self.to - self.from)
    }
}

impl HasAbsoluteBounds for BoundedAbsoluteInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::unchecked_new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            self.from,
            self.from_inclusivity,
        ))
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(self.to, self.to_inclusivity))
    }
}

impl From<(DateTime<Utc>, DateTime<Utc>)> for BoundedAbsoluteInterval {
    fn from((from, to): (DateTime<Utc>, DateTime<Utc>)) -> Self {
        BoundedAbsoluteInterval::new(from, to)
    }
}

impl From<((DateTime<Utc>, BoundInclusivity), (DateTime<Utc>, BoundInclusivity))> for BoundedAbsoluteInterval {
    fn from(
        ((from, from_inclusivity), (to, to_inclusivity)): (
            (DateTime<Utc>, BoundInclusivity),
            (DateTime<Utc>, BoundInclusivity),
        ),
    ) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity)
    }
}

/// Converts `((DateTime<Utc>, bool), (DateTime<Utc>, bool))` into [`BoundedAbsoluteInterval`]
///
/// The booleans in the original structure are to be interpreted as _is it inclusive?_
impl From<((DateTime<Utc>, bool), (DateTime<Utc>, bool))> for BoundedAbsoluteInterval {
    fn from(
        ((from, is_from_inclusive), (to, is_to_inclusive)): ((DateTime<Utc>, bool), (DateTime<Utc>, bool)),
    ) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            from,
            BoundInclusivity::from(is_from_inclusive),
            to,
            BoundInclusivity::from(is_to_inclusive),
        )
    }
}

impl From<Range<DateTime<Utc>>> for BoundedAbsoluteInterval {
    fn from(range: Range<DateTime<Utc>>) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<DateTime<Utc>>> for BoundedAbsoluteInterval {
    fn from(range: RangeInclusive<DateTime<Utc>>) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

/// Errors that can occur when trying to convert [`AbsoluteBounds`] into [`BoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalFromAbsoluteBoundsError {
    NotBoundedInterval,
}

impl Display for BoundedAbsoluteIntervalFromAbsoluteBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotBoundedInterval => write!(f, "Not a bounded interval"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalFromAbsoluteBoundsError {}

impl TryFrom<AbsoluteBounds> for BoundedAbsoluteInterval {
    type Error = BoundedAbsoluteIntervalFromAbsoluteBoundsError;

    fn try_from(value: AbsoluteBounds) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
                Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity(),
                    finite_end.time(),
                    finite_end.inclusivity(),
                ))
            },
            _ => Err(Self::Error::NotBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`AbsoluteInterval`] into [`BoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalFromAbsoluteIntervalError {
    WrongVariant,
}

impl Display for BoundedAbsoluteIntervalFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for BoundedAbsoluteInterval {
    type Error = BoundedAbsoluteIntervalFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Bounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// A half-bounded absolute interval
///
/// An interval with a set reference time and an [opening direction](OpeningDirection).
/// Like all specific absolute interval types, it conserves the invariant of its bounds being
/// in chronological order[^chrono_order_invariant] and if the interval has a length of zero,
/// they must be inclusive[^doubly_inclusive_invariant].
///
/// However, like the other specific interval types, it conserves an additional invariant:
/// Its [openness](Openness) cannot change. That is to say a half-bounded interval must remain a half-bounded interval.
/// It cannot mutate from being a half-bounded interval to a bounded interval.
///
/// [^chrono_order_invariant]: This invariant is automatically guaranteed in this structure
///     since it only has one bound.
/// [^doubly_inclusive_invariant]: This invariant is automatically guaranteed in this structure
///     since the reference time is finite and therefore cannot reach the opposite end of the half-bounded interval,
///     since the opposite end is infinite.
///
/// Instead, if you are looking for an absolute interval that doesn't keep the [openness](Openness) invariant,
/// see [`AbsoluteBounds`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub struct HalfBoundedAbsoluteInterval {
    reference_time: DateTime<Utc>,
    opening_direction: OpeningDirection,
    reference_inclusivity: BoundInclusivity,
}

impl HalfBoundedAbsoluteInterval {
    /// Creates a new [`HalfBoundedAbsoluteInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new(reference_time: DateTime<Utc>, opening_direction: OpeningDirection) -> Self {
        HalfBoundedAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] with the given bound inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        reference_time: DateTime<Utc>,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfBoundedAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_inclusivity: reference_time_inclusivity,
        }
    }

    /// Returns the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn reference_time(&self) -> DateTime<Utc> {
        self.reference_time
    }

    /// Returns the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference time
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference_inclusivity
    }

    /// Sets the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_ref_time = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// half_bounded_interval.set_reference_time(new_ref_time);
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), new_ref_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_reference_time(&mut self, new_reference_time: DateTime<Utc>) {
        self.reference_time = new_reference_time;
    }

    /// Sets the inclusivity of the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded_interval.set_reference_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_reference_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_inclusivity = new_inclusivity;
    }

    /// Sets the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded_interval.set_opening_direction(OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        self.opening_direction = new_opening_direction;
    }
}

impl Interval for HalfBoundedAbsoluteInterval {}

impl HasOpenness for HalfBoundedAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for HalfBoundedAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasAbsoluteBounds for HalfBoundedAbsoluteInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteStartBound::InfinitePast,
            OpeningDirection::ToFuture => AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                self.reference_time,
                self.reference_inclusivity,
            )),
        }
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                self.reference_time,
                self.reference_inclusivity,
            )),
            OpeningDirection::ToFuture => AbsoluteEndBound::InfiniteFuture,
        }
    }
}

impl From<(DateTime<Utc>, OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from((time, direction): (DateTime<Utc>, OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new(time, direction)
    }
}

/// Converts `(DateTime<Utc>, bool)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean is interpreted as _is it going to future?_
impl From<(DateTime<Utc>, bool)> for HalfBoundedAbsoluteInterval {
    fn from((time, goes_to_future): (DateTime<Utc>, bool)) -> Self {
        HalfBoundedAbsoluteInterval::new(time, OpeningDirection::from(goes_to_future))
    }
}

impl From<((DateTime<Utc>, BoundInclusivity), OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from(((time, inclusivity), direction): ((DateTime<Utc>, BoundInclusivity), OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(time, inclusivity, direction)
    }
}

/// Converts `((DateTime<Utc>, BoundInclusivity), bool)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean is interpreted as _is it going to future?_
impl From<((DateTime<Utc>, BoundInclusivity), bool)> for HalfBoundedAbsoluteInterval {
    fn from(((time, inclusivity), goes_to_future): ((DateTime<Utc>, BoundInclusivity), bool)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(time, inclusivity, OpeningDirection::from(goes_to_future))
    }
}

/// Converts `((DateTime<Utc>, bool), OpeningDirection)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean is interpreted as _is it inclusive?_
impl From<((DateTime<Utc>, bool), OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from(((time, is_inclusive), direction): ((DateTime<Utc>, bool), OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(time, BoundInclusivity::from(is_inclusive), direction)
    }
}

/// Converts `((DateTime<Utc>, bool), bool)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean of the first tuple element is interpreted as _is it inclusive?_
///
/// The boolean of the second tuple element is interpreted as _is it going to future?_
impl From<((DateTime<Utc>, bool), bool)> for HalfBoundedAbsoluteInterval {
    fn from(((time, is_inclusive), goes_to_future): ((DateTime<Utc>, bool), bool)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            time,
            BoundInclusivity::from(is_inclusive),
            OpeningDirection::from(goes_to_future),
        )
    }
}

impl From<RangeFrom<DateTime<Utc>>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeFrom<DateTime<Utc>>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<DateTime<Utc>>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeTo<DateTime<Utc>>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<DateTime<Utc>>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeToInclusive<DateTime<Utc>>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

/// Errors that can occur when trying to convert [`AbsoluteBounds`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError {
    NotHalfBoundedInterval,
}

impl Display for HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotHalfBoundedInterval => write!(f, "Not a half-bounded interval"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError {}

impl TryFrom<AbsoluteBounds> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError;

    fn try_from(value: AbsoluteBounds) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(finite_end)) => {
                Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    finite_end.time(),
                    finite_end.inclusivity(),
                    OpeningDirection::ToPast,
                ))
            },
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::InfiniteFuture) => {
                Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity(),
                    OpeningDirection::ToFuture,
                ))
            },
            _ => Err(Self::Error::NotHalfBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`AbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {
    WrongVariant,
}

impl Display for HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::HalfBounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// An absolute interval
///
/// An enumerator to store any kind of absolute interval: [`BoundedAbsoluteInterval`],
/// [`HalfBoundedAbsoluteInterval`], [`UnboundedInterval`], and [`EmptyInterval`].
///
/// The contained intervals conserve the [openness](Openness) invariant, but the chosen variant can change.
/// Compared to [`AbsoluteBounds`], thanks to the variants we know exactly the kind of interval that is stored
/// without needing to check inner data.
///
/// Usually this is the structure that you want to use when dealing with absolute intervals
/// as it has more conversion methods from standard types, and also provides a quick way to know the type of
/// the interval and perhaps extract from it to make its type immutable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum AbsoluteInterval {
    Bounded(BoundedAbsoluteInterval),
    HalfBounded(HalfBoundedAbsoluteInterval),
    Unbounded(UnboundedInterval),
    Empty(EmptyInterval),
}

impl AbsoluteInterval {
    /// Compares two [`AbsoluteInterval`], but if they have the same start, order by decreasing length
    ///
    /// Uses [`EmptiableAbsoluteBounds::ord_by_start_and_inv_length`] under the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteInterval;
    /// # let mut bounds: [AbsoluteInterval; 0] = [];
    /// bounds.sort_by(AbsoluteInterval::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.emptiable_abs_bounds()
            .ord_by_start_and_inv_length(&other.emptiable_abs_bounds())
    }
}

impl Interval for AbsoluteInterval {}

impl HasDuration for AbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
            Self::Empty(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for AbsoluteInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
            Self::Empty(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for AbsoluteInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
            Self::Empty(interval) => interval.openness(),
        }
    }
}

impl HasEmptiableAbsoluteBounds for AbsoluteInterval {
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        match self {
            Self::Bounded(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::HalfBounded(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::Unbounded(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::Empty(interval) => interval.emptiable_abs_bounds(),
        }
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Bounded(interval) => interval.partial_abs_start(),
            Self::HalfBounded(interval) => interval.partial_abs_start(),
            Self::Unbounded(interval) => interval.partial_abs_start(),
            Self::Empty(interval) => interval.partial_abs_start(),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Bounded(interval) => interval.partial_abs_end(),
            Self::HalfBounded(interval) => interval.partial_abs_end(),
            Self::Unbounded(interval) => interval.partial_abs_end(),
            Self::Empty(interval) => interval.partial_abs_end(),
        }
    }
}

impl Emptiable for AbsoluteInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for AbsoluteInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_abs_bounds().cmp(&other.emptiable_abs_bounds())
    }
}

impl From<BoundedAbsoluteInterval> for AbsoluteInterval {
    fn from(value: BoundedAbsoluteInterval) -> Self {
        AbsoluteInterval::Bounded(value)
    }
}

impl From<HalfBoundedAbsoluteInterval> for AbsoluteInterval {
    fn from(value: HalfBoundedAbsoluteInterval) -> Self {
        AbsoluteInterval::HalfBounded(value)
    }
}

impl From<UnboundedInterval> for AbsoluteInterval {
    fn from(value: UnboundedInterval) -> Self {
        AbsoluteInterval::Unbounded(value)
    }
}

impl From<EmptyInterval> for AbsoluteInterval {
    fn from(value: EmptyInterval) -> Self {
        AbsoluteInterval::Empty(value)
    }
}

impl From<AbsoluteBounds> for AbsoluteInterval {
    fn from(value: AbsoluteBounds) -> Self {
        type StartB = AbsoluteStartBound;
        type EndB = AbsoluteEndBound;

        match (value.abs_start(), value.abs_end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => AbsoluteInterval::Unbounded(UnboundedInterval),
            (StartB::InfinitePast, EndB::Finite(AbsoluteFiniteBound { time, inclusivity })) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(AbsoluteFiniteBound { time, inclusivity }), EndB::InfiniteFuture) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (
                StartB::Finite(AbsoluteFiniteBound {
                    time: start_time,
                    inclusivity: start_inclusivity,
                }),
                EndB::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                }),
            ) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
                start_time,
                start_inclusivity,
                end_time,
                end_inclusivity,
            )),
        }
    }
}

impl From<EmptiableAbsoluteBounds> for AbsoluteInterval {
    fn from(value: EmptiableAbsoluteBounds) -> Self {
        type StartB = AbsoluteStartBound;
        type EndB = AbsoluteEndBound;

        match (value.partial_abs_start(), value.partial_abs_end()) {
            (None, _) | (_, None) => AbsoluteInterval::Empty(EmptyInterval),
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => AbsoluteInterval::Unbounded(UnboundedInterval),
            (Some(StartB::InfinitePast), Some(EndB::Finite(AbsoluteFiniteBound { time, inclusivity }))) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (Some(StartB::Finite(AbsoluteFiniteBound { time, inclusivity })), Some(EndB::InfiniteFuture)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (
                Some(StartB::Finite(AbsoluteFiniteBound {
                    time: start_time,
                    inclusivity: start_inclusivity,
                })),
                Some(EndB::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                })),
            ) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
                start_time,
                start_inclusivity,
                end_time,
                end_inclusivity,
            )),
        }
    }
}

/// Converts `(Option<DateTime<Utc>>, Option<DateTime<Utc>>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
impl From<(Option<DateTime<Utc>>, Option<DateTime<Utc>>)> for AbsoluteInterval {
    fn from((from_opt, to_opt): (Option<DateTime<Utc>>, Option<DateTime<Utc>>)) -> Self {
        match (from_opt, to_opt) {
            (Some(from), Some(to)) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(from, to)),
            (Some(from), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(DateTime<Utc>, BoundInclusivity)>, Option<(DateTime<Utc>, BoundInclusivity)>)`
/// into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
impl
    From<(
        Option<(DateTime<Utc>, BoundInclusivity)>,
        Option<(DateTime<Utc>, BoundInclusivity)>,
    )> for AbsoluteInterval
{
    fn from(
        (from_opt, to_opt): (
            Option<(DateTime<Utc>, BoundInclusivity)>,
            Option<(DateTime<Utc>, BoundInclusivity)>,
        ),
    ) -> Self {
        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(DateTime<Utc>, bool)>, Option<(DateTime<Utc>, bool)>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
///
/// The booleans contained within the `Option<(DateTime<Utc>, bool)>`s are interpreted as _is it inclusive?_
impl From<(Option<(DateTime<Utc>, bool)>, Option<(DateTime<Utc>, bool)>)> for AbsoluteInterval {
    fn from((from_opt, to_opt): (Option<(DateTime<Utc>, bool)>, Option<(DateTime<Utc>, bool)>)) -> Self {
        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<DateTime<Utc>>, Option<DateTime<Utc>>)` into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, Option<DateTime<Utc>>, Option<DateTime<Utc>>)> for AbsoluteInterval {
    fn from((is_empty, from_opt, to_opt): (bool, Option<DateTime<Utc>>, Option<DateTime<Utc>>)) -> Self {
        if is_empty {
            return AbsoluteInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some(from), Some(to)) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(from, to)),
            (Some(from), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<(DateTime<Utc>, BoundInclusivity)>, Option<(DateTime<Utc>, BoundInclusivity)>)`
/// into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl
    From<(
        bool,
        Option<(DateTime<Utc>, BoundInclusivity)>,
        Option<(DateTime<Utc>, BoundInclusivity)>,
    )> for AbsoluteInterval
{
    fn from(
        (is_empty, from_opt, to_opt): (
            bool,
            Option<(DateTime<Utc>, BoundInclusivity)>,
            Option<(DateTime<Utc>, BoundInclusivity)>,
        ),
    ) -> Self {
        if is_empty {
            return AbsoluteInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<(DateTime<Utc>, bool)>, Option<(DateTime<Utc>, bool)>)` into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
///
/// The booleans contained within the `Option<(DateTime<Utc>, bool)>`s are interpreted as _is it inclusive?_
impl From<(bool, Option<(DateTime<Utc>, bool)>, Option<(DateTime<Utc>, bool)>)> for AbsoluteInterval {
    fn from(
        (is_empty, from_opt, to_opt): (bool, Option<(DateTime<Utc>, bool)>, Option<(DateTime<Utc>, bool)>),
    ) -> Self {
        if is_empty {
            return AbsoluteInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

// Unfortunately can't use impl<R: RangeBounds> From<R> as it's conflicting with the core implementation of From
/// Converts `(Bound<DateTime<Utc>>, Bound<DateTime<Utc>>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second tuple element represents the end bound.
impl From<(Bound<DateTime<Utc>>, Bound<DateTime<Utc>>)> for AbsoluteInterval {
    fn from((start_bound, end_bound): (Bound<DateTime<Utc>>, Bound<DateTime<Utc>>)) -> Self {
        match (start_bound, end_bound) {
            (Bound::Included(from), Bound::Included(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Included(from), Bound::Excluded(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Included(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Excluded(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Included(from), Bound::Unbounded) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Excluded(from), Bound::Unbounded) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Unbounded, Bound::Included(from)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Excluded(from)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Unbounded) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<Range<DateTime<Utc>>> for AbsoluteInterval {
    fn from(value: Range<DateTime<Utc>>) -> Self {
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeInclusive<DateTime<Utc>>> for AbsoluteInterval {
    fn from(value: RangeInclusive<DateTime<Utc>>) -> Self {
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeFrom<DateTime<Utc>>> for AbsoluteInterval {
    fn from(value: RangeFrom<DateTime<Utc>>) -> Self {
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeTo<DateTime<Utc>>> for AbsoluteInterval {
    fn from(value: RangeTo<DateTime<Utc>>) -> Self {
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeToInclusive<DateTime<Utc>>> for AbsoluteInterval {
    fn from(value: RangeToInclusive<DateTime<Utc>>) -> Self {
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeFull> for AbsoluteInterval {
    fn from(_value: RangeFull) -> Self {
        AbsoluteInterval::Unbounded(UnboundedInterval)
    }
}

impl From<()> for AbsoluteInterval {
    fn from(_value: ()) -> Self {
        AbsoluteInterval::Empty(EmptyInterval)
    }
}

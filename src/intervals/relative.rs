//! Relative intervals

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::{Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use chrono::Duration;

use crate::intervals::meta::Interval;

use super::meta::{BoundInclusivity, Duration as IntervalDuration, OpeningDirection, Openness, Relativity};
use super::prelude::*;
use super::special::{EmptyInterval, UnboundedInterval};

/// A relative finite bound
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub struct RelativeFiniteBound {
    offset: Duration,
    inclusivity: BoundInclusivity,
}

impl RelativeFiniteBound {
    /// Creates a new relative finite bound using just the offset
    #[must_use]
    pub fn new(offset: Duration) -> Self {
        Self::new_with_inclusivity(offset, BoundInclusivity::default())
    }

    /// Creates a new relative finite bound using the given offset and inclusivity
    #[must_use]
    pub fn new_with_inclusivity(offset: Duration, inclusivity: BoundInclusivity) -> Self {
        RelativeFiniteBound { offset, inclusivity }
    }

    /// Returns the offset
    #[must_use]
    pub fn offset(&self) -> Duration {
        self.offset
    }

    /// Sets the offset of the relative finite bound
    pub fn set_offset(&mut self, offset: Duration) {
        self.offset = offset;
    }

    /// Sets the inclusivity of the relative finite bound
    pub fn set_inclusivity(&mut self, inclusivity: BoundInclusivity) {
        self.inclusivity = inclusivity;
    }
}

impl HasBoundInclusivity for RelativeFiniteBound {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl PartialOrd for RelativeFiniteBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeFiniteBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl Display for RelativeFiniteBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Relative finite bound with offset {} ({})",
            self.offset, self.inclusivity
        )
    }
}

impl From<Duration> for RelativeFiniteBound {
    fn from(value: Duration) -> Self {
        RelativeFiniteBound::new(value)
    }
}

impl From<(Duration, BoundInclusivity)> for RelativeFiniteBound {
    fn from((offset, inclusivity): (Duration, BoundInclusivity)) -> Self {
        RelativeFiniteBound::new_with_inclusivity(offset, inclusivity)
    }
}

impl From<(Duration, bool)> for RelativeFiniteBound {
    fn from((offset, is_inclusive): (Duration, bool)) -> Self {
        RelativeFiniteBound::new_with_inclusivity(
            offset,
            if is_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
        )
    }
}

/// Errors that can occur when trying to convert a [`Bound<Duration>`] into an [`RelativeFiniteBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeFiniteBoundFromBoundError {
    /// The given bound was of the [`Unbounded`](Bound::Unbounded) variant
    IsUnbounded,
}

impl Display for RelativeFiniteBoundFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IsUnbounded => {
                write!(
                    f,
                    "The given bound was of the `Unbounded` variant, \
                    and therefore could not be converted to an `RelativeFiniteBound`"
                )
            },
        }
    }
}

impl Error for RelativeFiniteBoundFromBoundError {}

impl TryFrom<Bound<Duration>> for RelativeFiniteBound {
    type Error = RelativeFiniteBoundFromBoundError;

    fn try_from(value: Bound<Duration>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(offset) => Ok(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(offset) => Ok(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => Err(RelativeFiniteBoundFromBoundError::IsUnbounded),
        }
    }
}

/// A relative start interval bound, including [inclusivity](BoundInclusivity)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum RelativeStartBound {
    Finite(RelativeFiniteBound),
    InfinitePast,
}

impl RelativeStartBound {
    /// Returns whether the [`RelativeStartBound`] is of the [`Finite`](RelativeStartBound::Finite) variant
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether the [`RelativeStartBound`] is of the [`InfinitePast`](RelativeStartBound::InfinitePast) variant
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfinitePast)
    }

    /// Returns the content of the [`Finite`](RelativeStartBound::Finite) variant
    #[must_use]
    pub fn finite(self) -> Option<RelativeFiniteBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfinitePast => None,
        }
    }

    /// Returns the opposite [`RelativeEndBound`]
    ///
    /// Returns [`None`] if the [`RelativeStartBound`] is of the [`InfinitePast`](RelativeStartBound::InfinitePast)
    /// variant.
    #[must_use]
    pub fn opposite(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Finite(finite) => Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                finite.offset(),
                finite.inclusivity().opposite(),
            ))),
            Self::InfinitePast => None,
        }
    }
}

impl PartialEq<RelativeEndBound> for RelativeStartBound {
    fn eq(&self, other: &RelativeEndBound) -> bool {
        let RelativeStartBound::Finite(RelativeFiniteBound {
            offset: start_offset,
            inclusivity: start_inclusivity,
        }) = self
        else {
            return false;
        };
        let RelativeEndBound::Finite(RelativeFiniteBound {
            offset: end_offset,
            inclusivity: end_inclusivity,
        }) = other
        else {
            return false;
        };

        // If the offsets are equal, anything other than double inclusive bounds is invalid
        start_offset == end_offset
            && *start_inclusivity == BoundInclusivity::Inclusive
            && *end_inclusivity == BoundInclusivity::Inclusive
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
            (RelativeStartBound::InfinitePast, RelativeStartBound::InfinitePast) => Ordering::Equal,
            (RelativeStartBound::InfinitePast, RelativeStartBound::Finite(_)) => Ordering::Less,
            (RelativeStartBound::Finite(_), RelativeStartBound::InfinitePast) => Ordering::Greater,
            (
                RelativeStartBound::Finite(RelativeFiniteBound {
                    offset: offset_og,
                    inclusivity: inclusivity_og,
                }),
                RelativeStartBound::Finite(RelativeFiniteBound {
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
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Less,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Greater,
                }
            },
        }
    }
}

impl PartialOrd<RelativeEndBound> for RelativeStartBound {
    fn partial_cmp(&self, other: &RelativeEndBound) -> Option<Ordering> {
        match (self, other) {
            (RelativeStartBound::InfinitePast, _) | (_, RelativeEndBound::InfiniteFuture) => Some(Ordering::Less),
            (
                RelativeStartBound::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                }),
                RelativeEndBound::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                }),
            ) => match start_offset.cmp(end_offset) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Equal => {
                    let disambiguated_bound_overlap =
                        BoundOverlapAmbiguity::StartEnd(*start_inclusivity, *end_inclusivity)
                            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict);

                    match disambiguated_bound_overlap {
                        DisambiguatedBoundOverlap::Before => Some(Ordering::Less),
                        DisambiguatedBoundOverlap::Equal => Some(Ordering::Equal),
                        DisambiguatedBoundOverlap::After => Some(Ordering::Greater),
                    }
                },
                Ordering::Greater => Some(Ordering::Greater),
            },
        }
    }
}

impl Display for RelativeStartBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());
        result = result.and(write!(f, "Relative start: "));

        match self {
            Self::Finite(RelativeFiniteBound { offset, inclusivity }) => {
                result = result.and(write!(f, "{offset} ({inclusivity})"));
            },
            Self::InfinitePast => {
                result = result.and(write!(f, "Infinite past"));
            },
        }

        result
    }
}

impl From<RelativeFiniteBound> for RelativeStartBound {
    fn from(value: RelativeFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Bound<Duration>> for RelativeStartBound {
    fn from(bound: Bound<Duration>) -> Self {
        match bound {
            Bound::Included(offset) => RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(offset) => RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => RelativeStartBound::InfinitePast,
        }
    }
}

/// A relative end interval bound, including [inclusivity](BoundInclusivity)
///
/// This contains an offset from the reference time to the end bound, not the length of the relative interval.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum RelativeEndBound {
    Finite(RelativeFiniteBound),
    InfiniteFuture,
}

impl RelativeEndBound {
    /// Returns whether the [`RelativeEndBound`] is of the [`Finite`](RelativeEndBound::Finite) variant
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether the [`RelativeEndBound`] is of the [`InfiniteFuture`](RelativeEndBound::InfiniteFuture) variant
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfiniteFuture)
    }

    /// Returns the content of the [`Finite`](RelativeEndBound::Finite) variant
    #[must_use]
    pub fn finite(self) -> Option<RelativeFiniteBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfiniteFuture => None,
        }
    }

    /// Returns the opposite [`RelativeStartBound`]
    ///
    /// Returns [`None`] if the [`RelativeEndBound`] is of the [`InfiniteFuture`](RelativeEndBound::InfiniteFuture)
    /// variant.
    #[must_use]
    pub fn opposite(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Finite(finite) => Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                finite.offset(),
                finite.inclusivity().opposite(),
            ))),
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
                        DisambiguatedBoundOverlap::Before => Some(Ordering::Less),
                        DisambiguatedBoundOverlap::Equal => Some(Ordering::Equal),
                        DisambiguatedBoundOverlap::After => Some(Ordering::Greater),
                    }
                },
                Ordering::Greater => Some(Ordering::Greater),
            },
        }
    }
}

impl Display for RelativeEndBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());
        result = result.and(write!(f, "Relative end: "));

        match self {
            Self::Finite(RelativeFiniteBound { offset, inclusivity }) => {
                result = result.and(write!(f, "{offset} ({inclusivity})"));
            },
            Self::InfiniteFuture => {
                result = result.and(write!(f, "Infinite future"));
            },
        }

        result
    }
}

impl From<RelativeFiniteBound> for RelativeEndBound {
    fn from(value: RelativeFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Bound<Duration>> for RelativeEndBound {
    fn from(bound: Bound<Duration>) -> Self {
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

/// Swaps a relative start bound with a relative end bound
pub fn swap_relative_bounds(start: &mut RelativeStartBound, end: &mut RelativeEndBound) {
    // We temporarily reborrow start and end for the match arms so that when a pattern matches, they move out of their
    // temporary scope and we can use the original mutable references without guard patterns shenanigans.
    // When destructuring, however, the scope of the reborrowed value extends up to where it is used within the body,
    // So we always finish our business with the reborrowed values first before accessing the original ones.
    match (&mut *start, &mut *end) {
        (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => {},
        (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(finite_end)) => {
            *start = RelativeStartBound::Finite(*finite_end);
            *end = RelativeEndBound::InfiniteFuture;
        },
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::InfiniteFuture) => {
            *end = RelativeEndBound::Finite(*finite_start);
            *start = RelativeStartBound::InfinitePast;
        },
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
            std::mem::swap(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeBoundsCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same offset but don't have only inclusive bound inclusivities
    SameOffsetButNotDoublyInclusive,
}

impl Display for RelativeBoundsCheckForIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StartPastEnd => write!(f, "Start bound is past the end bound"),
            Self::SameOffsetButNotDoublyInclusive => write!(
                f,
                "Both bounds are on the same offset but don't have only inclusive bound inclusivities"
            ),
        }
    }
}

impl Error for RelativeBoundsCheckForIntervalCreationError {}

/// Checks if the given start and end bound are ready for creating an interval
///
/// # Errors
///
/// If the start bound is past the end bound,
/// it returns [`StartPastEnd`](RelativeBoundsCheckForIntervalCreationError::StartPastEnd).
///
/// If both bounds are at the same time, but one of them has an exclusive bound inclusivity, it returns
/// [`SameOffsetButNotDoublyInclusive`](RelativeBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive).
pub fn check_relative_bounds_for_interval_creation(
    start: &RelativeStartBound,
    end: &RelativeEndBound,
) -> Result<(), RelativeBoundsCheckForIntervalCreationError> {
    match (start, end) {
        (RelativeStartBound::InfinitePast, _) | (_, RelativeEndBound::InfiniteFuture) => Ok(()),
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
            match finite_start.offset().cmp(&finite_end.offset()) {
                Ordering::Less => Ok(()),
                Ordering::Equal => {
                    if finite_start.inclusivity() == BoundInclusivity::Inclusive
                        && finite_end.inclusivity() == BoundInclusivity::Inclusive
                    {
                        Ok(())
                    } else {
                        Err(RelativeBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
                    }
                },
                Ordering::Greater => Err(RelativeBoundsCheckForIntervalCreationError::StartPastEnd),
            }
        },
    }
}

/// Prepares a start and end bound for being used for creating an interval
///
/// If some problems are present, see [`check_relative_bounds_for_interval_creation`], it resolves them automatically
/// by modifying the passed mutable references for the start and end bound.
pub fn prepare_relative_bounds_for_interval_creation(
    start_mut: &mut RelativeStartBound,
    end_mut: &mut RelativeEndBound,
) {
    match check_relative_bounds_for_interval_creation(start_mut, end_mut) {
        Ok(()) => {},
        Err(RelativeBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_relative_bounds(start_mut, end_mut);
        },
        Err(RelativeBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive) => {
            if let RelativeStartBound::Finite(finite_start_mut) = start_mut {
                finite_start_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            if let RelativeEndBound::Finite(finite_end_mut) = end_mut {
                finite_end_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }
        },
    }
}

/// Enum for relative start and end bounds
#[derive(Debug, Clone, Copy)]
pub enum RelativeBound {
    Start(RelativeStartBound),
    End(RelativeEndBound),
}

impl RelativeBound {
    /// Returns whether [`RelativeBound`] is of the [`Start`](RelativeBound::Start) variant
    #[must_use]
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    /// Returns whether [`RelativeBound`] is of the [`End`](RelativeBound::End) variant
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    /// Returns the content of the [`Start`](RelativeBound::Start) variant
    #[must_use]
    pub fn start(self) -> Option<RelativeStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](RelativeBound::End) variant
    #[must_use]
    pub fn end(self) -> Option<RelativeEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the opposite bound type with the opposite inclusivity
    ///
    /// Returns [`None`] if the bound is infinite.
    #[must_use]
    pub fn opposite(&self) -> Option<Self> {
        match self {
            Self::Start(start) => start.opposite().map(Self::End),
            Self::End(end) => end.opposite().map(Self::Start),
        }
    }
}

impl PartialEq for RelativeBound {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RelativeBound::Start(og_start), RelativeBound::Start(other_start)) => og_start.eq(other_start),
            (RelativeBound::End(og_end), RelativeBound::End(other_end)) => og_end.eq(other_end),
            (RelativeBound::Start(start), RelativeBound::End(end))
            | (RelativeBound::End(end), RelativeBound::Start(start)) => start.eq(end),
        }
    }
}

impl Eq for RelativeBound {}

impl PartialOrd for RelativeBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (RelativeBound::Start(og_start), RelativeBound::Start(other_start)) => og_start.cmp(other_start),
            (RelativeBound::End(og_end), RelativeBound::End(other_end)) => og_end.cmp(other_end),
            (RelativeBound::Start(og_start), RelativeBound::End(other_end)) => og_start.partial_cmp(other_end).unwrap(),
            (RelativeBound::End(og_end), RelativeBound::Start(other_start)) => og_end.partial_cmp(other_start).unwrap(),
        }
    }
}

impl Hash for RelativeBound {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Start(RelativeStartBound::InfinitePast) => {
                RelativeStartBound::InfinitePast.hash(state);
            },
            Self::Start(RelativeStartBound::Finite(finite)) | Self::End(RelativeEndBound::Finite(finite)) => {
                finite.hash(state);
            },
            Self::End(RelativeEndBound::InfiniteFuture) => {
                RelativeEndBound::InfiniteFuture.hash(state);
            },
        }
    }
}

impl From<RelativeStartBound> for RelativeBound {
    fn from(value: RelativeStartBound) -> Self {
        RelativeBound::Start(value)
    }
}

impl From<RelativeEndBound> for RelativeBound {
    fn from(value: RelativeEndBound) -> Self {
        RelativeBound::End(value)
    }
}

/// Represents something that has **non-empty** relative bounds
pub trait HasRelativeBounds {
    /// Returns the relative bounds
    #[must_use]
    fn rel_bounds(&self) -> RelativeBounds;

    /// Returns the relative start bound
    #[must_use]
    fn rel_start(&self) -> RelativeStartBound;

    /// Returns the relative end bound
    #[must_use]
    fn rel_end(&self) -> RelativeEndBound;
}

/// Represents something that has possibly empty relative bounds
pub trait HasEmptiableRelativeBounds {
    /// Returns the [`EmptiableRelativeBounds`] of self
    #[must_use]
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds;

    /// Returns an [`Option`] of [the relative start bound](RelativeStartBound)
    #[must_use]
    fn partial_rel_start(&self) -> Option<RelativeStartBound>;

    /// Returns an [`Option`] of [the relative end bound](RelativeEndBound)
    #[must_use]
    fn partial_rel_end(&self) -> Option<RelativeEndBound>;
}

/// All implementors of [`HasRelativeBounds`] implement [`HasEmptiableRelativeBounds`].
/// This could change in the future to separate emptiable from non-emptiable bounds.
impl<T> HasEmptiableRelativeBounds for T
where
    T: HasRelativeBounds,
{
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        EmptiableRelativeBounds::Bound(self.rel_bounds())
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        Some(self.rel_start())
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        Some(self.rel_end())
    }
}

/// Bounds of a non-empty relative interval
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativeBounds {
    start: RelativeStartBound,
    end: RelativeEndBound,
}

impl RelativeBounds {
    /// Creates an instance of relative bound without checking if the bounds are in order
    #[must_use]
    pub fn unchecked_new(start: RelativeStartBound, end: RelativeEndBound) -> Self {
        RelativeBounds { start, end }
    }

    /// Creates a new instance of relative bounds
    ///
    /// Uses [`prepare_relative_bounds_for_interval_creation`] under the hood for making the bounds safe to use.
    #[must_use]
    pub fn new(mut start: RelativeStartBound, mut end: RelativeEndBound) -> Self {
        prepare_relative_bounds_for_interval_creation(&mut start, &mut end);
        Self::unchecked_new(start, end)
    }

    /// Returns the relative start bound
    #[must_use]
    pub fn start(&self) -> &RelativeStartBound {
        &self.start
    }

    /// Returns the relative end bound
    #[must_use]
    pub fn end(&self) -> &RelativeEndBound {
        &self.end
    }

    /// Sets the relative start bound without checking if it is in order
    pub fn unchecked_set_start(&mut self, start: RelativeStartBound) {
        self.start = start;
    }

    /// Sets the relative end bound without checking if it is in order
    pub fn unchecked_set_end(&mut self, end: RelativeEndBound) {
        self.end = end;
    }

    /// Sets the relative start bound
    ///
    /// Returns whether the change was successful: the new start must be in chronological order and if it is equal
    /// to the end bound, both bounds must be inclusive.
    pub fn set_start(&mut self, start: RelativeStartBound) -> bool {
        if start.partial_cmp(self.end()).is_none_or(Ordering::is_gt) {
            return false;
        }

        self.unchecked_set_start(start);
        true
    }

    /// Sets the relative end bound
    ///
    /// Returns whether the change was successful: the new end must be in chronological order and if it is equal
    /// to the start bound, both bounds must be inclusive.
    pub fn set_end(&mut self, end: RelativeEndBound) -> bool {
        if self.start().partial_cmp(&end).is_none_or(Ordering::is_gt) {
            return false;
        }

        self.unchecked_set_end(end);
        true
    }

    /// Compares two [`RelativeBounds`], but if they have the same start, order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// length don't match too.
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match self.cmp(other) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.end.cmp(&other.end).reverse(),
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl Interval for RelativeBounds {}

impl HasRelativeBounds for RelativeBounds {
    fn rel_bounds(&self) -> RelativeBounds {
        self.clone()
    }

    fn rel_start(&self) -> RelativeStartBound {
        *self.start()
    }

    fn rel_end(&self) -> RelativeEndBound {
        *self.end()
    }
}

impl HasDuration for RelativeBounds {
    fn duration(&self) -> IntervalDuration {
        match (self.start(), self.end()) {
            (RelativeStartBound::InfinitePast, _) | (_, RelativeEndBound::InfiniteFuture) => IntervalDuration::Infinite,
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
                IntervalDuration::Finite(
                    finite_end
                        .offset()
                        .checked_sub(&finite_start.offset())
                        .unwrap_or(Duration::zero()),
                )
            },
        }
    }
}

impl HasOpenness for RelativeBounds {
    fn openness(&self) -> Openness {
        match (self.start(), self.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => Openness::Unbounded,
            (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(_))
            | (RelativeStartBound::Finite(_), RelativeEndBound::InfiniteFuture) => Openness::HalfBounded,
            (RelativeStartBound::Finite(_), RelativeEndBound::Finite(_)) => Openness::Bounded,
        }
    }
}

impl HasRelativity for RelativeBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl PartialOrd for RelativeBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        // using the comparison of self.end and other.end as a way to disambiguate when the two starts are equal
        // leads to side-effects, like when we store absolute bounds inside a BTreeSet, then if we use `range()`,
        // one can be considered out of the range when it shouldn't.
        self.start.cmp(&other.start)
    }
}

impl Display for RelativeBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());

        result = result.and(write!(f, "Relative bounds: "));

        match self.start() {
            RelativeStartBound::Finite(RelativeFiniteBound { offset, inclusivity }) => {
                result = result.and(write!(f, "{offset} ({inclusivity})"));
            },
            RelativeStartBound::InfinitePast => {
                result = result.and(write!(f, "Infinite past"));
            },
        }

        result = result.and(write!(f, " to "));

        match self.end() {
            RelativeEndBound::Finite(RelativeFiniteBound { offset, inclusivity }) => {
                result = result.and(write!(f, "{offset} ({inclusivity})"));
            },
            RelativeEndBound::InfiniteFuture => {
                result = result.and(write!(f, "Infinite future"));
            },
        }

        result
    }
}

impl<R> From<R> for RelativeBounds
where
    R: RangeBounds<Duration>,
{
    fn from(range: R) -> Self {
        RelativeBounds::new(
            RelativeStartBound::from(range.start_bound().cloned()),
            RelativeEndBound::from(range.end_bound().cloned()),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeBoundsFromEmptiableRelativeBoundsError {
    EmptyVariant,
}

impl Display for RelativeBoundsFromEmptiableRelativeBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyVariant => write!(f, "Provided EmptiableRelativeBounds was empty"),
        }
    }
}

impl Error for RelativeBoundsFromEmptiableRelativeBoundsError {}

impl TryFrom<EmptiableRelativeBounds> for RelativeBounds {
    type Error = RelativeBoundsFromEmptiableRelativeBoundsError;

    fn try_from(value: EmptiableRelativeBounds) -> Result<Self, Self::Error> {
        match value {
            EmptiableRelativeBounds::Empty => Err(RelativeBoundsFromEmptiableRelativeBoundsError::EmptyVariant),
            EmptiableRelativeBounds::Bound(bounds) => Ok(bounds),
        }
    }
}

/// Bounds of a relative interval
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum EmptiableRelativeBounds {
    Empty,
    Bound(RelativeBounds),
}

impl EmptiableRelativeBounds {
    /// Converts the content of the [`Bound`](EmptiableRelativeBounds::Bound) variant into an [`Option`]
    #[must_use]
    pub fn bound(self) -> Option<RelativeBounds> {
        match self {
            EmptiableRelativeBounds::Empty => None,
            EmptiableRelativeBounds::Bound(bound) => Some(bound),
        }
    }

    /// Compares two [`EmptiableRelativeBounds`], but if they have the same start, order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// length don't match too.
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableRelativeBounds::Bound(og_rel_bounds), EmptiableRelativeBounds::Bound(other_rel_bounds)) => {
                og_rel_bounds.ord_by_start_and_inv_length(other_rel_bounds)
            },
            _ => self.cmp(other),
        }
    }
}

impl Interval for EmptiableRelativeBounds {}

impl HasEmptiableRelativeBounds for EmptiableRelativeBounds {
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        self.clone()
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.start()),
        }
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.end()),
        }
    }
}

impl Emptiable for EmptiableRelativeBounds {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableRelativeBounds {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(Duration::zero()),
        }
    }
}

impl HasOpenness for EmptiableRelativeBounds {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableRelativeBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl PartialOrd for EmptiableRelativeBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableRelativeBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableRelativeBounds::Empty, EmptiableRelativeBounds::Empty) => Ordering::Equal,
            (EmptiableRelativeBounds::Empty, EmptiableRelativeBounds::Bound(_)) => Ordering::Less,
            (EmptiableRelativeBounds::Bound(_), EmptiableRelativeBounds::Empty) => Ordering::Greater,
            (EmptiableRelativeBounds::Bound(og_rel_bounds), EmptiableRelativeBounds::Bound(other_rel_bounds)) => {
                og_rel_bounds.cmp(other_rel_bounds)
            },
        }
    }
}

impl Display for EmptiableRelativeBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "Empty relative interval bounds"),
            Self::Bound(bounds) => write!(f, "{bounds}"),
        }
    }
}

impl From<RelativeBounds> for EmptiableRelativeBounds {
    fn from(value: RelativeBounds) -> Self {
        EmptiableRelativeBounds::Bound(value)
    }
}

/// A bounded relative interval
///
/// An interval set with relative time, with a defined start and end
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoundedRelativeInterval {
    offset: Duration,
    length: Duration,
    from_inclusivity: BoundInclusivity,
    to_inclusivity: BoundInclusivity,
}

impl BoundedRelativeInterval {
    /// Creates a new instance of a bounded relative interval
    #[must_use]
    pub fn new(offset: Duration, length: Duration) -> Self {
        BoundedRelativeInterval {
            offset,
            length,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a bounded relative interval with given inclusivity for the bounds
    ///
    /// If the length is 0, then the inclusivities will be set to inclusive.
    #[must_use]
    pub fn new_with_inclusivity(
        offset: Duration,
        start_inclusivity: BoundInclusivity,
        length: Duration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        if length.is_zero() {
            return Self::new(offset, length);
        }

        BoundedRelativeInterval {
            offset,
            length,
            from_inclusivity: start_inclusivity,
            to_inclusivity: end_inclusivity,
        }
    }

    /// Returns the offset of the interval
    #[must_use]
    pub fn offset(&self) -> Duration {
        self.offset
    }

    /// Returns the length of the interval
    #[must_use]
    pub fn length(&self) -> Duration {
        self.length
    }

    /// Returns the inclusivity of the start bound
    #[must_use]
    pub fn from_inclusivity(&self) -> BoundInclusivity {
        self.from_inclusivity
    }

    /// Returns the inclusivity of the end bound
    #[must_use]
    pub fn to_inclusivity(&self) -> BoundInclusivity {
        self.to_inclusivity
    }

    /// Sets the offset of the interval
    pub fn set_offset(&mut self, new_offset: Duration) {
        self.offset = new_offset;
    }

    /// Sets the length of the interval
    ///
    /// Returns whether the operation is successful: if the length is 0, then the bound inclusivities must be inclusive.
    pub fn set_length(&mut self, new_length: Duration) -> bool {
        if new_length.is_zero()
            && (self.from_inclusivity != BoundInclusivity::Inclusive
                || self.to_inclusivity != BoundInclusivity::Inclusive)
        {
            return false;
        }

        self.length = new_length;
        true
    }

    /// Sets the inclusivity of the start bound
    ///
    /// Returns whether the operation is successful: if the length is 0, then the bound inclusivities must be inclusive.
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.length.is_zero()
            && (self.from_inclusivity != BoundInclusivity::Inclusive
                || self.to_inclusivity != BoundInclusivity::Inclusive)
        {
            return false;
        }

        self.from_inclusivity = new_inclusivity;
        true
    }

    /// Sets the inclusivity of the end bound
    ///
    /// Returns whether the operation is successful: if the length is 0, then the bound inclusivities must be inclusive.
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.length.is_zero()
            && (self.from_inclusivity != BoundInclusivity::Inclusive
                || self.to_inclusivity != BoundInclusivity::Inclusive)
        {
            return false;
        }

        self.to_inclusivity = new_inclusivity;
        true
    }
}

impl Interval for BoundedRelativeInterval {}

impl HasOpenness for BoundedRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::Bounded
    }
}

impl HasRelativity for BoundedRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for BoundedRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(self.length)
    }
}

impl HasRelativeBounds for BoundedRelativeInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            self.offset,
            self.from_inclusivity,
        ))
    }

    fn rel_end(&self) -> RelativeEndBound {
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            self.offset + self.length,
            self.to_inclusivity,
        ))
    }
}

impl From<(Duration, Duration)> for BoundedRelativeInterval {
    fn from((from, to): (Duration, Duration)) -> Self {
        BoundedRelativeInterval::new(from, to)
    }
}

impl From<((Duration, BoundInclusivity), (Duration, BoundInclusivity))> for BoundedRelativeInterval {
    fn from(
        ((from, from_inclusivity), (to, to_inclusivity)): ((Duration, BoundInclusivity), (Duration, BoundInclusivity)),
    ) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity)
    }
}

impl From<((Duration, bool), (Duration, bool))> for BoundedRelativeInterval {
    fn from(((from, is_from_inclusive), (to, is_to_inclusive)): ((Duration, bool), (Duration, bool))) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            from,
            if is_from_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
            to,
            if is_to_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
        )
    }
}

impl From<Range<Duration>> for BoundedRelativeInterval {
    fn from(range: Range<Duration>) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<Duration>> for BoundedRelativeInterval {
    fn from(range: RangeInclusive<Duration>) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedRelativeIntervalFromRelativeBoundsError {
    NotBoundedInterval,
}

impl Display for BoundedRelativeIntervalFromRelativeBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotBoundedInterval => write!(f, "Not a bounded interval"),
        }
    }
}

impl Error for BoundedRelativeIntervalFromRelativeBoundsError {}

impl TryFrom<RelativeBounds> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalFromRelativeBoundsError;

    fn try_from(value: RelativeBounds) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
                Ok(BoundedRelativeInterval::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity(),
                    finite_end.offset(),
                    finite_end.inclusivity(),
                ))
            },
            _ => Err(Self::Error::NotBoundedInterval),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedRelativeIntervalFromRelativeIntervalError {
    WrongVariant,
}

impl Display for BoundedRelativeIntervalFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for BoundedRelativeIntervalFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Bounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// A half-bounded relative interval
///
/// An interval set with relative time, has a relative reference time (offset) and an opening direction.
/// Infinite duration.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub struct HalfBoundedRelativeInterval {
    offset: Duration,
    opening_direction: OpeningDirection,
    reference_time_inclusivity: BoundInclusivity,
}

impl HalfBoundedRelativeInterval {
    /// Creates a new instance of a half-bounded relative interval
    #[must_use]
    pub fn new(offset: Duration, opening_direction: OpeningDirection) -> Self {
        HalfBoundedRelativeInterval {
            offset,
            opening_direction,
            reference_time_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a half-bounded relative interval with given inclusivity for the bound
    #[must_use]
    pub fn new_with_inclusivity(
        offset: Duration,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfBoundedRelativeInterval {
            offset,
            opening_direction,
            reference_time_inclusivity,
        }
    }

    /// Returns the offset of the interval
    #[must_use]
    pub fn offset(&self) -> Duration {
        self.offset
    }

    /// Returns the opening direction of the interval
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference time
    #[must_use]
    pub fn reference_time_inclusivity(&self) -> BoundInclusivity {
        self.reference_time_inclusivity
    }

    /// Sets the offset of the interval
    pub fn set_offset(&mut self, new_offset: Duration) {
        self.offset = new_offset;
    }

    /// Sets the inclusivity of the reference time
    pub fn set_reference_time_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_time_inclusivity = new_inclusivity;
    }

    /// Sets the opening direction of the interval
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        self.opening_direction = new_opening_direction;
    }
}

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

impl HasRelativeBounds for HalfBoundedRelativeInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        match self.opening_direction {
            OpeningDirection::ToPast => RelativeStartBound::InfinitePast,
            OpeningDirection::ToFuture => RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                self.offset,
                self.reference_time_inclusivity,
            )),
        }
    }

    fn rel_end(&self) -> RelativeEndBound {
        match self.opening_direction {
            OpeningDirection::ToPast => RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                self.offset,
                self.reference_time_inclusivity,
            )),
            OpeningDirection::ToFuture => RelativeEndBound::InfiniteFuture,
        }
    }
}

impl From<(Duration, OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from((offset, direction): (Duration, OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new(offset, direction)
    }
}

impl From<(Duration, bool)> for HalfBoundedRelativeInterval {
    fn from((offset, goes_to_future): (Duration, bool)) -> Self {
        HalfBoundedRelativeInterval::new(
            offset,
            if goes_to_future {
                OpeningDirection::ToFuture
            } else {
                OpeningDirection::ToPast
            },
        )
    }
}

impl From<((Duration, BoundInclusivity), OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from(((offset, inclusivity), direction): ((Duration, BoundInclusivity), OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(offset, inclusivity, direction)
    }
}

impl From<((Duration, BoundInclusivity), bool)> for HalfBoundedRelativeInterval {
    fn from(((offset, inclusivity), goes_to_future): ((Duration, BoundInclusivity), bool)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            offset,
            inclusivity,
            if goes_to_future {
                OpeningDirection::ToFuture
            } else {
                OpeningDirection::ToPast
            },
        )
    }
}

impl From<((Duration, bool), OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from(((offset, is_inclusive), direction): ((Duration, bool), OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            offset,
            if is_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
            direction,
        )
    }
}

impl From<((Duration, bool), bool)> for HalfBoundedRelativeInterval {
    fn from(((offset, is_inclusive), goes_to_future): ((Duration, bool), bool)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            offset,
            if is_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
            if goes_to_future {
                OpeningDirection::ToFuture
            } else {
                OpeningDirection::ToPast
            },
        )
    }
}

impl From<RangeFrom<Duration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeFrom<Duration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<Duration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeTo<Duration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<Duration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeToInclusive<Duration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedRelativeIntervalFromRelativeBoundsError {
    NotHalfBoundedInterval,
}

impl Display for HalfBoundedRelativeIntervalFromRelativeBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotHalfBoundedInterval => write!(f, "Not a half-bounded interval"),
        }
    }
}

impl Error for HalfBoundedRelativeIntervalFromRelativeBoundsError {}

impl TryFrom<RelativeBounds> for HalfBoundedRelativeInterval {
    type Error = HalfBoundedRelativeIntervalFromRelativeBoundsError;

    fn try_from(value: RelativeBounds) -> Result<Self, Self::Error> {
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
            _ => Err(Self::Error::NotHalfBoundedInterval),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedRelativeIntervalFromRelativeIntervalError {
    WrongVariant,
}

impl Display for HalfBoundedRelativeIntervalFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for HalfBoundedRelativeIntervalFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for HalfBoundedRelativeInterval {
    type Error = HalfBoundedRelativeIntervalFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::HalfBounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// Represents any relative interval, including empty and unbounded interval
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum RelativeInterval {
    Bounded(BoundedRelativeInterval),
    HalfBounded(HalfBoundedRelativeInterval),
    Unbounded(UnboundedInterval),
    Empty(EmptyInterval),
}

impl RelativeInterval {
    /// Compares two [`RelativeInterval`]s, but if they have the same start, order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// length don't match too.
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.emptiable_rel_bounds()
            .ord_by_start_and_inv_length(&other.emptiable_rel_bounds())
    }
}

impl Interval for RelativeInterval {}

impl HasDuration for RelativeInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
            Self::Empty(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for RelativeInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
            Self::Empty(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for RelativeInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
            Self::Empty(interval) => interval.openness(),
        }
    }
}

impl HasEmptiableRelativeBounds for RelativeInterval {
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        match self {
            Self::Bounded(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::HalfBounded(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::Unbounded(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::Empty(interval) => interval.emptiable_rel_bounds(),
        }
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Bounded(interval) => interval.partial_rel_start(),
            Self::HalfBounded(interval) => interval.partial_rel_start(),
            Self::Unbounded(interval) => interval.partial_rel_start(),
            Self::Empty(interval) => interval.partial_rel_start(),
        }
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Bounded(interval) => interval.partial_rel_end(),
            Self::HalfBounded(interval) => interval.partial_rel_end(),
            Self::Unbounded(interval) => interval.partial_rel_end(),
            Self::Empty(interval) => interval.partial_rel_end(),
        }
    }
}

impl Emptiable for RelativeInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for RelativeInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_rel_bounds().cmp(&other.emptiable_rel_bounds())
    }
}

impl From<BoundedRelativeInterval> for RelativeInterval {
    fn from(value: BoundedRelativeInterval) -> Self {
        RelativeInterval::Bounded(value)
    }
}

impl From<HalfBoundedRelativeInterval> for RelativeInterval {
    fn from(value: HalfBoundedRelativeInterval) -> Self {
        RelativeInterval::HalfBounded(value)
    }
}

impl From<UnboundedInterval> for RelativeInterval {
    fn from(value: UnboundedInterval) -> Self {
        RelativeInterval::Unbounded(value)
    }
}

impl From<EmptyInterval> for RelativeInterval {
    fn from(value: EmptyInterval) -> Self {
        RelativeInterval::Empty(value)
    }
}

impl From<RelativeBounds> for RelativeInterval {
    fn from(value: RelativeBounds) -> Self {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.rel_start(), value.rel_end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => RelativeInterval::Unbounded(UnboundedInterval),
            (StartB::InfinitePast, EndB::Finite(RelativeFiniteBound { offset, inclusivity })) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(RelativeFiniteBound { offset, inclusivity }), EndB::InfiniteFuture) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (
                StartB::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                }),
                EndB::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                }),
            ) => RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset - start_offset,
                end_inclusivity,
            )),
        }
    }
}

impl From<EmptiableRelativeBounds> for RelativeInterval {
    fn from(value: EmptiableRelativeBounds) -> Self {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.partial_rel_start(), value.partial_rel_end()) {
            (None, _) | (_, None) => RelativeInterval::Empty(EmptyInterval),
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => RelativeInterval::Unbounded(UnboundedInterval),
            (Some(StartB::InfinitePast), Some(EndB::Finite(RelativeFiniteBound { offset, inclusivity }))) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (Some(StartB::Finite(RelativeFiniteBound { offset, inclusivity })), Some(EndB::InfiniteFuture)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (
                Some(StartB::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                })),
                Some(EndB::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                })),
            ) => RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset - start_offset,
                end_inclusivity,
            )),
        }
    }
}

impl From<(Option<Duration>, Option<Duration>)> for RelativeInterval {
    fn from((from_opt, to_opt): (Option<Duration>, Option<Duration>)) -> Self {
        match (from_opt, to_opt) {
            (Some(from), Some(to)) => RelativeInterval::Bounded(BoundedRelativeInterval::new(from, to)),
            (Some(from), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl
    From<(
        Option<(Duration, BoundInclusivity)>,
        Option<(Duration, BoundInclusivity)>,
    )> for RelativeInterval
{
    fn from(
        (from_opt, to_opt): (
            Option<(Duration, BoundInclusivity)>,
            Option<(Duration, BoundInclusivity)>,
        ),
    ) -> Self {
        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => RelativeInterval::Bounded(
                BoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<(Option<(Duration, bool)>, Option<(Duration, bool)>)> for RelativeInterval {
    fn from((from_opt, to_opt): (Option<(Duration, bool)>, Option<(Duration, bool)>)) -> Self {
        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    if is_from_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                    to,
                    if is_to_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    if is_from_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    to,
                    if is_to_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<(bool, Option<Duration>, Option<Duration>)> for RelativeInterval {
    fn from((is_empty, from_opt, to_opt): (bool, Option<Duration>, Option<Duration>)) -> Self {
        if is_empty {
            return RelativeInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some(from), Some(to)) => RelativeInterval::Bounded(BoundedRelativeInterval::new(from, to)),
            (Some(from), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl
    From<(
        bool,
        Option<(Duration, BoundInclusivity)>,
        Option<(Duration, BoundInclusivity)>,
    )> for RelativeInterval
{
    fn from(
        (is_empty, from_opt, to_opt): (
            bool,
            Option<(Duration, BoundInclusivity)>,
            Option<(Duration, BoundInclusivity)>,
        ),
    ) -> Self {
        if is_empty {
            return RelativeInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => RelativeInterval::Bounded(
                BoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<(bool, Option<(Duration, bool)>, Option<(Duration, bool)>)> for RelativeInterval {
    fn from((is_empty, from_opt, to_opt): (bool, Option<(Duration, bool)>, Option<(Duration, bool)>)) -> Self {
        if is_empty {
            return RelativeInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    if is_from_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                    to,
                    if is_to_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    if is_from_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    to,
                    if is_to_inclusive {
                        BoundInclusivity::Inclusive
                    } else {
                        BoundInclusivity::Exclusive
                    },
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

// Unfortunately can't use impl<R: RangeBounds> From<R> as it's conflicting with the core implementation of From
impl From<(Bound<Duration>, Bound<Duration>)> for RelativeInterval {
    fn from((start_bound, end_bound): (Bound<Duration>, Bound<Duration>)) -> Self {
        match (start_bound, end_bound) {
            (Bound::Included(from), Bound::Included(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Included(from), Bound::Excluded(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Included(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Excluded(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Included(from), Bound::Unbounded) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Excluded(from), Bound::Unbounded) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Unbounded, Bound::Included(from)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Excluded(from)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Unbounded) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<Range<Duration>> for RelativeInterval {
    fn from(value: Range<Duration>) -> Self {
        RelativeInterval::Bounded(BoundedRelativeInterval::from(value))
    }
}

impl From<RangeInclusive<Duration>> for RelativeInterval {
    fn from(value: RangeInclusive<Duration>) -> Self {
        RelativeInterval::Bounded(BoundedRelativeInterval::from(value))
    }
}

impl From<RangeFrom<Duration>> for RelativeInterval {
    fn from(value: RangeFrom<Duration>) -> Self {
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::from(value))
    }
}

impl From<RangeTo<Duration>> for RelativeInterval {
    fn from(value: RangeTo<Duration>) -> Self {
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::from(value))
    }
}

impl From<RangeToInclusive<Duration>> for RelativeInterval {
    fn from(value: RangeToInclusive<Duration>) -> Self {
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::from(value))
    }
}

impl From<RangeFull> for RelativeInterval {
    fn from(_value: RangeFull) -> Self {
        RelativeInterval::Unbounded(UnboundedInterval)
    }
}

impl From<()> for RelativeInterval {
    fn from(_value: ()) -> Self {
        RelativeInterval::Empty(EmptyInterval)
    }
}

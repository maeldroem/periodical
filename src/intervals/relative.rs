//! Relative intervals

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use chrono::Duration;

use crate::intervals::meta::Interval;

use super::meta::{BoundInclusivity, Duration as IntervalDuration, OpeningDirection, Openness, Relativity};
use super::prelude::*;
use super::special::{EmptyInterval, OpenInterval};

/// A relative finite bound
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

impl Display for RelativeFiniteBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Relative finite bound with offset {} ({})",
            self.offset, self.inclusivity
        )
    }
}

/// A relative start interval bound, including [inclusivity](BoundInclusivity)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeStartBound {
    Finite(RelativeFiniteBound),
    InfinitePast,
}

impl RelativeStartBound {
    /// Returns the offset of the bound, if finite
    #[must_use]
    pub fn offset(&self) -> Option<Duration> {
        if let Self::Finite(RelativeFiniteBound { offset, .. }) = self {
            return Some(*offset);
        }

        None
    }

    /// Returns the inclusivity of the bound, if finite
    #[must_use]
    pub fn inclusivity(&self) -> Option<BoundInclusivity> {
        if let Self::Finite(RelativeFiniteBound { inclusivity, .. }) = self {
            return Some(*inclusivity);
        }

        None
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
            (RelativeStartBound::InfinitePast, _) => Ordering::Less,
            (_, RelativeStartBound::InfinitePast) => Ordering::Greater,
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
            ) => {
                match start_offset.cmp(end_offset) {
                    Ordering::Less => Some(Ordering::Less),
                    Ordering::Greater => Some(Ordering::Greater),
                    Ordering::Equal => match (start_inclusivity, end_inclusivity) {
                        (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => Some(Ordering::Equal),
                        _ => None, // If the offsets are equal, anything other than double inclusive bounds is invalid
                    },
                }
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

/// A relative end interval bound, including [inclusivity](BoundInclusivity)
///
/// This contains an offset from the reference time to the end bound, not the length of the relative interval.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeEndBound {
    Finite(RelativeFiniteBound),
    InfiniteFuture,
}

impl RelativeEndBound {
    /// Returns the offset of the bound, if finite
    #[must_use]
    pub fn offset(&self) -> Option<Duration> {
        if let Self::Finite(RelativeFiniteBound { offset, .. }) = self {
            return Some(*offset);
        }

        None
    }

    /// Returns the inclusivity of the bound, if finite
    #[must_use]
    pub fn inclusivity(&self) -> Option<BoundInclusivity> {
        if let Self::Finite(RelativeFiniteBound { inclusivity, .. }) = self {
            return Some(*inclusivity);
        }

        None
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
            (RelativeEndBound::InfiniteFuture, _) => Ordering::Greater,
            (_, RelativeEndBound::InfiniteFuture) => Ordering::Less,
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
        other.partial_cmp(self).map(Ordering::reverse)
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
    /// If the given bounds are not in chronological order, they are swapped.
    /// If their [partial comparison](PartialOrd) resulted in [`None`], meaning they had the same offsets
    /// but inclusivities other than inclusive for both,
    /// we set their inclusivities to [`Inclusive`](BoundInclusivity::Inclusive).
    #[must_use]
    pub fn new(mut start: RelativeStartBound, mut end: RelativeEndBound) -> Self {
        match start.partial_cmp(&end) {
            None => {
                if let RelativeStartBound::Finite(ref mut finite_start) = start {
                    finite_start.set_inclusivity(BoundInclusivity::default());
                }

                if let RelativeEndBound::Finite(ref mut finite_end) = end {
                    finite_end.set_inclusivity(BoundInclusivity::default());
                }

                match start.partial_cmp(&end) {
                    Some(Ordering::Equal | Ordering::Less) => Self::unchecked_new(start, end),
                    Some(Ordering::Greater) => {
                        swap_relative_bounds(&mut start, &mut end);
                        Self::unchecked_new(start, end)
                    },
                    None => unimplemented!(
                        "Something went wrong when instantiating `RelativeBounds` with bounds that partially compared to `None`"
                    ),
                }
            },
            Some(Ordering::Equal | Ordering::Less) => Self::unchecked_new(start, end),
            Some(Ordering::Greater) => {
                // If the start time is after the end time, swap the two to preserve order
                swap_relative_bounds(&mut start, &mut end);
                Self::unchecked_new(start, end)
            },
        }
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
        if self.start().partial_cmp(self.end()).is_none_or(Ordering::is_gt) {
            return false;
        }

        self.unchecked_set_end(end);
        true
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeBoundsConversionErr {
    EmptyVariant,
}

impl Display for RelativeBoundsConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyVariant => write!(f, "Provided EmptiableRelativeBounds was empty"),
        }
    }
}

impl Error for RelativeBoundsConversionErr {}

impl TryFrom<EmptiableRelativeBounds> for RelativeBounds {
    type Error = RelativeBoundsConversionErr;

    fn try_from(value: EmptiableRelativeBounds) -> Result<Self, Self::Error> {
        match value {
            EmptiableRelativeBounds::Empty => Err(RelativeBoundsConversionErr::EmptyVariant),
            EmptiableRelativeBounds::Bound(bounds) => Ok(bounds),
        }
    }
}

/// Bounds of a relative interval
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EmptiableRelativeBounds {
    Empty,
    Bound(RelativeBounds),
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

impl From<RelativeBounds> for EmptiableRelativeBounds {
    fn from(value: RelativeBounds) -> Self {
        EmptiableRelativeBounds::Bound(value)
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

/// A closed relative interval
///
/// An interval set with relative time, with a defined start and end
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClosedRelativeInterval {
    pub(super) offset: Duration,
    pub(super) length: Duration,
    pub(super) from_inclusivity: BoundInclusivity,
    pub(super) to_inclusivity: BoundInclusivity,
}

impl ClosedRelativeInterval {
    /// Creates a new instance of a closed relative interval
    #[must_use]
    pub fn new(offset: Duration, length: Duration) -> Self {
        ClosedRelativeInterval {
            offset,
            length,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a closed relative interval with given inclusivity for the bounds
    ///
    /// If the length is 0, then the inclusivities will be set to inclusive.
    #[must_use]
    pub fn with_inclusivity(
        offset: Duration,
        start_inclusivity: BoundInclusivity,
        length: Duration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
        if length.is_zero() {
            return Self::new(offset, length);
        }

        ClosedRelativeInterval {
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

impl Interval for ClosedRelativeInterval {}

impl HasOpenness for ClosedRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::Closed
    }
}

impl HasRelativity for ClosedRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for ClosedRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(self.length)
    }
}

impl HasRelativeBounds for ClosedRelativeInterval {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClosedRelativeIntervalConversionErr {
    WrongVariant,
}

impl Display for ClosedRelativeIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for ClosedRelativeIntervalConversionErr {}

impl TryFrom<RelativeInterval> for ClosedRelativeInterval {
    type Error = ClosedRelativeIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Closed(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// A half-open relative interval
///
/// An interval set with relative time, has a relative reference time (offset) and an opening direction.
/// Infinite duration.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HalfOpenRelativeInterval {
    pub(super) offset: Duration,
    pub(super) opening_direction: OpeningDirection,
    pub(super) reference_time_inclusivity: BoundInclusivity,
}

impl HalfOpenRelativeInterval {
    /// Creates a new instance of a half-open relative interval
    #[must_use]
    pub fn new(offset: Duration, opening_direction: OpeningDirection) -> Self {
        HalfOpenRelativeInterval {
            offset,
            opening_direction,
            reference_time_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a half-open relative interval with given inclusivity for the bound
    #[must_use]
    pub fn with_inclusivity(
        offset: Duration,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfOpenRelativeInterval {
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
}

impl Interval for HalfOpenRelativeInterval {}

impl HasOpenness for HalfOpenRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::HalfOpen
    }
}

impl HasRelativity for HalfOpenRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for HalfOpenRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasRelativeBounds for HalfOpenRelativeInterval {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfOpenRelativeIntervalConversionErr {
    WrongVariant,
}

impl Display for HalfOpenRelativeIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for HalfOpenRelativeIntervalConversionErr {}

impl TryFrom<RelativeInterval> for HalfOpenRelativeInterval {
    type Error = HalfOpenRelativeIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::HalfOpen(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// Represents any relative interval, including empty and open interval
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RelativeInterval {
    Closed(ClosedRelativeInterval),
    HalfOpen(HalfOpenRelativeInterval),
    Open(OpenInterval),
    Empty(EmptyInterval),
}

impl Interval for RelativeInterval {}

impl HasDuration for RelativeInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Closed(interval) => interval.duration(),
            Self::HalfOpen(interval) => interval.duration(),
            Self::Open(interval) => interval.duration(),
            Self::Empty(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for RelativeInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Closed(interval) => interval.relativity(),
            Self::HalfOpen(interval) => interval.relativity(),
            Self::Open(interval) => interval.relativity(),
            Self::Empty(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for RelativeInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Closed(interval) => interval.openness(),
            Self::HalfOpen(interval) => interval.openness(),
            Self::Open(interval) => interval.openness(),
            Self::Empty(interval) => interval.openness(),
        }
    }
}

impl HasEmptiableRelativeBounds for RelativeInterval {
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        match self {
            Self::Closed(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::HalfOpen(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::Open(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::Empty(interval) => interval.emptiable_rel_bounds(),
        }
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Closed(interval) => interval.partial_rel_start(),
            Self::HalfOpen(interval) => interval.partial_rel_start(),
            Self::Open(interval) => interval.partial_rel_start(),
            Self::Empty(interval) => interval.partial_rel_start(),
        }
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Closed(interval) => interval.partial_rel_end(),
            Self::HalfOpen(interval) => interval.partial_rel_end(),
            Self::Open(interval) => interval.partial_rel_end(),
            Self::Empty(interval) => interval.partial_rel_end(),
        }
    }
}

impl Emptiable for RelativeInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl From<ClosedRelativeInterval> for RelativeInterval {
    fn from(value: ClosedRelativeInterval) -> Self {
        RelativeInterval::Closed(value)
    }
}

impl From<HalfOpenRelativeInterval> for RelativeInterval {
    fn from(value: HalfOpenRelativeInterval) -> Self {
        RelativeInterval::HalfOpen(value)
    }
}

impl From<OpenInterval> for RelativeInterval {
    fn from(value: OpenInterval) -> Self {
        RelativeInterval::Open(value)
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
            (StartB::InfinitePast, EndB::InfiniteFuture) => RelativeInterval::Open(OpenInterval),
            (StartB::InfinitePast, EndB::Finite(RelativeFiniteBound { offset, inclusivity })) => {
                RelativeInterval::HalfOpen(HalfOpenRelativeInterval::with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(RelativeFiniteBound { offset, inclusivity }), EndB::InfiniteFuture) => {
                RelativeInterval::HalfOpen(HalfOpenRelativeInterval::with_inclusivity(
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
            ) => RelativeInterval::Closed(ClosedRelativeInterval::with_inclusivity(
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
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => RelativeInterval::Open(OpenInterval),
            (Some(StartB::InfinitePast), Some(EndB::Finite(RelativeFiniteBound { offset, inclusivity }))) => {
                RelativeInterval::HalfOpen(HalfOpenRelativeInterval::with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (Some(StartB::Finite(RelativeFiniteBound { offset, inclusivity })), Some(EndB::InfiniteFuture)) => {
                RelativeInterval::HalfOpen(HalfOpenRelativeInterval::with_inclusivity(
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
            ) => RelativeInterval::Closed(ClosedRelativeInterval::with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset - start_offset,
                end_inclusivity,
            )),
        }
    }
}

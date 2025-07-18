//! Intervals
//!
//! # Interval structure and terminology
//!
//! Interval refers to an interval, a range, like in mathematics. But if we are talking strictly about this crate,
//! then an interval, such as [`AbsoluteInterval`] and [`RelativeInterval`] are enumerators over specific intervals,
//! like [`ClosedAbsoluteInterval`] or [`HalfOpenRelativeInterval`].
//!
//! Those specific intervals must conserve their invariants. A closed interval must remain closed, a half-open interval
//! must remain half-open.
//!
//! All such intervals are composed of bounds (e.g. [`AbsoluteBounds`], [`RelativeBounds`]).
//! They may also come in _emptiable_ variants (e.g. [`EmptiableAbsoluteBounds`], [`EmptiableRelativeBounds`]).
//! Bounds represent the start and end point of intervals, and they have the following invariants:
//!
//! 1. The start and end must be in chronological order
//! 2. If both points are at the same position, their _bound inclusivities_ can only be [inclusive](BoundInclusivity::Inclusive)
//!
//! Bounds can be modified however you want, as they don't conserve invariants regarding [openness](Openness)
//! of their bounds.
//!
//! _Emptiable_ bounds are bounds that can also represent an [empty interval](EmptyInterval).
//!
//! While processing intervals through operations like unions and intersections can yield a different kind of interval,
//! they never mutate themselves in order to represent this new state, as they have to conserve their invariant
//! regarding [bound openness](Openness). This is the difference between an interval and bounds.
//!
//! Bounds are composed of both a start bound (e.g. [`AbsoluteStartBound`], [`RelativeStartBound`]) and an end bound
//! (e.g. [`AbsoluteEndBound`], [`RelativeEndBound`]).
//!
//! Those individual bounds represent the start and end of their parent, so they cary only a [time](chrono::DateTime)
//! (or [offset](chrono::Duration) for relative bounds) as well as a [bound inclusivity](BoundInclusivity)
//! in order to determinate whether they contain or not their time/offset.
//!
//! The reason why start and end bounds are separate and not the same structure is double:
//!
//! - To determinate the bound inclusivity _direction_: an exclusive start bound at `10.0` would mean `>10.0`,
//!   while an exclusive end bound at `10.0` would mean `<10.0`
//! - To ease processing when destructuring multiple intervals in a table of individual bounds
//!
//! Individual bounds also support being at infinite points in time, such as infinitely in the future or infinitely
//! in the past.
//!
//! While they are separate, their finite variants are composed of finite bounds (e.g. [`AbsoluteFiniteBound`],
//! [`RelativeFiniteBound`]). This is because they are meant for representing a point in time with an on-off-like
//! bound inclusivity system. This is why, when comparing them, only their time/offset is taken into account.
//!
//! [Empty intervals](EmptyInterval) are equivalent to no interval, to an empty set. They do not possess
//! a specific point in time. This is the reason why they can't be compared with other intervals, or are mostly ignored.
//!
//! The reason why empty intervals exist is to provide a way to represent _no duration_ without having to use [`Option`]
//! to represent it. This also makes it compatible with other interval operations, for example you can still get the
//! complement of an empty interval, which results in an [open interval](`OpenInterval`).

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use chrono::{DateTime, Duration, RoundingError, Utc};

use crate::intervals::meta::HasBoundInclusivity;

use super::meta::{
    BoundInclusivity, Duration as IntervalDuration, HasDuration, HasOpenness, HasRelativity, OpeningDirection,
    Openness, Relativity,
};
use super::ops::Precision;

/// Conversion trait for every interval that can be converted into an absolute interval
pub trait ToAbsolute {
    type AbsoluteType;

    /// Converts any interval into an absolute interval
    ///
    /// If relative, then a new absolute interval is created from the relative one.
    /// If absolute or [any](super::meta::Relativity::Any), then a clone of the current interval is made.
    #[must_use]
    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType;
}

/// Conversion trait for every interval that can be converted into a relative interval
pub trait ToRelative {
    type RelativeType;

    /// Converts any interval into a relative interval
    ///
    /// If absolute, then a new relative interval is created from the absolute one.
    /// If relative or [any](super::meta::Relativity::Any), then a clone of the current interval is made.
    #[must_use]
    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType;
}

/// An absolute finite bound
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsoluteFiniteBound {
    time: DateTime<Utc>,
    inclusivity: BoundInclusivity,
}

impl AbsoluteFiniteBound {
    /// Creates a new instance of an absolute finite bound using just a given time
    #[must_use]
    pub fn new(time: DateTime<Utc>) -> Self {
        Self::new_with_inclusivity(time, BoundInclusivity::default())
    }

    /// Creates a new instance of an absolute finite bound using the given time and bound inclusivity
    #[must_use]
    pub fn new_with_inclusivity(time: DateTime<Utc>, inclusivity: BoundInclusivity) -> Self {
        AbsoluteFiniteBound { time, inclusivity }
    }

    /// Returns the time of the absolute finite bound
    #[must_use]
    pub fn time(&self) -> DateTime<Utc> {
        self.time
    }

    /// Sets the time of the absolute finite bound
    pub fn set_time(&mut self, new_time: DateTime<Utc>) {
        self.time = new_time;
    }

    /// Sets the bound inclusivity of the absolute finite bound
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

impl ToAbsolute for AbsoluteFiniteBound {
    type AbsoluteType = Self;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToRelative for AbsoluteFiniteBound {
    type RelativeType = RelativeFiniteBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        RelativeFiniteBound::new_with_inclusivity(self.time - reference_time, self.inclusivity)
    }
}

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

impl ToAbsolute for RelativeFiniteBound {
    type AbsoluteType = AbsoluteFiniteBound;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        AbsoluteFiniteBound::new_with_inclusivity(reference_time + self.offset, self.inclusivity)
    }
}

impl ToRelative for RelativeFiniteBound {
    type RelativeType = Self;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
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

/// An absolute start bound, including [inclusivity](BoundInclusivity)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteStartBound {
    Finite(AbsoluteFiniteBound),
    InfinitePast,
}

impl ToAbsolute for AbsoluteStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToRelative for AbsoluteStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            AbsoluteStartBound::InfinitePast => RelativeStartBound::InfinitePast,
            AbsoluteStartBound::Finite(AbsoluteFiniteBound { time, inclusivity }) => RelativeStartBound::Finite(
                RelativeFiniteBound::new_with_inclusivity(*time - reference_time, *inclusivity),
            ),
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
            (AbsoluteStartBound::InfinitePast, _) => Ordering::Less,
            (_, AbsoluteStartBound::InfinitePast) => Ordering::Greater,
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
            ) => {
                match start_time.cmp(end_time) {
                    Ordering::Less => Some(Ordering::Less),
                    Ordering::Greater => Some(Ordering::Greater),
                    Ordering::Equal => match (start_inclusivity, end_inclusivity) {
                        (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => Some(Ordering::Equal),
                        _ => None, // If the times are equal, anything other than double inclusive bounds is invalid
                    },
                }
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

/// An absolute end bound, including [inclusivity](BoundInclusivity)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteEndBound {
    Finite(AbsoluteFiniteBound),
    InfiniteFuture,
}

impl AbsoluteEndBound {
    /// Returns the time of the bound, if finite
    #[must_use]
    pub fn time(&self) -> Option<DateTime<Utc>> {
        if let Self::Finite(AbsoluteFiniteBound { time, .. }) = self {
            return Some(*time);
        }

        None
    }

    /// Returns the inclusivity of the bound, if finite
    #[must_use]
    pub fn inclusivity(&self) -> Option<BoundInclusivity> {
        if let Self::Finite(AbsoluteFiniteBound { inclusivity, .. }) = self {
            return Some(*inclusivity);
        }

        None
    }
}

impl ToAbsolute for AbsoluteEndBound {
    type AbsoluteType = AbsoluteEndBound;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToRelative for AbsoluteEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            AbsoluteEndBound::InfiniteFuture => RelativeEndBound::InfiniteFuture,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound { time, inclusivity }) => RelativeEndBound::Finite(
                RelativeFiniteBound::new_with_inclusivity(*time - reference_time, *inclusivity),
            ),
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
            (AbsoluteEndBound::InfiniteFuture, _) => Ordering::Greater,
            (_, AbsoluteEndBound::InfiniteFuture) => Ordering::Less,
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
        other.partial_cmp(self).map(Ordering::reverse)
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

/// Swaps an absolute start bound with an absolute end bound
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

impl ToAbsolute for RelativeStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            RelativeStartBound::InfinitePast => AbsoluteStartBound::InfinitePast,
            RelativeStartBound::Finite(RelativeFiniteBound { offset, inclusivity }) => AbsoluteStartBound::Finite(
                AbsoluteFiniteBound::new_with_inclusivity(reference_time + *offset, *inclusivity),
            ),
        }
    }
}

impl ToRelative for RelativeStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
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

impl ToAbsolute for RelativeEndBound {
    type AbsoluteType = AbsoluteEndBound;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            RelativeEndBound::InfiniteFuture => AbsoluteEndBound::InfiniteFuture,
            RelativeEndBound::Finite(RelativeFiniteBound { offset, inclusivity }) => AbsoluteEndBound::Finite(
                AbsoluteFiniteBound::new_with_inclusivity(reference_time + *offset, *inclusivity),
            ),
        }
    }
}

impl ToRelative for RelativeEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
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

/// Represents something that has **non-empty** absolute bounds
pub trait HasAbsoluteBounds {
    /// Returns the absolute bounds
    #[must_use]
    fn abs_bounds(&self) -> AbsoluteBounds;

    /// Returns the absolute start bound
    #[must_use]
    fn abs_start(&self) -> AbsoluteStartBound;

    /// Returns the absolute end bound
    #[must_use]
    fn abs_end(&self) -> AbsoluteEndBound;
}

/// Represents something that has possibly empty absolute bounds
pub trait HasEmptiableAbsoluteBounds {
    /// Returns the [`EmptiableAbsoluteBounds`] of self
    #[must_use]
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds;

    /// Returns an [`Option`] of [the absolute start bound](AbsoluteStartBound)
    #[must_use]
    fn partial_abs_start(&self) -> Option<AbsoluteStartBound>;

    /// Returns an [`Option`] of [the absolute end bound](AbsoluteEndBound)
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

/// Bounds of a non-empty absolute interval
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBounds {
    start: AbsoluteStartBound,
    end: AbsoluteEndBound,
}

impl AbsoluteBounds {
    /// Creates a new instance of absolute bounds without checking if the bounds are in order
    #[must_use]
    pub fn unchecked_new(start: AbsoluteStartBound, end: AbsoluteEndBound) -> Self {
        AbsoluteBounds { start, end }
    }

    /// Creates a new instance of absolute bounds
    ///
    /// If the given bounds are not in chronological order, they are swapped.
    /// If their [partial comparison](PartialOrd) resulted in [`None`], meaning they had the same time but inclusivities
    /// other than inclusive for both, we set their inclusivities to [`Inclusive`](BoundInclusivity::Inclusive).
    #[must_use]
    pub fn new(mut start: AbsoluteStartBound, mut end: AbsoluteEndBound) -> Self {
        match start.partial_cmp(&end) {
            None => {
                if let AbsoluteStartBound::Finite(ref mut finite_start) = start {
                    finite_start.set_inclusivity(BoundInclusivity::default());
                }

                if let AbsoluteEndBound::Finite(ref mut finite_end) = end {
                    finite_end.set_inclusivity(BoundInclusivity::default());
                }

                match start.partial_cmp(&end) {
                    Some(Ordering::Equal | Ordering::Less) => Self::unchecked_new(start, end),
                    Some(Ordering::Greater) => {
                        swap_absolute_bounds(&mut start, &mut end);
                        Self::unchecked_new(start, end)
                    },
                    None => unimplemented!(
                        "Something went wrong when instantiating `AbsoluteBounds` with bounds that partially compared to `None`"
                    ),
                }
            },
            Some(Ordering::Equal | Ordering::Less) => Self::unchecked_new(start, end),
            Some(Ordering::Greater) => {
                // If the start time is after the end time, swap the two to preserve order
                swap_absolute_bounds(&mut start, &mut end);
                Self::unchecked_new(start, end)
            },
        }
    }

    /// Returns the absolute start bound
    #[must_use]
    pub fn start(&self) -> &AbsoluteStartBound {
        &self.start
    }

    /// Returns the absolute end bound
    #[must_use]
    pub fn end(&self) -> &AbsoluteEndBound {
        &self.end
    }

    /// Sets the start bound without checking if it is in the right order
    pub fn unchecked_set_start(&mut self, new_start: AbsoluteStartBound) {
        self.start = new_start;
    }

    /// Sets the end bound without checking if it is in the right order
    pub fn unchecked_set_end(&mut self, new_end: AbsoluteEndBound) {
        self.end = new_end;
    }

    /// Sets the start bound
    ///
    /// Returns whether the operation was successful: the new start must be in chronological order and if it is equal
    /// to the end bound, both bounds must be inclusive.
    pub fn set_start(&mut self, new_start: AbsoluteStartBound) -> bool {
        if new_start.partial_cmp(self.end()).is_none_or(Ordering::is_gt) {
            return false;
        }

        self.unchecked_set_start(new_start);
        true
    }

    /// Sets the end bound
    ///
    /// Returns whether the operation was successful: the new end must be in chronological order and if it is equal
    /// to the start bound, both bounds must be inclusive.
    pub fn set_end(&mut self, new_end: AbsoluteEndBound) -> bool {
        if self.start().partial_cmp(&new_end).is_none_or(Ordering::is_gt) {
            return false;
        }

        self.unchecked_set_end(new_end);
        true
    }
}

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

impl PartialOrd for AbsoluteBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteBounds {
    fn cmp(&self, other: &Self) -> Ordering {
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

impl ToAbsolute for AbsoluteBounds {
    type AbsoluteType = AbsoluteBounds;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for AbsoluteBounds {
    type RelativeType = RelativeBounds;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        RelativeBounds::new(
            self.abs_start().to_relative(reference_time),
            self.abs_end().to_relative(reference_time),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbsoluteBoundsConversionErr {
    EmptyVariant,
}

impl Display for AbsoluteBoundsConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyVariant => write!(f, "Provided EmptiableAbsoluteBounds was empty"),
        }
    }
}

impl Error for AbsoluteBoundsConversionErr {}

impl TryFrom<EmptiableAbsoluteBounds> for AbsoluteBounds {
    type Error = AbsoluteBoundsConversionErr;

    fn try_from(value: EmptiableAbsoluteBounds) -> Result<Self, Self::Error> {
        match value {
            EmptiableAbsoluteBounds::Empty => Err(AbsoluteBoundsConversionErr::EmptyVariant),
            EmptiableAbsoluteBounds::Bound(bounds) => Ok(bounds),
        }
    }
}

// Bounds of an absolute interval
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EmptiableAbsoluteBounds {
    Empty,
    Bound(AbsoluteBounds),
}

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

impl ToAbsolute for EmptiableAbsoluteBounds {
    type AbsoluteType = Self;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for EmptiableAbsoluteBounds {
    type RelativeType = EmptiableRelativeBounds;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            Self::Empty => EmptiableRelativeBounds::Empty,
            Self::Bound(abs_bounds) => EmptiableRelativeBounds::Bound(abs_bounds.to_relative(reference_time)),
        }
    }
}

impl From<AbsoluteBounds> for EmptiableAbsoluteBounds {
    fn from(value: AbsoluteBounds) -> Self {
        EmptiableAbsoluteBounds::Bound(value)
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

impl ToAbsolute for RelativeBounds {
    type AbsoluteType = AbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        AbsoluteBounds::new(
            self.rel_start().to_absolute(reference_time),
            self.rel_end().to_absolute(reference_time),
        )
    }
}

impl ToRelative for RelativeBounds {
    type RelativeType = RelativeBounds;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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

impl ToAbsolute for EmptiableRelativeBounds {
    type AbsoluteType = EmptiableAbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            Self::Empty => EmptiableAbsoluteBounds::Empty,
            Self::Bound(abs_bounds) => EmptiableAbsoluteBounds::Bound(abs_bounds.to_absolute(reference_time)),
        }
    }
}

impl ToRelative for EmptiableRelativeBounds {
    type RelativeType = Self;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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

/// A closed absolute interval
///
/// Interval set with absolute time, with a defined start and end
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClosedAbsoluteInterval {
    pub(super) from: DateTime<Utc>,
    pub(super) to: DateTime<Utc>,
    pub(super) from_inclusivity: BoundInclusivity,
    pub(super) to_inclusivity: BoundInclusivity,
}

impl ClosedAbsoluteInterval {
    /// Creates a new instance of a closed absolute interval without checking if from is greater than to
    #[must_use]
    pub fn unchecked_new(from: DateTime<Utc>, to: DateTime<Utc>) -> Self {
        ClosedAbsoluteInterval {
            from,
            to,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a closed absolute interval
    #[must_use]
    pub fn new(mut from: DateTime<Utc>, mut to: DateTime<Utc>) -> Self {
        if from > to {
            std::mem::swap(&mut from, &mut to);
        }

        Self::unchecked_new(from, to)
    }

    /// Creates a new instance of a closed absolute interval with given inclusivity for the bounds without checking
    /// if from is greater than to
    #[must_use]
    pub fn unchecked_with_inclusivity(
        from: DateTime<Utc>,
        from_inclusivity: BoundInclusivity,
        to: DateTime<Utc>,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        ClosedAbsoluteInterval {
            from,
            to,
            from_inclusivity,
            to_inclusivity,
        }
    }

    /// Creates a new instance of a closed absolute interval with given inclusivity for the bounds
    ///
    /// If the given times are not in chronological order, we swap them so they are in chronological order.
    /// If the given times are equal but have bound inclusivities other than inclusive,
    /// we set them to [`Inclusive`](BoundInclusivity::Inclusive).
    #[must_use]
    pub fn with_inclusivity(
        mut from: DateTime<Utc>,
        from_inclusivity: BoundInclusivity,
        mut to: DateTime<Utc>,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        match from.cmp(&to) {
            Ordering::Less => Self::unchecked_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            Ordering::Equal => Self::unchecked_new(from, to),
            Ordering::Greater => {
                std::mem::swap(&mut from, &mut to);
                Self::unchecked_with_inclusivity(from, from_inclusivity, to, to_inclusivity)
            },
        }
    }

    /// Returns the start time
    #[must_use]
    pub fn from_time(&self) -> DateTime<Utc> {
        self.from
    }

    /// Returns the end time
    #[must_use]
    pub fn to_time(&self) -> DateTime<Utc> {
        self.to
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

    /// Sets the from time of the interval without checking if it is before the to time
    pub fn unchecked_set_from(&mut self, new_from: DateTime<Utc>) {
        self.from = new_from;
    }

    /// Sets the to time of the interval without checking if it is after the from time
    pub fn unchecked_set_to(&mut self, new_to: DateTime<Utc>) {
        self.to = new_to;
    }

    /// Sets the from time of the interval
    ///
    /// Returns boolean indicating whether the change was successful: the new from must be in chronological order
    /// and if it is equal to the to time, then the bounds must be inclusive already.
    pub fn set_from(&mut self, new_from: DateTime<Utc>) -> bool {
        match new_from.cmp(&self.to) {
            Ordering::Less => self.unchecked_set_from(new_from),
            Ordering::Equal => {
                if self.from_inclusivity != BoundInclusivity::Inclusive
                    || self.to_inclusivity != BoundInclusivity::Inclusive
                {
                    return false;
                }

                self.unchecked_set_from(new_from);
            },
            Ordering::Greater => {
                return false;
            },
        }

        true
    }

    /// Sets the to time of the interval
    ///
    /// Returns boolean indicating whether the change was successful: the new to must be in chronological order
    /// and if it is equal to the from time, then the bounds must be inclusive already.
    pub fn set_to(&mut self, new_to: DateTime<Utc>) -> bool {
        match self.from.cmp(&new_to) {
            Ordering::Less => self.unchecked_set_to(new_to),
            Ordering::Equal => {
                if self.from_inclusivity != BoundInclusivity::Inclusive
                    || self.to_inclusivity != BoundInclusivity::Inclusive
                {
                    return false;
                }

                self.unchecked_set_to(new_to);
            },
            Ordering::Greater => {
                return false;
            },
        }

        true
    }

    /// Sets the inclusivity of the start bound
    ///
    /// Returns whether the operation was successful: if the start and end times are equal, the inclusivities can't be
    /// set to anything other than inclusive.
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.from == self.to && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.from_inclusivity = new_inclusivity;
        true
    }

    /// Sets the inclusivity of the end bound
    ///
    /// Returns whether the operation was successful: if the start and end times are equal, the inclusivities can't be
    /// set to anything other than inclusive.
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.from == self.to && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.to_inclusivity = new_inclusivity;
        true
    }
}

impl HasOpenness for ClosedAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::Closed
    }
}

impl HasRelativity for ClosedAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for ClosedAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(self.to - self.from)
    }
}

impl HasAbsoluteBounds for ClosedAbsoluteInterval {
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

impl ToAbsolute for ClosedAbsoluteInterval {
    type AbsoluteType = ClosedAbsoluteInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for ClosedAbsoluteInterval {
    type RelativeType = ClosedRelativeInterval;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        ClosedRelativeInterval::with_inclusivity(
            self.from - reference_time,
            self.from_inclusivity,
            self.to - self.from,
            self.to_inclusivity,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClosedAbsoluteIntervalConversionErr {
    WrongVariant,
}

impl Display for ClosedAbsoluteIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for ClosedAbsoluteIntervalConversionErr {}

impl TryFrom<AbsoluteInterval> for ClosedAbsoluteInterval {
    type Error = ClosedAbsoluteIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Closed(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
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

impl ToAbsolute for ClosedRelativeInterval {
    type AbsoluteType = ClosedAbsoluteInterval;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        ClosedAbsoluteInterval::unchecked_with_inclusivity(
            reference_time + self.offset,
            self.from_inclusivity,
            reference_time + self.offset + self.length,
            self.to_inclusivity,
        )
    }
}

impl ToRelative for ClosedRelativeInterval {
    type RelativeType = ClosedRelativeInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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

/// A half-open absolute interval
///
/// An interval set with absolute time, has a defined reference time and an opening direction (only one defined bound).
/// Infinite duration.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HalfOpenAbsoluteInterval {
    pub(super) reference_time: DateTime<Utc>,
    pub(super) opening_direction: OpeningDirection,
    pub(super) reference_time_inclusivity: BoundInclusivity,
}

impl HalfOpenAbsoluteInterval {
    /// Creates a new instance of a half-open absolute interval
    #[must_use]
    pub fn new(reference_time: DateTime<Utc>, opening_direction: OpeningDirection) -> Self {
        HalfOpenAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_time_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new instance of a half-open absolute interval with given inclusivity for the bound
    #[must_use]
    pub fn with_inclusivity(
        reference_time: DateTime<Utc>,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfOpenAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_time_inclusivity,
        }
    }

    /// Returns the reference time of the interval
    #[must_use]
    pub fn reference_time(&self) -> DateTime<Utc> {
        self.reference_time
    }

    /// Tries to return the reference time with the given precision
    ///
    /// # Errors
    ///
    /// See [`Precision::try_precise_time`]
    pub fn try_reference_time_with_precision(&self, precision: Precision) -> Result<DateTime<Utc>, RoundingError> {
        precision.precise_time(self.reference_time)
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

    /// Sets the reference time of the interval
    pub fn set_reference_time(&mut self, new_reference_time: DateTime<Utc>) {
        self.reference_time = new_reference_time;
    }

    /// Sets the inclusivity of the reference time
    pub fn set_reference_time_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_time_inclusivity = new_inclusivity;
    }
}

impl HasOpenness for HalfOpenAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::HalfOpen
    }
}

impl HasRelativity for HalfOpenAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for HalfOpenAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasAbsoluteBounds for HalfOpenAbsoluteInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteStartBound::InfinitePast,
            OpeningDirection::ToFuture => AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                self.reference_time,
                self.reference_time_inclusivity,
            )),
        }
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                self.reference_time,
                self.reference_time_inclusivity,
            )),
            OpeningDirection::ToFuture => AbsoluteEndBound::InfiniteFuture,
        }
    }
}

impl ToAbsolute for HalfOpenAbsoluteInterval {
    type AbsoluteType = HalfOpenAbsoluteInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for HalfOpenAbsoluteInterval {
    type RelativeType = HalfOpenRelativeInterval;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        HalfOpenRelativeInterval::with_inclusivity(
            self.reference_time - reference_time,
            self.reference_time_inclusivity,
            self.opening_direction,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfOpenAbsoluteIntervalConversionErr {
    WrongVariant,
}

impl Display for HalfOpenAbsoluteIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for HalfOpenAbsoluteIntervalConversionErr {}

impl TryFrom<AbsoluteInterval> for HalfOpenAbsoluteInterval {
    type Error = HalfOpenAbsoluteIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::HalfOpen(interval) => Ok(interval),
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

impl ToAbsolute for HalfOpenRelativeInterval {
    type AbsoluteType = HalfOpenAbsoluteInterval;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        HalfOpenAbsoluteInterval::with_inclusivity(
            reference_time + self.offset,
            self.reference_time_inclusivity,
            self.opening_direction,
        )
    }
}

impl ToRelative for HalfOpenRelativeInterval {
    type RelativeType = HalfOpenRelativeInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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

/// An open interval
///
/// Interval without relativity (not absolute nor relative) and without any bounds.
/// Is equivalent to _time itself_ (all time), infinite duration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OpenInterval;

impl HasOpenness for OpenInterval {
    fn openness(&self) -> Openness {
        Openness::Open
    }
}

impl HasRelativity for OpenInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Any
    }
}

impl HasDuration for OpenInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasAbsoluteBounds for OpenInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        AbsoluteStartBound::InfinitePast
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        AbsoluteEndBound::InfiniteFuture
    }
}

impl HasRelativeBounds for OpenInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        RelativeStartBound::InfinitePast
    }

    fn rel_end(&self) -> RelativeEndBound {
        RelativeEndBound::InfiniteFuture
    }
}

impl ToAbsolute for OpenInterval {
    type AbsoluteType = OpenInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToRelative for OpenInterval {
    type RelativeType = OpenInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpenIntervalConversionErr {
    WrongVariant,
}

impl Display for OpenIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for OpenIntervalConversionErr {}

impl TryFrom<AbsoluteInterval> for OpenInterval {
    type Error = OpenIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Open(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<RelativeInterval> for OpenInterval {
    type Error = OpenIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Open(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// No interval
///
/// Equivalent to the [empty set](https://en.wikipedia.org/wiki/Empty_set), this allows for still performing
/// operations such as the complement of the interval without issues.
///
/// In regards to operations such as the overlap position, an empty interval has no defined place,
/// it simply represents the _lack_ of a time interval, like the complement of an open interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyInterval;

impl HasOpenness for EmptyInterval {
    fn openness(&self) -> Openness {
        Openness::Empty
    }
}

impl HasRelativity for EmptyInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Any
    }
}

impl HasDuration for EmptyInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(Duration::zero())
    }
}

impl HasEmptiableAbsoluteBounds for EmptyInterval {
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        EmptiableAbsoluteBounds::Empty
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        None
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        None
    }
}

impl HasEmptiableRelativeBounds for EmptyInterval {
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        EmptiableRelativeBounds::Empty
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        None
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        None
    }
}

impl ToAbsolute for EmptyInterval {
    type AbsoluteType = EmptyInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToRelative for EmptyInterval {
    type RelativeType = EmptyInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EmptyIntervalConversionErr {
    WrongVariant,
}

impl Display for EmptyIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for EmptyIntervalConversionErr {}

impl TryFrom<AbsoluteInterval> for EmptyInterval {
    type Error = EmptyIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Empty(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<RelativeInterval> for EmptyInterval {
    type Error = EmptyIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Empty(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// Represents any absolute interval, including empty and open intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbsoluteInterval {
    Closed(ClosedAbsoluteInterval),
    HalfOpen(HalfOpenAbsoluteInterval),
    Open(OpenInterval),
    Empty(EmptyInterval),
}

impl HasDuration for AbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Closed(interval) => interval.duration(),
            Self::HalfOpen(interval) => interval.duration(),
            Self::Open(interval) => interval.duration(),
            Self::Empty(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for AbsoluteInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Closed(interval) => interval.relativity(),
            Self::HalfOpen(interval) => interval.relativity(),
            Self::Open(interval) => interval.relativity(),
            Self::Empty(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for AbsoluteInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Closed(interval) => interval.openness(),
            Self::HalfOpen(interval) => interval.openness(),
            Self::Open(interval) => interval.openness(),
            Self::Empty(interval) => interval.openness(),
        }
    }
}

impl HasEmptiableAbsoluteBounds for AbsoluteInterval {
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        match self {
            Self::Closed(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::HalfOpen(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::Open(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::Empty(interval) => interval.emptiable_abs_bounds(),
        }
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Closed(interval) => interval.partial_abs_start(),
            Self::HalfOpen(interval) => interval.partial_abs_start(),
            Self::Open(interval) => interval.partial_abs_start(),
            Self::Empty(interval) => interval.partial_abs_start(),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Closed(interval) => interval.partial_abs_end(),
            Self::HalfOpen(interval) => interval.partial_abs_end(),
            Self::Open(interval) => interval.partial_abs_end(),
            Self::Empty(interval) => interval.partial_abs_end(),
        }
    }
}

impl ToAbsolute for AbsoluteInterval {
    type AbsoluteType = AbsoluteInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for AbsoluteInterval {
    type RelativeType = RelativeInterval;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            Self::Closed(closed) => RelativeInterval::Closed(closed.to_relative(reference_time)),
            Self::HalfOpen(half_open) => RelativeInterval::HalfOpen(half_open.to_relative(reference_time)),
            Self::Open(open) => RelativeInterval::Open(open.to_relative(reference_time)),
            Self::Empty(empty) => RelativeInterval::Empty(empty.to_relative(reference_time)),
        }
    }
}

impl From<ClosedAbsoluteInterval> for AbsoluteInterval {
    fn from(value: ClosedAbsoluteInterval) -> Self {
        AbsoluteInterval::Closed(value)
    }
}

impl From<HalfOpenAbsoluteInterval> for AbsoluteInterval {
    fn from(value: HalfOpenAbsoluteInterval) -> Self {
        AbsoluteInterval::HalfOpen(value)
    }
}

impl From<OpenInterval> for AbsoluteInterval {
    fn from(value: OpenInterval) -> Self {
        AbsoluteInterval::Open(value)
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
            (StartB::InfinitePast, EndB::InfiniteFuture) => AbsoluteInterval::Open(OpenInterval),
            (StartB::InfinitePast, EndB::Finite(AbsoluteFiniteBound { time, inclusivity })) => {
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(AbsoluteFiniteBound { time, inclusivity }), EndB::InfiniteFuture) => {
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::with_inclusivity(
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
            ) => AbsoluteInterval::Closed(ClosedAbsoluteInterval::unchecked_with_inclusivity(
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
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => AbsoluteInterval::Open(OpenInterval),
            (Some(StartB::InfinitePast), Some(EndB::Finite(AbsoluteFiniteBound { time, inclusivity }))) => {
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (Some(StartB::Finite(AbsoluteFiniteBound { time, inclusivity })), Some(EndB::InfiniteFuture)) => {
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::with_inclusivity(
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
            ) => AbsoluteInterval::Closed(ClosedAbsoluteInterval::unchecked_with_inclusivity(
                start_time,
                start_inclusivity,
                end_time,
                end_inclusivity,
            )),
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

impl ToAbsolute for RelativeInterval {
    type AbsoluteType = AbsoluteInterval;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            Self::Closed(closed) => AbsoluteInterval::Closed(closed.to_absolute(reference_time)),
            Self::HalfOpen(half_open) => AbsoluteInterval::HalfOpen(half_open.to_absolute(reference_time)),
            Self::Open(open) => AbsoluteInterval::Open(open.to_absolute(reference_time)),
            Self::Empty(empty) => AbsoluteInterval::Empty(empty.to_absolute(reference_time)),
        }
    }
}

impl ToRelative for RelativeInterval {
    type RelativeType = RelativeInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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

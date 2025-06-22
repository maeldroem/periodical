//! Intervals
//!
//! The core of intervals is implemented here. You will find the implementations for each different variant
//! of intervals, but also find how the principal structure, [`Interval`] works.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use chrono::{DateTime, Duration, RoundingError, Utc};

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


/// An absolute start bound, including [inclusivity](BoundInclusivity)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteStartBound {
    Finite(DateTime<Utc>, BoundInclusivity),
    InfinitePast,
}

impl AbsoluteStartBound {
    /// Returns the time of the bound, if finite
    #[must_use]
    pub fn time(&self) -> Option<DateTime<Utc>> {
        if let Self::Finite(time, _) = self {
            return Some(*time);
        }

        None
    }

    /// Returns the inclusivity of the bound, if finite
    #[must_use]
    pub fn inclusivity(&self) -> Option<BoundInclusivity> {
        if let Self::Finite(_, inclusivity) = self {
            return Some(*inclusivity);
        }

        None
    }
}

impl ToAbsolute for AbsoluteStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for AbsoluteStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            AbsoluteStartBound::InfinitePast => RelativeStartBound::InfinitePast,
            AbsoluteStartBound::Finite(time, inclusivity) => RelativeStartBound::Finite(*time - reference_time, *inclusivity),
        }
    }
}

impl PartialEq<AbsoluteEndBound> for AbsoluteStartBound {
    fn eq(&self, other: &AbsoluteEndBound) -> bool {
        match (self, other) {
            (
                AbsoluteStartBound::Finite(start_time, start_inclusivity),
                AbsoluteEndBound::Finite(end_time, end_inclusivity),
            ) => {
                start_time == end_time
                    && *start_inclusivity == BoundInclusivity::Inclusive
                    && *end_inclusivity == BoundInclusivity::Inclusive
            },
            _ => false,
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
            (AbsoluteStartBound::InfinitePast, _) => Ordering::Less,
            (_, AbsoluteStartBound::InfinitePast) => Ordering::Greater,
            (
                AbsoluteStartBound::Finite(time_og, inclusivity_og),
                AbsoluteStartBound::Finite(time_other, inclusivity_other),
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
                AbsoluteStartBound::Finite(start_time, start_inclusivity),
                AbsoluteEndBound::Finite(end_time, end_inclusivity),
            ) => {
                match start_time.cmp(end_time) {
                    Ordering::Less => Some(Ordering::Less),
                    Ordering::Greater => Some(Ordering::Greater),
                    Ordering::Equal => match (start_inclusivity, end_inclusivity) {
                        // think of it as a start bound of a later interval compared to the end bound of an earlier one
                        (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => Some(Ordering::Equal),
                        _ => Some(Ordering::Greater),
                    },
                }
            },
        }
    }
}

impl Display for AbsoluteStartBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Absolute start: ");

        match self {
            Self::Finite(time, inclusivity) => {
                write!(f, "{time} ({inclusivity})")
            },
            Self::InfinitePast => write!(f, "Infinite past"),
        }
    }
}

/// An absolute end bound, including [inclusivity](BoundInclusivity)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteEndBound {
    Finite(DateTime<Utc>, BoundInclusivity),
    InfiniteFuture,
}

impl AbsoluteEndBound {
    /// Returns the time of the bound, if finite
    #[must_use]
    pub fn time(&self) -> Option<DateTime<Utc>> {
        if let Self::Finite(time, _) = self {
            return Some(*time);
        }

        None
    }

    /// Returns the inclusivity of the bound, if finite
    #[must_use]
    pub fn inclusivity(&self) -> Option<BoundInclusivity> {
        if let Self::Finite(_, inclusivity) = self {
            return Some(*inclusivity);
        }

        None
    }
}

impl ToAbsolute for AbsoluteEndBound {
    type AbsoluteType = AbsoluteEndBound;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for AbsoluteEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            AbsoluteEndBound::InfiniteFuture => RelativeEndBound::InfiniteFuture,
            AbsoluteEndBound::Finite(time, inclusivity) => RelativeEndBound::Finite(*time - reference_time, *inclusivity),
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
                AbsoluteEndBound::Finite(time_og, inclusivity_og),
                AbsoluteEndBound::Finite(time_other, inclusivity_other),
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
        write!(f, "Absolute end: ");

        match self {
            Self::Finite(time, inclusivity) => {
                write!(f, "{time} ({inclusivity})")
            },
            Self::InfiniteFuture => write!(f, "Infinite future"),
        }
    }
}

/// A relative start interval bound, including [inclusivity](BoundInclusivity)
///
/// # Why no [`PartialOrd`] implementation
///
/// Partial ordering is only correct if all bound offsets were created from the same reference,
/// which we can't guarantee.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeStartBound {
    Finite(Duration, BoundInclusivity),
    InfinitePast,
}

impl RelativeStartBound {
    /// Returns the offset of the bound, if finite
    #[must_use]
    pub fn offset(&self) -> Option<Duration> {
        if let Self::Finite(offset, _) = self {
            return Some(*offset);
        }

        None
    }

    /// Returns the inclusivity of the bound, if finite
    #[must_use]
    pub fn inclusivity(&self) -> Option<BoundInclusivity> {
        if let Self::Finite(_, inclusivity) = self {
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
            RelativeStartBound::Finite(offset, inclusivity) => AbsoluteStartBound::Finite(reference_time + *offset, *inclusivity),
        }
    }
}

impl ToRelative for RelativeStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
    }
}

impl Display for RelativeStartBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Relative start: ");

        match self {
            Self::Finite(offset, inclusivity) => {
                write!(f, "{offset} ({inclusivity})")
            },
            Self::InfinitePast => write!(f, "Infinite past"),
        }
    }
}

/// A relative end interval bound, including [inclusivity](BoundInclusivity)
/// 
/// This contains an offset from the reference time to the end bound, not the length of the relative interval
///
/// # Why no [`PartialOrd`] implementation
///
/// Partial ordering is only correct if all bound offsets were created from the same reference,
/// which we can't guarantee.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeEndBound {
    Finite(Duration, BoundInclusivity),
    InfiniteFuture,
}

impl RelativeEndBound {
    /// Returns the offset of the bound, if finite
    #[must_use]
    pub fn offset(&self) -> Option<Duration> {
        if let Self::Finite(offset, _) = self {
            return Some(*offset);
        }

        None
    }

    /// Returns the inclusivity of the bound, if finite
    #[must_use]
    pub fn inclusivity(&self) -> Option<BoundInclusivity> {
        if let Self::Finite(_, inclusivity) = self {
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
            RelativeEndBound::Finite(offset, inclusivity) => AbsoluteEndBound::Finite(reference_time + *offset, *inclusivity),
        }
    }
}

impl ToRelative for RelativeEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
    }
}

impl Display for RelativeEndBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Relative end: ");

        match self {
            Self::Finite(offset, inclusivity) => {
                write!(f, "{offset} ({inclusivity})")
            },
            Self::InfiniteFuture => write!(f, "Infinite future"),
        }
    }
}

/// Represents something that has absolute bounds
pub trait HasAbsoluteBounds {
    /// Returns the absolute bounds
    #[must_use]
    fn abs_bounds(&self) -> AbsoluteBounds;

    /// Returns the absolute start bound
    #[must_use]
    fn abs_start(&self) -> Option<AbsoluteStartBound> {
        self.abs_bounds().start
    }

    /// Returns the absolute end bound
    #[must_use]
    fn abs_end(&self) -> Option<AbsoluteEndBound> {
        self.abs_bounds().end
    }

    /// Returns the time of the absolute start bound
    #[must_use]
    fn abs_start_time(&self) -> Option<DateTime<Utc>> {
        self.abs_start().and_then(|bound| {
            if let AbsoluteStartBound::Finite(time, _) = bound {
                return Some(time);
            }

            None
        })
    }

    /// Returns the time of the absolute end bound
    #[must_use]
    fn abs_end_time(&self) -> Option<DateTime<Utc>> {
        self.abs_end().and_then(|bound| {
            if let AbsoluteEndBound::Finite(time, _) = bound {
                return Some(time);
            }

            None
        })
    }

    /// Returns the bound inclusivity of the absolute start bound
    #[must_use]
    fn abs_start_inclusivity(&self) -> Option<BoundInclusivity> {
        self.abs_start().and_then(|bound| {
            if let AbsoluteStartBound::Finite(_, inclusivity) = bound {
                return Some(inclusivity);
            }

            None
        })
    }

    /// Returns the bound inclusivity of the absolute end bound
    #[must_use]
    fn abs_end_inclusivity(&self) -> Option<BoundInclusivity> {
        self.abs_end().and_then(|bound| {
            if let AbsoluteEndBound::Finite(_, inclusivity) = bound {
                return Some(inclusivity);
            }

            None
        })
    }

    /// Returns whether the bounds are those for an empty interval
    #[must_use]
    fn is_empty(&self) -> bool {
        let bounds = self.abs_bounds();
        bounds.start.is_none() || bounds.end.is_none()
    }
}

/// Bounds of an absolute interval
///
/// # Invariant
///
/// Either two bounds are defined, or no bounds are defined (in the case of an empty interval)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBounds {
    start: Option<AbsoluteStartBound>,
    end: Option<AbsoluteEndBound>,
}

impl AbsoluteBounds {
    /// Creates a new instance of absolute bounds without checking if the bounds are in order
    #[must_use]
    pub fn unchecked_new(start: AbsoluteStartBound, end: AbsoluteEndBound) -> Self {
        AbsoluteBounds {
            start: Some(start),
            end: Some(end),
        }
    }

    /// Creates a new instance of absolute bounds
    #[must_use]
    pub fn new(start: AbsoluteStartBound, end: AbsoluteEndBound) -> Self {
        // If the start time is after the end time, swap the two to preserve order
        if let (AbsoluteStartBound::Finite(ref mut start_time, _), AbsoluteEndBound::Finite(ref mut end_time, _)) = (start, end) {
            if start_time > end_time {
                std::mem::swap(start_time, end_time)
            }
        }

        Self::unchecked_new(start, end)
    }

    /// Creates a new instance of absolute bounds for an empty interval
    #[must_use]
    pub fn new_empty() -> Self {
        AbsoluteBounds { start: None, end: None }
    }

    /// Sets the start bound without checking if it is in the right order
    /// 
    /// Returns whether the operation was successful as this method still guarantees [`AbsoluteBounds`]' invariant
    pub fn unchecked_set_start(&mut self, new_start: AbsoluteStartBound) -> bool {
        if self.is_empty() {
            return false;
        }

        self.start = Some(new_start);
        true
    }

    /// Sets the end bound without checking if it is in the right order
    /// 
    /// Returns whether the operation was successful as this method still guarantees [`AbsoluteBounds`]' invariant.
    pub fn unchecked_set_end(&mut self, new_end: AbsoluteEndBound) -> bool {
        if self.is_empty() {
            return false;
        }

        self.end = Some(new_end);
        true
    }

    /// Sets the start bound
    /// 
    /// Returns whether the operation was successful: the new start must be in order compared to the end and shouldn't
    /// compromise [`AbsoluteBounds`]' invariant.
    pub fn set_start(&mut self, new_start: AbsoluteStartBound) -> bool {
        if self.end.is_none_or(|end_time| new_start > end_time) {
            return false;
        }

        self.unchecked_set_start(new_start)
    }

    /// Sets the end bound
    /// 
    /// Returns whether the operation was successful: the new end must be in order compared to the start and shouldn't
    /// compromise [`AbsoluteBounds`]' invariant.
    pub fn set_end(&mut self, new_end: AbsoluteEndBound) -> bool {
        if self.start.is_none_or(|start_time| new_end < start_time) {
            return false;
        }

        self.unchecked_set_end(new_end)
    }
}

impl HasAbsoluteBounds for AbsoluteBounds {
    fn abs_bounds(&self) -> AbsoluteBounds {
        self.clone()
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
        match (self.start, self.end) {
            (None, _) | (_, None) => write!(f, "Empty interval bounds"),
            (Some(start), Some(end)) => {
                match start {
                    AbsoluteStartBound::Finite(time, inclusivity) => {
                        write!(f, "{time} ({inclusivity})");
                    },
                    AbsoluteStartBound::InfinitePast => {
                        write!(f, "Infinite past");
                    },
                }

                write!(f, " - ");

                match end {
                    AbsoluteEndBound::Finite(time, inclusivity) => {
                        write!(f, "{time} ({inclusivity})");
                    },
                    AbsoluteEndBound::InfiniteFuture => {
                        write!(f, "Infinite future");
                    },
                }

                Ok(())
            },
        }
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
        if self.is_empty() {
            return RelativeBounds::new_empty();
        }

        RelativeBounds::new(
            self.abs_start().unwrap().to_relative(reference_time),
            self.abs_end().unwrap().to_relative(reference_time),
        )
    }
}

/// Represents something that has relative bounds
pub trait HasRelativeBounds {
    /// Returns the relative bounds
    #[must_use]
    fn rel_bounds(&self) -> RelativeBounds;

    /// Returns the relative start bound
    #[must_use]
    fn rel_start(&self) -> Option<RelativeStartBound> {
        self.rel_bounds().start
    }

    /// Returns the relative end bound
    #[must_use]
    fn rel_end(&self) -> Option<RelativeEndBound> {
        self.rel_bounds().end
    }


    /// Returns the offset of the relative start bound
    #[must_use]
    fn rel_start_offset(&self) -> Option<Duration> {
        self.rel_start().and_then(|bound| {
            if let RelativeStartBound::Finite(offset, _) = bound {
                return Some(offset);
            }

            None
        })
    }

    /// Returns the offset of the relative end bound
    #[must_use]
    fn rel_end_offset(&self) -> Option<Duration> {
        self.rel_end().and_then(|bound| {
            if let RelativeEndBound::Finite(offset, _) = bound {
                return Some(offset);
            }

            None
        })
    }

    /// Returns the bound inclusivity of the relative start bound
    #[must_use]
    fn rel_start_inclusivity(&self) -> Option<BoundInclusivity> {
        self.rel_start().and_then(|bound| {
            if let RelativeStartBound::Finite(_, inclusivity) = bound {
                return Some(inclusivity);
            }

            None
        })
    }

    /// Returns the bound inclusivity of the relative end bound
    #[must_use]
    fn rel_end_inclusivity(&self) -> Option<BoundInclusivity> {
        self.rel_end().and_then(|bound| {
            if let RelativeEndBound::Finite(_, inclusivity) = bound {
                return Some(inclusivity);
            }

            None
        })
    }

    /// Returns whether the bounds are those for an empty interval
    #[must_use]
    fn is_empty(&self) -> bool {
        let bounds = self.rel_bounds();
        bounds.start.is_none() || bounds.end.is_none()
    }
}

/// Bounds of a relative interval
///
/// # Why no [`PartialOrd`] implementation
///
/// Partial ordering is only correct if all bound offsets were created from the same reference,
/// which we can't guarantee.
///
/// # Invariant
///
/// Either two bounds are defined, or no bounds are defined (in the case of an empty interval)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativeBounds {
    start: Option<RelativeStartBound>,
    end: Option<RelativeEndBound>,
}

impl RelativeBounds {
    /// Creates an instance of relative bounds
    #[must_use]
    pub fn new(start: RelativeStartBound, end: RelativeEndBound) -> Self {
        RelativeBounds {
            start: Some(start),
            end: Some(end),
        }
    }

    /// Creates an instance of empty relative bounds (for empty intervals)
    #[must_use]
    pub fn new_empty() -> Self {
        RelativeBounds { start: None, end: None }
    }

    /// Sets the start bound
    /// 
    /// Returns whether the operation was successful: it shouldn't compromise [`RelativeBounds`]' invariant.
    pub fn set_start(&mut self, new_start: RelativeStartBound) -> bool {
        if self.is_empty() {
            return false;
        }

        self.start = Some(new_start);
        true
    }

    /// Sets the end bound
    /// 
    /// Returns whether the operation was successful: it shouldn't compromise [`RelativeBounds`]' invariant.
    pub fn set_end(&mut self, new_end: RelativeEndBound) -> bool {
        if self.is_empty() {
            return false;
        }

        self.end = Some(new_end);
        true
    }
}

impl HasRelativeBounds for RelativeBounds {
    fn rel_bounds(&self) -> RelativeBounds {
        self.clone()
    }
}

impl Display for RelativeBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.start, self.end) {
            (None, _) | (_, None) => write!(f, "Empty interval bounds"),
            (Some(start), Some(end)) => {
                match start {
                    RelativeStartBound::Finite(offset, inclusivity) => {
                        write!(f, "{offset} ({inclusivity})");
                    },
                    RelativeStartBound::InfinitePast => {
                        write!(f, "Infinite past");
                    },
                }

                write!(f, " - ");

                match end {
                    RelativeEndBound::Finite(offset, inclusivity) => {
                        write!(f, "{offset} ({inclusivity})");
                    },
                    RelativeEndBound::InfiniteFuture => {
                        write!(f, "Infinite future");
                    },
                }

                Ok(())
            },
        }
    }
}

impl ToAbsolute for RelativeBounds {
    type AbsoluteType = AbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        if self.is_empty() {
            return AbsoluteBounds::new_empty();
        }

        AbsoluteBounds::unchecked_new(
            self.rel_start().unwrap().to_absolute(reference_time),
            self.rel_end().unwrap().to_absolute(reference_time),
        )
    }
}

impl ToRelative for RelativeBounds {
    type RelativeType = RelativeBounds;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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
    #[must_use]
    pub fn with_inclusivity(
        mut from: DateTime<Utc>,
        from_inclusivity: BoundInclusivity,
        mut to: DateTime<Utc>,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        if from > to {
            std::mem::swap(&mut from, &mut to);
        }

        Self::unchecked_with_inclusivity(from, from_inclusivity, to, to_inclusivity)
    }

    /// Returns the start time
    #[must_use]
    pub fn from(&self) -> DateTime<Utc> {
        self.from
    }

    /// Returns the end time
    #[must_use]
    pub fn to(&self) -> DateTime<Utc> {
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
    /// Returns boolean indicating whether the change was successful.
    pub fn set_from(&mut self, new_from: DateTime<Utc>) -> bool {
        if new_from > self.to {
            return false;
        }

        self.unchecked_set_from(new_from);
        true
    }

    /// Sets the to time of the interval
    /// 
    /// Returns boolean indicating whether the change was successful.
    pub fn set_to(&mut self, new_to: DateTime<Utc>) -> bool {
        if new_to < self.from {
            return false;
        }

        self.unchecked_set_to(new_to);
        true
    }

    /// Sets the inclusivity of the start bound
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.from_inclusivity = new_inclusivity;
    }

    /// Sets the inclusivity of the end bound
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.to_inclusivity = new_inclusivity;
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
        AbsoluteBounds::unchecked_new(
            AbsoluteStartBound::Finite(self.from, self.from_inclusivity),
            AbsoluteEndBound::Finite(self.to, self.to_inclusivity),
        )
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
    #[must_use]
    pub fn with_inclusivity(
        offset: Duration,
        start_inclusivity: BoundInclusivity,
        length: Duration,
        end_inclusivity: BoundInclusivity,
    ) -> Self {
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
    pub fn set_length(&mut self, new_length: Duration) {
        self.length = new_length;
    }

    /// Sets the inclusivity of the start bound
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.from_inclusivity = new_inclusivity;
    }

    /// Sets the inclusivity of the end bound
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.to_inclusivity = new_inclusivity;
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
        RelativeBounds::new(
            RelativeStartBound::Finite(self.offset, self.from_inclusivity),
            RelativeEndBound::Finite(self.offset + self.length, self.to_inclusivity),
        )
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
        precision.try_precise_time(self.reference_time)
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
        if self.opening_direction == OpeningDirection::ToFuture {
            return AbsoluteBounds::new(
                AbsoluteStartBound::Finite(self.reference_time, self.reference_time_inclusivity),
                AbsoluteEndBound::InfiniteFuture,
            );
        }

        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(self.reference_time, self.reference_time_inclusivity),
        )
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
        if self.opening_direction == OpeningDirection::ToFuture {
            return RelativeBounds::new(
                RelativeStartBound::Finite(self.offset, self.reference_time_inclusivity),
                RelativeEndBound::InfiniteFuture,
            );
        }

        RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(self.offset, self.reference_time_inclusivity),
        )
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
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
    }
}

impl HasRelativeBounds for OpenInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
    }
}

impl ToAbsolute for OpenInterval {
    type AbsoluteType = OpenInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for OpenInterval {
    type RelativeType = OpenInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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

impl HasAbsoluteBounds for EmptyInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::new_empty()
    }
}

impl HasRelativeBounds for EmptyInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new_empty()
    }
}

impl ToAbsolute for EmptyInterval {
    type AbsoluteType = EmptyInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToRelative for EmptyInterval {
    type RelativeType = EmptyInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
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

        if value.is_empty() {
            return AbsoluteInterval::Empty(EmptyInterval);
        }

        match (value.abs_start().unwrap(), value.abs_end().unwrap()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => AbsoluteInterval::Open(OpenInterval),
            (StartB::InfinitePast, EndB::Finite(time, inclusivity)) => {
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(time, inclusivity), EndB::InfiniteFuture) => {
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (StartB::Finite(start_time, start_inclusivity), EndB::Finite(end_time, end_inclusivity)) => {
                AbsoluteInterval::Closed(ClosedAbsoluteInterval::unchecked_with_inclusivity(
                    start_time,
                    start_inclusivity,
                    end_time,
                    end_inclusivity,
                ))
            }
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

        if value.is_empty() {
            return RelativeInterval::Empty(EmptyInterval);
        }

        match (value.rel_start().unwrap(), value.rel_end().unwrap()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => RelativeInterval::Open(OpenInterval),
            (StartB::InfinitePast, EndB::Finite(offset, inclusivity)) => {
                RelativeInterval::HalfOpen(HalfOpenRelativeInterval::with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(offset, inclusivity), EndB::InfiniteFuture) => {
                RelativeInterval::HalfOpen(HalfOpenRelativeInterval::with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (StartB::Finite(start_offset, start_inclusivity), EndB::Finite(end_offset, end_inclusivity)) => {
                RelativeInterval::Closed(ClosedRelativeInterval::with_inclusivity(
                    start_offset,
                    start_inclusivity,
                    end_offset - start_offset,
                    end_inclusivity,
                ))
            }
        }
    }
}

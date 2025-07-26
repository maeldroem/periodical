//! Absolute intervals

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use chrono::{DateTime, Utc};

use crate::intervals::meta::Interval;

use super::meta::{BoundInclusivity, Duration as IntervalDuration, OpeningDirection, Openness, Relativity};
use super::prelude::*;
use super::special::{EmptyInterval, OpenInterval};

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

/// An absolute start bound, including [inclusivity](BoundInclusivity)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteStartBound {
    Finite(AbsoluteFiniteBound),
    InfinitePast,
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

impl Interval for ClosedAbsoluteInterval {}

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

impl Interval for HalfOpenAbsoluteInterval {}

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

/// Represents any absolute interval, including empty and open intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbsoluteInterval {
    Closed(ClosedAbsoluteInterval),
    HalfOpen(HalfOpenAbsoluteInterval),
    Open(OpenInterval),
    Empty(EmptyInterval),
}

impl Interval for AbsoluteInterval {}

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

impl Emptiable for AbsoluteInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
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

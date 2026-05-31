//! Relative bound pair
//!
//! Represents a pair composed of a [`RelativeStartBound`] and a
//! [`RelativeEndBound`].
//!
//! Contrary to a specific interval type, it doesn't keep any
//! [`Openness`]-related invariants, making it
//! useful for changing an interval's openness easily.
//!
//! Relative bound pairs are also used for when, after a given operation, the
//! openness of the resulting interval can't be guaranteed at compile-time. This
//! also gives the opportunity for the caller to make a choice of whether to
//! include/exclude the resulting interval on an openness-related basis.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::RangeBounds;

use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasBoundInclusivity,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    IsEmpty,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
    check_relative_start_end_bounds_for_interval_creation,
    prepare_relative_bound_pair_for_interval_creation,
};
use crate::intervals::special::UnboundedInterval;

/// Possession of non-empty relative bound pair
pub trait HasRelativeBoundPair: HasEmptiableRelativeBoundPair {
    /// Returns the relative bound pair of the object
    #[must_use]
    fn rel_bound_pair(&self) -> RelativeBoundPair;

    /// Returns the relative start bound of the object
    #[must_use]
    fn rel_start(&self) -> RelativeStartBound;

    /// Returns the relative end bound of the object
    #[must_use]
    fn rel_end(&self) -> RelativeEndBound;
}

/// Pair of [`RelativeStartBound`] and [`RelativeEndBound`]
///
/// [`RelativeBoundPair`] should be used when you want a non-empty interval
/// which don't need to conserve a given [`Openness`].
///
/// # Invariants
///
/// 1. The bounds are in chronological order
/// 2. If the bounds have the same offset, their inclusivities should be
///    [inclusive](crate::intervals::meta::BoundInclusivity::Inclusive) for both
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeBoundPair {
    start: RelativeStartBound,
    end: RelativeEndBound,
}

impl RelativeBoundPair {
    /// Creates a new [`RelativeBoundPair`] without checking if it violates
    /// invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// // Start and end are not in chronological order!
    /// let start_offset = SignedDuration::from_hours(16);
    /// let end_offset = SignedDuration::from_hours(8);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let bounds = RelativeBoundPair::unchecked_new(start, end);
    ///
    /// assert_eq!(bounds.start(), start);
    /// assert_eq!(bounds.end(), end);
    /// ```
    #[must_use]
    pub fn unchecked_new(start: RelativeStartBound, end: RelativeEndBound) -> Self {
        RelativeBoundPair {
            start,
            end,
        }
    }

    /// Creates a new [`RelativeBoundPair`]
    ///
    /// Uses [`prepare_relative_bound_pair_for_interval_creation`] under the
    /// hood for making sure the bounds respect the invariants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// // Start and end are not in chronological order!
    /// let start_offset = SignedDuration::from_hours(16);
    /// let end_offset = SignedDuration::from_hours(8);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let bounds = RelativeBoundPair::new(start, end);
    ///
    /// // Now the start and end are in chronological order
    /// assert_eq!(bounds.start(), end);
    /// assert_eq!(bounds.end(), start);
    /// ```
    #[must_use]
    pub fn new(mut start: RelativeStartBound, mut end: RelativeEndBound) -> Self {
        prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);
        Self::unchecked_new(start, end)
    }

    /// Creates an [`RelativeBoundPair`] from a [`SignedDuration`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let start = SignedDuration::from_hours(-5);
    /// let end = SignedDuration::from_hours(20);
    ///
    /// let bounds = RelativeBoundPair::from_range(start..end);
    ///
    /// assert_eq!(
    ///     bounds.start(),
    ///     RelativeFiniteBoundPosition::new(start).to_start_bound(),
    /// );
    /// assert_eq!(
    ///     bounds.end(),
    ///     RelativeFiniteBoundPosition::new_with_inclusivity(end, BoundInclusivity::Exclusive,)
    ///         .to_end_bound(),
    /// );
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        RelativeBoundPair::new(
            RelativeStartBound::from(range.start_bound().cloned()),
            RelativeEndBound::from(range.end_bound().cloned()),
        )
    }

    /// Returns the relative start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let bounds = RelativeBoundPair::new(start, end);
    ///
    /// assert_eq!(bounds.start(), start);
    /// ```
    #[must_use]
    pub fn start(&self) -> RelativeStartBound {
        self.start
    }

    /// Returns the relative end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let bounds = RelativeBoundPair::new(start, end);
    ///
    /// assert_eq!(bounds.end(), end);
    /// ```
    #[must_use]
    pub fn end(&self) -> RelativeEndBound {
        self.end
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let mut bounds = RelativeBoundPair::new(start, end);
    ///
    /// let new_start_offset = SignedDuration::from_hours(18);
    /// let new_start = RelativeFiniteBoundPosition::new(new_start_offset).to_start_bound();
    ///
    /// // New start is past the end
    /// bounds.unchecked_set_start(new_start);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), new_start);
    /// assert_eq!(bounds.end(), end);
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: RelativeStartBound) {
        self.start = new_start;
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let mut bounds = RelativeBoundPair::new(start, end);
    ///
    /// let new_end_offset = SignedDuration::from_hours(6);
    /// let new_end = RelativeFiniteBoundPosition::new(new_end_offset).to_end_bound();
    ///
    /// // New end is before the start
    /// bounds.unchecked_set_end(new_end);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), start);
    /// assert_eq!(bounds.end(), new_end);
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: RelativeEndBound) {
        self.end = new_end;
    }

    /// Sets the start bound
    ///
    /// Returns whether the operation was successful and the start bound
    /// modified. If the given new start bound violates the invariants, the
    /// method simply returns `false` without changing the start bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let mut bounds = RelativeBoundPair::new(start, end);
    ///
    /// let new_start_offset = SignedDuration::from_hours(18);
    /// let new_start = RelativeFiniteBoundPosition::new(new_start_offset).to_start_bound();
    ///
    /// // New start is past the end, and therefore gets ignored
    /// let was_successful = bounds.set_start(new_start);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), start);
    /// assert_eq!(bounds.end(), end);
    /// ```
    pub fn set_start(&mut self, new_start: RelativeStartBound) -> bool {
        match check_relative_start_end_bounds_for_interval_creation(&new_start, &self.end()) {
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
    /// If the given new end bound violates the invariants, the method simply
    /// returns `false` without changing the end bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
    ///
    /// let mut bounds = RelativeBoundPair::new(start, end);
    ///
    /// let new_end_offset = SignedDuration::from_hours(6);
    /// let new_end = RelativeFiniteBoundPosition::new(new_end_offset).to_end_bound();
    ///
    /// // New end is before the start, and therefore gets ignored
    /// let was_successful = bounds.set_end(new_end);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), start);
    /// assert_eq!(bounds.end(), end);
    /// ```
    pub fn set_end(&mut self, new_end: RelativeEndBound) -> bool {
        match check_relative_start_end_bounds_for_interval_creation(&self.start(), &new_end) {
            Ok(()) => {
                self.unchecked_set_end(new_end);
                true
            },
            Err(_) => false,
        }
    }

    /// Compares two [`RelativeBoundPair`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelativeBoundPair;
    /// # let mut bounds: [RelativeBoundPair; 0] = [];
    /// bounds.sort_by(RelativeBoundPair::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match self.cmp(other) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.end.cmp(&other.end).reverse(),
            Ordering::Greater => Ordering::Greater,
        }
    }

    /// Converts the [`RelativeBoundPair`] into [`RelativeInterval`]
    #[must_use]
    pub fn to_interval(self) -> RelativeInterval {
        RelativeInterval::from(self)
    }

    /// Converts the [`RelativeBoundPair`] into [`EmptiableRelativeInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableRelativeInterval {
        self.to_interval().to_emptiable()
    }

    /// Wraps the [`RelativeBoundPair`] in an [`EmptiableRelativeBoundPair`]
    #[must_use]
    pub fn to_emptiable(self) -> EmptiableRelativeBoundPair {
        EmptiableRelativeBoundPair::from(self)
    }
}

impl Interval for RelativeBoundPair {}

impl HasRelativeBoundPair for RelativeBoundPair {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        self.clone()
    }

    fn rel_start(&self) -> RelativeStartBound {
        self.start()
    }

    fn rel_end(&self) -> RelativeEndBound {
        self.end()
    }
}

impl HasDuration for RelativeBoundPair {
    fn duration(&self) -> IntervalDuration {
        match (self.start(), self.end()) {
            (RelativeStartBound::InfinitePast, _) | (_, RelativeEndBound::InfiniteFuture) => IntervalDuration::Infinite,
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
                IntervalDuration::Finite(
                    finite_end
                        .pos()
                        .offset()
                        .saturating_sub(finite_start.pos().offset())
                        .unsigned_abs(),
                    Epsilon::from((finite_start.pos().inclusivity(), finite_end.pos().inclusivity())),
                )
            },
        }
    }
}

impl HasOpenness for RelativeBoundPair {
    fn openness(&self) -> Openness {
        match (self.start(), self.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => Openness::Unbounded,
            (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(_))
            | (RelativeStartBound::Finite(_), RelativeEndBound::InfiniteFuture) => Openness::HalfBounded,
            (RelativeStartBound::Finite(_), RelativeEndBound::Finite(_)) => Openness::Bounded,
        }
    }
}

impl HasRelativity for RelativeBoundPair {
    fn relativity(&self) -> Relativity {
        match (self.start(), self.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => Relativity::Any,
            _ => Relativity::Relative,
        }
    }
}

impl PartialOrd for RelativeBoundPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeBoundPair {
    fn cmp(&self, other: &Self) -> Ordering {
        // using the comparison of self.end and other.end as a way to disambiguate when
        // the two starts are equal leads to side-effects, like when we store
        // absolute bounds inside a BTreeSet, then if we use `range()`,
        // one can be considered out of the range when it shouldn't.
        self.start.cmp(&other.start)
    }
}

impl IsEmpty for RelativeBoundPair {
    fn is_empty(&self) -> bool {
        false
    }
}

/// Converts `(Option<SignedDuration>, Option<SignedDuration>)` into [`RelativeBoundPair`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl From<(Option<SignedDuration>, Option<SignedDuration>)> for RelativeBoundPair {
    fn from((start_opt, end_opt): (Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        let start = RelativeStartBound::from(start_opt);
        let end = RelativeEndBound::from(end_opt);
        RelativeBoundPair::new(start, end)
    }
}

/// Converts `(Option<(SignedDuration, BoundInclusivity)>, Option<(SignedDuration, BoundInclusivity)>)`
/// into [`RelativeBoundPair`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl
    From<(
        Option<(SignedDuration, BoundInclusivity)>,
        Option<(SignedDuration, BoundInclusivity)>,
    )> for RelativeBoundPair
{
    fn from(
        (start_opt, end_opt): (
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        let start = RelativeStartBound::from(start_opt);
        let end = RelativeEndBound::from(end_opt);
        Self::new(start, end)
    }
}

impl From<BoundedRelativeInterval> for RelativeBoundPair {
    fn from(value: BoundedRelativeInterval) -> Self {
        value.rel_bound_pair()
    }
}

impl From<HalfBoundedRelativeInterval> for RelativeBoundPair {
    fn from(value: HalfBoundedRelativeInterval) -> Self {
        value.rel_bound_pair()
    }
}

impl From<RelativeInterval> for RelativeBoundPair {
    fn from(value: RelativeInterval) -> Self {
        value.rel_bound_pair()
    }
}

impl From<UnboundedInterval> for RelativeBoundPair {
    fn from(value: UnboundedInterval) -> Self {
        value.rel_bound_pair()
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeBoundPair`]
/// into [`RelativeBoundPair`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelativeBoundPairTryFromEmptiableRelativeBoundPairError;

impl Display for RelativeBoundPairTryFromEmptiableRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeBoundPair` into `RelativeBoundPair`"
        )
    }
}

impl Error for RelativeBoundPairTryFromEmptiableRelativeBoundPairError {}

impl TryFrom<EmptiableRelativeBoundPair> for RelativeBoundPair {
    type Error = RelativeBoundPairTryFromEmptiableRelativeBoundPairError;

    fn try_from(value: EmptiableRelativeBoundPair) -> Result<Self, Self::Error> {
        value
            .bound()
            .ok_or(RelativeBoundPairTryFromEmptiableRelativeBoundPairError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeInterval`]
/// into [`RelativeBoundPair`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativeBoundPairTryFromEmptiableRelativeIntervalError;

impl Display for RelativeBoundPairTryFromEmptiableRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeInterval` into `RelativeBoundPair`"
        )
    }
}

impl Error for RelativeBoundPairTryFromEmptiableRelativeIntervalError {}

impl TryFrom<EmptiableRelativeInterval> for RelativeBoundPair {
    type Error = RelativeBoundPairTryFromEmptiableRelativeIntervalError;

    fn try_from(value: EmptiableRelativeInterval) -> Result<Self, Self::Error> {
        Ok(value
            .bound()
            .ok_or(RelativeBoundPairTryFromEmptiableRelativeIntervalError)?
            .rel_bound_pair())
    }
}

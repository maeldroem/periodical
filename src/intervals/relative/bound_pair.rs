//! Relative bound pair
//!
//! Represents a pair composed of a [`RelStartBound`] and a
//! [`RelEndBound`].
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
    HasIntervalTypeWithRel,
    HasOpenness,
    HasRelativity,
    Interval,
    IntervalTypeWithRel,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    RelEndBound,
    RelInterval,
    RelStartBound,
    check_rel_start_end_bounds_for_interval_creation,
    prepare_rel_start_end_bounds_for_interval_creation,
};
use crate::intervals::special::UnboundedInterval;

/// Possession of a **non-empty** relative bound pair
pub trait HasRelBoundPair: HasEmptiableRelBoundPair {
    /// Returns the relative bound pair
    #[must_use]
    fn rel_bound_pair(&self) -> RelBoundPair;

    /// Returns the relative start bound
    #[must_use]
    fn rel_start(&self) -> RelStartBound;

    /// Returns the relative end bound
    #[must_use]
    fn rel_end(&self) -> RelEndBound;
}

/// Pair of [`RelStartBound`] and [`RelEndBound`]
///
/// [`RelBoundPair`] should be used when you want a non-empty interval
/// which don't need to conserve a given [`Openness`].
///
/// # Invariants
///
/// 1. The bounds are in chronological order
/// 2. If the bounds have the same offset, their inclusivities should be [inclusive](BoundInclusivity::Inclusive) for
///    both
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelBoundPair {
    start: RelStartBound,
    end: RelEndBound,
}

impl RelBoundPair {
    /// Creates a new [`RelBoundPair`] without checking if it violates
    /// invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// // Start and end are not in chronological order!
    /// let start_offset = SignedDuration::from_hours(16);
    /// let end_offset = SignedDuration::from_hours(8);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let bound_pair = RelBoundPair::unchecked_new(start, end);
    ///
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), end);
    /// ```
    #[must_use]
    pub fn unchecked_new(start: RelStartBound, end: RelEndBound) -> Self {
        RelBoundPair {
            start,
            end,
        }
    }

    /// Creates a new [`RelBoundPair`]
    ///
    /// Uses [`prepare_rel_start_end_bounds_for_interval_creation`] under the
    /// hood for making sure the bounds respect the invariants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// // Start and end are not in chronological order!
    /// let start_offset = SignedDuration::from_hours(16);
    /// let end_offset = SignedDuration::from_hours(8);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let bound_pair = RelBoundPair::new(start, end);
    ///
    /// // Now the start and end are in chronological order
    /// assert_eq!(
    ///     bound_pair.start(),
    ///     RelFiniteBoundPos::new(end_offset).to_start_bound()
    /// );
    /// assert_eq!(
    ///     bound_pair.end(),
    ///     RelFiniteBoundPos::new(start_offset).to_end_bound()
    /// );
    /// ```
    #[must_use]
    pub fn new(mut start: RelStartBound, mut end: RelEndBound) -> Self {
        prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);
        Self::unchecked_new(start, end)
    }

    /// Creates an [`RelBoundPair`] from a [`SignedDuration`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let start = SignedDuration::from_hours(-5);
    /// let end = SignedDuration::from_hours(20);
    ///
    /// let bound_pair = RelBoundPair::from_range(start..end);
    ///
    /// assert_eq!(
    ///     bound_pair.start(),
    ///     RelFiniteBoundPos::new(start).to_start_bound(),
    /// );
    /// assert_eq!(
    ///     bound_pair.end(),
    ///     RelFiniteBoundPos::new_with_incl(end, BoundInclusivity::Exclusive).to_end_bound(),
    /// );
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        RelBoundPair::new(
            RelStartBound::from(range.start_bound().cloned()),
            RelEndBound::from(range.end_bound().cloned()),
        )
    }

    /// Returns the relative start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let bound_pair = RelBoundPair::new(start, end);
    ///
    /// assert_eq!(bound_pair.start(), start);
    /// ```
    #[must_use]
    pub fn start(&self) -> RelStartBound {
        self.start
    }

    /// Returns the relative end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let bound_pair = RelBoundPair::new(start, end);
    ///
    /// assert_eq!(bound_pair.end(), end);
    /// ```
    #[must_use]
    pub fn end(&self) -> RelEndBound {
        self.end
    }

    /// Compares two [`RelBoundPair`], if they have the same start,
    /// order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of starts, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelBoundPair;
    /// # let mut bound_pairs: [RelBoundPair; 0] = [];
    /// bound_pairs.sort_by(RelBoundPair::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match self
            .start()
            .bound_cmp(&other.start())
            .disambiguate(BoundOverlapDisambiguationRuleSet::Strict)
        {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self
                .end()
                .bound_cmp(&other.end())
                .disambiguate(BoundOverlapDisambiguationRuleSet::Strict)
                .reverse(),
            Ordering::Greater => Ordering::Greater,
        }
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let mut bound_pair = RelBoundPair::new(start, end);
    ///
    /// let new_start_offset = SignedDuration::from_hours(18);
    /// let new_start = RelFiniteBoundPos::new(new_start_offset).to_start_bound();
    ///
    /// // New start is past the end
    /// bound_pair.unchecked_set_start(new_start);
    ///
    /// // And yet stays in `bound_pair`
    /// assert_eq!(bound_pair.start(), new_start);
    /// assert_eq!(bound_pair.end(), end);
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: RelStartBound) {
        self.start = new_start;
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let mut bound_pair = RelBoundPair::new(start, end);
    ///
    /// let new_end_offset = SignedDuration::from_hours(6);
    /// let new_end = RelFiniteBoundPos::new(new_end_offset).to_end_bound();
    ///
    /// // New end is before the start
    /// bound_pair.unchecked_set_end(new_end);
    ///
    /// // And yet stays in `bound_pair`
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), new_end);
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: RelEndBound) {
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
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let mut bound_pair = RelBoundPair::new(start, end);
    ///
    /// let new_start_offset = SignedDuration::from_hours(18);
    /// let new_start = RelFiniteBoundPos::new(new_start_offset).to_start_bound();
    ///
    /// // New start is past the end, and therefore gets ignored
    /// let was_successful = bound_pair.set_start(new_start);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), end);
    /// ```
    pub fn set_start(&mut self, new_start: RelStartBound) -> bool {
        match check_rel_start_end_bounds_for_interval_creation(&new_start, &self.end()) {
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
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset).to_start_bound();
    /// let end = RelFiniteBoundPos::new(end_offset).to_end_bound();
    ///
    /// let mut bound_pair = RelBoundPair::new(start, end);
    ///
    /// let new_end_offset = SignedDuration::from_hours(6);
    /// let new_end = RelFiniteBoundPos::new(new_end_offset).to_end_bound();
    ///
    /// // New end is before the start, and therefore gets ignored
    /// let was_successful = bound_pair.set_end(new_end);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), end);
    /// ```
    pub fn set_end(&mut self, new_end: RelEndBound) -> bool {
        match check_rel_start_end_bounds_for_interval_creation(&self.start(), &new_end) {
            Ok(()) => {
                self.unchecked_set_end(new_end);
                true
            },
            Err(_) => false,
        }
    }

    /// Converts `self` into [`RelInterval`]
    #[must_use]
    pub fn to_interval(self) -> RelInterval {
        RelInterval::from(self)
    }

    /// Converts `self` into [`EmptiableRelInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableRelInterval {
        self.to_interval().to_emptiable()
    }

    /// Wraps `self` in an [`EmptiableRelBoundPair`]
    #[must_use]
    pub fn to_emptiable(self) -> EmptiableRelBoundPair {
        EmptiableRelBoundPair::from(self)
    }
}

impl Interval for RelBoundPair {}

impl HasRelBoundPair for RelBoundPair {
    fn rel_bound_pair(&self) -> RelBoundPair {
        self.clone()
    }

    fn rel_start(&self) -> RelStartBound {
        self.start()
    }

    fn rel_end(&self) -> RelEndBound {
        self.end()
    }
}

impl HasDuration for RelBoundPair {
    fn duration(&self) -> IntervalDuration {
        match (self.start(), self.end()) {
            (RelStartBound::InfinitePast, _) | (_, RelEndBound::InfiniteFuture) => IntervalDuration::Infinite,
            (RelStartBound::Finite(finite_start), RelEndBound::Finite(finite_end)) => IntervalDuration::Finite(
                finite_end
                    .pos()
                    .offset()
                    .saturating_sub(finite_start.pos().offset())
                    .unsigned_abs(),
                Epsilon::from((finite_start.pos().inclusivity(), finite_end.pos().inclusivity())),
            ),
        }
    }
}

impl HasOpenness for RelBoundPair {
    fn openness(&self) -> Openness {
        match (self.start(), self.end()) {
            (RelStartBound::InfinitePast, RelEndBound::InfiniteFuture) => Openness::Unbounded,
            (RelStartBound::InfinitePast, RelEndBound::Finite(_))
            | (RelStartBound::Finite(_), RelEndBound::InfiniteFuture) => Openness::HalfBounded,
            (RelStartBound::Finite(_), RelEndBound::Finite(_)) => Openness::Bounded,
        }
    }
}

impl HasRelativity for RelBoundPair {
    fn relativity(&self) -> Relativity {
        match (self.start(), self.end()) {
            (RelStartBound::InfinitePast, RelEndBound::InfiniteFuture) => Relativity::Any,
            _ => Relativity::Relative,
        }
    }
}

impl PartialOrd for RelBoundPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelBoundPair {
    fn cmp(&self, other: &Self) -> Ordering {
        // using the comparison of self.end and other.end as a way to disambiguate when
        // the two starts are equal leads to side-effects, like when we store
        // absolute bounds inside a BTreeSet, then if we use `range()`,
        // one can be considered out of the range when it shouldn't.
        self.start()
            .bound_cmp(&other.start())
            .disambiguate(BoundOverlapDisambiguationRuleSet::Strict)
    }
}

impl IsEmpty for RelBoundPair {
    fn is_empty(&self) -> bool {
        false
    }
}

impl HasIntervalTypeWithRel for RelBoundPair {
    fn interval_type_with_rel(&self) -> IntervalTypeWithRel {
        match (self.start(), self.end()) {
            (RelStartBound::InfinitePast, RelEndBound::InfiniteFuture) => IntervalTypeWithRel::Unbounded,
            (RelStartBound::InfinitePast, RelEndBound::Finite(_)) => {
                IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast)
            },
            (RelStartBound::Finite(_), RelEndBound::InfiniteFuture) => {
                IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture)
            },
            (RelStartBound::Finite(_), RelEndBound::Finite(_)) => IntervalTypeWithRel::RelBounded,
        }
    }
}

/// Converts `(Option<SignedDuration>, Option<SignedDuration>)` into [`RelBoundPair`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl From<(Option<SignedDuration>, Option<SignedDuration>)> for RelBoundPair {
    fn from((start_opt, end_opt): (Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        let start = RelStartBound::from(start_opt);
        let end = RelEndBound::from(end_opt);
        RelBoundPair::new(start, end)
    }
}

/// Converts `(Option<(SignedDuration, BoundInclusivity)>, Option<(SignedDuration, BoundInclusivity)>)`
/// into [`RelBoundPair`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl
    From<(
        Option<(SignedDuration, BoundInclusivity)>,
        Option<(SignedDuration, BoundInclusivity)>,
    )> for RelBoundPair
{
    fn from(
        (start_opt, end_opt): (
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        let start = RelStartBound::from(start_opt);
        let end = RelEndBound::from(end_opt);
        Self::new(start, end)
    }
}

impl From<BoundedRelInterval> for RelBoundPair {
    fn from(value: BoundedRelInterval) -> Self {
        value.rel_bound_pair()
    }
}

impl From<HalfBoundedRelInterval> for RelBoundPair {
    fn from(value: HalfBoundedRelInterval) -> Self {
        value.rel_bound_pair()
    }
}

impl From<RelInterval> for RelBoundPair {
    fn from(value: RelInterval) -> Self {
        value.rel_bound_pair()
    }
}

impl From<UnboundedInterval> for RelBoundPair {
    fn from(value: UnboundedInterval) -> Self {
        value.rel_bound_pair()
    }
}

/// Error that can occur when trying to convert [`EmptiableRelBoundPair`]
/// into [`RelBoundPair`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelBoundPairTryFromEmptiableRelBoundPairError;

impl Display for RelBoundPairTryFromEmptiableRelBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelBoundPair` into `RelBoundPair`"
        )
    }
}

impl Error for RelBoundPairTryFromEmptiableRelBoundPairError {}

impl TryFrom<EmptiableRelBoundPair> for RelBoundPair {
    type Error = RelBoundPairTryFromEmptiableRelBoundPairError;

    fn try_from(value: EmptiableRelBoundPair) -> Result<Self, Self::Error> {
        value.bound().ok_or(RelBoundPairTryFromEmptiableRelBoundPairError)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelInterval`]
/// into [`RelBoundPair`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelBoundPairTryFromEmptiableRelIntervalError;

impl Display for RelBoundPairTryFromEmptiableRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelInterval` into `RelBoundPair`"
        )
    }
}

impl Error for RelBoundPairTryFromEmptiableRelIntervalError {}

impl TryFrom<EmptiableRelInterval> for RelBoundPair {
    type Error = RelBoundPairTryFromEmptiableRelIntervalError;

    fn try_from(value: EmptiableRelInterval) -> Result<Self, Self::Error> {
        Ok(value
            .bound()
            .ok_or(RelBoundPairTryFromEmptiableRelIntervalError)?
            .rel_bound_pair())
    }
}

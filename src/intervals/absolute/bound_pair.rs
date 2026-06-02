//! Absolute bound pair
//!
//! Represents a pair composed of an [`AbsoluteStartBound`] and an
//! [`AbsoluteEndBound`].
//!
//! Contrary to a specific interval type, it doesn't keep any
//! [`Openness`]-related invariants, making it
//! useful for changing an interval's openness easily.
//!
//! Absolute bound pairs are also used for when, after a given operation, the
//! openness of the resulting interval can't be guaranteed at compile-time. This
//! also gives the opportunity for the caller to make a choice of whether to
//! include/exclude the resulting interval on an openness-related basis.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::RangeBounds;

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasEmptiableAbsoluteBoundPair,
    check_absolute_start_end_bounds_for_interval_creation,
    prepare_absolute_bound_pair_for_interval_creation,
};
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
use crate::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
use crate::intervals::special::UnboundedInterval;

/// Possession of a **non-empty** absolute bound pair
pub trait HasAbsoluteBoundPair: HasEmptiableAbsoluteBoundPair {
    /// Returns the absolute bound pair
    #[must_use]
    fn abs_bound_pair(&self) -> AbsoluteBoundPair;

    /// Returns the absolute start bound
    #[must_use]
    fn abs_start(&self) -> AbsoluteStartBound;

    /// Returns the absolute end bound
    #[must_use]
    fn abs_end(&self) -> AbsoluteEndBound;
}

/// Pair of [`AbsoluteStartBound`] and [`AbsoluteEndBound`]
///
/// [`AbsoluteBoundPair`] should be used when you want a non-empty interval
/// which don't need to conserve a given [`Openness`].
///
/// # Invariants
///
/// 1. The bounds are in chronological order
/// 2. If the bounds have the same time, their inclusivities should be [inclusive](BoundInclusivity::Inclusive) for both
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteBoundPair {
    start: AbsoluteStartBound,
    end: AbsoluteEndBound,
}

impl AbsoluteBoundPair {
    /// Creates a new [`AbsoluteBoundPair`] without checking if it violates
    /// invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// // Start and end are not in chronological order!
    /// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let bound_pair = AbsoluteBoundPair::unchecked_new(start, end);
    ///
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn unchecked_new(start: AbsoluteStartBound, end: AbsoluteEndBound) -> Self {
        AbsoluteBoundPair {
            start,
            end,
        }
    }

    /// Creates a new [`AbsoluteBoundPair`]
    ///
    /// Uses [`prepare_absolute_bound_pair_for_interval_creation`] under the
    /// hood for making sure the bounds respect the invariants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// // Start and end are not in chronological order!
    /// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let bound_pair = AbsoluteBoundPair::new(start, end);
    ///
    /// // Now the start and end are in chronological order
    /// assert_eq!(
    ///     bound_pair.start(),
    ///     AbsoluteFiniteBoundPosition::new(end_time).to_start_bound()
    /// );
    /// assert_eq!(
    ///     bound_pair.end(),
    ///     AbsoluteFiniteBoundPosition::new(start_time).to_end_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new(mut start: AbsoluteStartBound, mut end: AbsoluteEndBound) -> Self {
        prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);
        Self::unchecked_new(start, end)
    }

    /// Creates an [`AbsoluteBoundPair`] from a [`Timestamp`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-05-01 00:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bound_pair = AbsoluteBoundPair::from_range(start..end);
    ///
    /// assert_eq!(
    ///     bound_pair.start(),
    ///     AbsoluteFiniteBoundPosition::new(start).to_start_bound(),
    /// );
    /// assert_eq!(
    ///     bound_pair.end(),
    ///     AbsoluteFiniteBoundPosition::new_with_inclusivity(end, BoundInclusivity::Exclusive)
    ///         .to_end_bound(),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        AbsoluteBoundPair::new(
            AbsoluteStartBound::from(range.start_bound().cloned()),
            AbsoluteEndBound::from(range.end_bound().cloned()),
        )
    }

    /// Returns the absolute start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let bound_pair = AbsoluteBoundPair::new(start, end);
    ///
    /// assert_eq!(bound_pair.start(), start);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start(&self) -> AbsoluteStartBound {
        self.start
    }

    /// Returns the absolute end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let bound_pair = AbsoluteBoundPair::new(start, end);
    ///
    /// assert_eq!(bound_pair.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(&self) -> AbsoluteEndBound {
        self.end
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let mut bound_pair = AbsoluteBoundPair::new(start, end);
    ///
    /// let new_start_time = "2025-01-01 18:00:00Z".parse::<Timestamp>()?;
    /// let new_start = AbsoluteFiniteBoundPosition::new(new_start_time).to_start_bound();
    ///
    /// // New start is past the end
    /// bound_pair.unchecked_set_start(new_start);
    ///
    /// // And yet stays in `bound_pair`
    /// assert_eq!(bound_pair.start(), new_start);
    /// assert_eq!(bound_pair.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: AbsoluteStartBound) {
        self.start = new_start;
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let mut bound_pair = AbsoluteBoundPair::new(start, end);
    ///
    /// let new_end_time = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    /// let new_end = AbsoluteFiniteBoundPosition::new(new_end_time).to_end_bound();
    ///
    /// // New end is before the start
    /// bound_pair.unchecked_set_end(new_end);
    ///
    /// // And yet stays in `bound_pair`
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), new_end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: AbsoluteEndBound) {
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
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let mut bound_pair = AbsoluteBoundPair::new(start, end);
    ///
    /// let new_start_time = "2025-01-01 18:00:00Z".parse::<Timestamp>()?;
    /// let new_start = AbsoluteFiniteBoundPosition::new(new_start_time).to_start_bound();
    ///
    /// // New start is past the end, and therefore gets ignored
    /// let was_successful = bound_pair.set_start(new_start);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_start(&mut self, new_start: AbsoluteStartBound) -> bool {
        match check_absolute_start_end_bounds_for_interval_creation(&new_start, &self.end()) {
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
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time).to_start_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time).to_end_bound();
    ///
    /// let mut bound_pair = AbsoluteBoundPair::new(start, end);
    ///
    /// let new_end_time = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    /// let new_end = AbsoluteFiniteBoundPosition::new(new_end_time).to_end_bound();
    ///
    /// // New end is before the start, and therefore gets ignored
    /// let was_successful = bound_pair.set_end(new_end);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bound_pair.start(), start);
    /// assert_eq!(bound_pair.end(), end);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_end(&mut self, new_end: AbsoluteEndBound) -> bool {
        match check_absolute_start_end_bounds_for_interval_creation(&self.start(), &new_end) {
            Ok(()) => {
                self.unchecked_set_end(new_end);
                true
            },
            Err(_) => false,
        }
    }

    /// Compares two [`AbsoluteBoundPair`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteBoundPair;
    /// # let mut bound_pairs: [AbsoluteBoundPair; 0] = [];
    /// bound_pairs.sort_by(AbsoluteBoundPair::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match self
            .start()
            .bound_cmp(&other.end())
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

    /// Converts `self` into [`AbsoluteInterval`]
    #[must_use]
    pub fn to_interval(self) -> AbsoluteInterval {
        AbsoluteInterval::from(self)
    }

    /// Converts `self` into [`EmptiableAbsoluteInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableAbsoluteInterval {
        self.to_interval().to_emptiable()
    }

    /// Wraps `self` in an [`EmptiableAbsoluteBoundPair`]
    #[must_use]
    pub fn to_emptiable(self) -> EmptiableAbsoluteBoundPair {
        EmptiableAbsoluteBoundPair::from(self)
    }
}

impl Interval for AbsoluteBoundPair {}

impl HasAbsoluteBoundPair for AbsoluteBoundPair {
    fn abs_bound_pair(&self) -> AbsoluteBoundPair {
        self.clone()
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        self.start()
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        self.end()
    }
}

impl HasDuration for AbsoluteBoundPair {
    fn duration(&self) -> IntervalDuration {
        match (self.start(), self.end()) {
            (AbsoluteStartBound::InfinitePast, _) | (_, AbsoluteEndBound::InfiniteFuture) => IntervalDuration::Infinite,
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
                IntervalDuration::Finite(
                    finite_end
                        .pos()
                        .time()
                        .duration_since(finite_start.pos().time())
                        .unsigned_abs(),
                    Epsilon::from((finite_start.pos().inclusivity(), finite_end.pos().inclusivity())),
                )
            },
        }
    }
}

impl HasOpenness for AbsoluteBoundPair {
    fn openness(&self) -> Openness {
        match (self.start(), self.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture) => Openness::Unbounded,
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(_))
            | (AbsoluteStartBound::Finite(_), AbsoluteEndBound::InfiniteFuture) => Openness::HalfBounded,
            (AbsoluteStartBound::Finite(_), AbsoluteEndBound::Finite(_)) => Openness::Bounded,
        }
    }
}

impl HasRelativity for AbsoluteBoundPair {
    fn relativity(&self) -> Relativity {
        match (self.start(), self.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture) => Relativity::Any,
            _ => Relativity::Absolute,
        }
    }
}

impl PartialOrd for AbsoluteBoundPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteBoundPair {
    fn cmp(&self, other: &Self) -> Ordering {
        // using the comparison of self.end and other.end as a way to disambiguate when
        // the two starts are equal leads to side-effects, like when we store
        // absolute bound pair inside a BTreeSet, then if we use `range()`,
        // one can be considered out of the range when it shouldn't.
        self.start()
            .bound_cmp(&other.start())
            .disambiguate(BoundOverlapDisambiguationRuleSet::Strict)
    }
}

impl IsEmpty for AbsoluteBoundPair {
    fn is_empty(&self) -> bool {
        false
    }
}

/// Converts `(Option<Timestamp>, Option<Timestamp>)` into [`AbsoluteBoundPair`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl From<(Option<Timestamp>, Option<Timestamp>)> for AbsoluteBoundPair {
    fn from((start_opt, end_opt): (Option<Timestamp>, Option<Timestamp>)) -> Self {
        let start = AbsoluteStartBound::from(start_opt);
        let end = AbsoluteEndBound::from(end_opt);
        AbsoluteBoundPair::new(start, end)
    }
}

/// Converts `(Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp, BoundInclusivity)>)`
/// into [`AbsoluteBoundPair`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl
    From<(
        Option<(Timestamp, BoundInclusivity)>,
        Option<(Timestamp, BoundInclusivity)>,
    )> for AbsoluteBoundPair
{
    fn from(
        (start_opt, end_opt): (
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        ),
    ) -> Self {
        let start = AbsoluteStartBound::from(start_opt);
        let end = AbsoluteEndBound::from(end_opt);
        Self::new(start, end)
    }
}

impl From<BoundedAbsoluteInterval> for AbsoluteBoundPair {
    fn from(value: BoundedAbsoluteInterval) -> Self {
        value.abs_bound_pair()
    }
}

impl From<HalfBoundedAbsoluteInterval> for AbsoluteBoundPair {
    fn from(value: HalfBoundedAbsoluteInterval) -> Self {
        value.abs_bound_pair()
    }
}

impl From<AbsoluteInterval> for AbsoluteBoundPair {
    fn from(value: AbsoluteInterval) -> Self {
        value.abs_bound_pair()
    }
}

impl From<UnboundedInterval> for AbsoluteBoundPair {
    fn from(value: UnboundedInterval) -> Self {
        value.abs_bound_pair()
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteBoundPair`]
/// into [`AbsoluteBoundPair`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError;

impl Display for AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteBoundPair` into `AbsoluteBoundPair`"
        )
    }
}

impl Error for AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError {}

impl TryFrom<EmptiableAbsoluteBoundPair> for AbsoluteBoundPair {
    type Error = AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError;

    fn try_from(value: EmptiableAbsoluteBoundPair) -> Result<Self, Self::Error> {
        value
            .bound()
            .ok_or(AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteInterval`]
/// into [`AbsoluteBoundPair`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBoundPairTryFromEmptiableAbsoluteIntervalError;

impl Display for AbsoluteBoundPairTryFromEmptiableAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteInterval` into `AbsoluteBoundPair`"
        )
    }
}

impl Error for AbsoluteBoundPairTryFromEmptiableAbsoluteIntervalError {}

impl TryFrom<EmptiableAbsoluteInterval> for AbsoluteBoundPair {
    type Error = AbsoluteBoundPairTryFromEmptiableAbsoluteIntervalError;

    fn try_from(value: EmptiableAbsoluteInterval) -> Result<Self, Self::Error> {
        Ok(value
            .bound()
            .ok_or(AbsoluteBoundPairTryFromEmptiableAbsoluteIntervalError)?
            .abs_bound_pair())
    }
}

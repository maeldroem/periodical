//! Emptiable absolute bound pair
//!
//! Similar to [absolute bound pair](crate::intervals::absolute::bound_pair),
//! but has the extra ability of being able to represent an [empty
//! interval](crate::intervals::special::EmptyInterval).

use std::cmp::Ordering;
use std::ops::RangeBounds;
use std::time::Duration;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteStartBound, HasAbsoluteBoundPair};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Emptiable,
    Epsilon,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    Openness,
    Relativity,
};

/// Possession of possibly empty absolute bound pair
pub trait HasEmptiableAbsoluteBoundPair {
    /// Returns the [`EmptiableAbsoluteBoundPair`] of the object
    #[must_use]
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsoluteBoundPair;

    /// Returns [the absolute start bound](AbsoluteStartBound) of the object, if
    /// applicable
    #[must_use]
    fn partial_abs_start(&self) -> Option<AbsoluteStartBound>;

    /// Returns [the absolute end bound](AbsoluteEndBound) of the object, if
    /// applicable
    #[must_use]
    fn partial_abs_end(&self) -> Option<AbsoluteEndBound>;
}

/// All implementors of [`HasAbsoluteBoundPair`] implement
/// [`HasEmptiableAbsoluteBoundPair`]. This could change in the future to
/// separate emptiable from non-emptiable bound pairs.
impl<T> HasEmptiableAbsoluteBoundPair for T
where
    T: HasAbsoluteBoundPair,
{
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsoluteBoundPair {
        EmptiableAbsoluteBoundPair::Bound(self.abs_bound_pair())
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        Some(self.abs_start())
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        Some(self.abs_end())
    }
}

/// Enum containing [`AbsoluteBoundPair`] but with support for
/// [empty intervals](crate::intervals::special::EmptyInterval)
///
/// For more information, check [`AbsoluteBoundPair`],
/// [`EmptyInterval`](crate::intervals::special::EmptyInterval),
/// or [`crate::intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableAbsoluteBoundPair {
    Bound(AbsoluteBoundPair),
    Empty,
}

impl EmptiableAbsoluteBoundPair {
    /// Creates an [`EmptiableAbsoluteBoundPair`] from a [`Timestamp`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let emptiable_bounds = EmptiableAbsoluteBoundPair::from_range(start..end);
    ///
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bounds| bounds.start()),
    ///     Some(AbsoluteFiniteBound::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bounds| bounds.end()),
    ///     Some(AbsoluteFiniteBound::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        AbsoluteBoundPair::from_range(range).to_emptiable()
    }

    /// Returns the content of the [`Bound`](EmptiableAbsoluteBoundPair::Bound)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Bound`](EmptiableAbsoluteBoundPair::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method
    /// returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBoundPair, AbsoluteEndBound, AbsoluteStartBound, EmptiableAbsoluteBoundPair,
    /// # };
    /// let bounds = AbsoluteBoundPair::new(
    ///     AbsoluteStartBound::InfinitePast,
    ///     AbsoluteEndBound::InfiniteFuture,
    /// );
    /// // Cloning is only for making the use of `bounds` okay in the following assertions
    /// let bound_emptiable_bounds = EmptiableAbsoluteBoundPair::Bound(bounds.clone());
    /// let empty_emptiable_bounds = EmptiableAbsoluteBoundPair::Empty;
    ///
    /// assert_eq!(bound_emptiable_bounds.bound(), Some(bounds));
    /// assert_eq!(empty_emptiable_bounds.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<AbsoluteBoundPair> {
        match self {
            EmptiableAbsoluteBoundPair::Empty => None,
            EmptiableAbsoluteBoundPair::Bound(bound) => Some(bound),
        }
    }

    /// Compares two [`EmptiableAbsoluteBoundPair`], but if they have the same
    /// start, order by decreasing length
    ///
    /// Uses [`AbsoluteBoundPair::ord_by_start_and_inv_length`] under the hood
    /// for the [`Bound`](EmptiableAbsoluteBoundPair::Bound) variants and
    /// [`EmptiableAbsoluteBoundPair::cmp`]
    /// for the [`Empty`](EmptiableAbsoluteBoundPair::Empty) variants (which
    /// will just place all empty bounds before any bound bounds).
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::EmptiableAbsoluteBoundPair;
    /// # let mut bounds: [EmptiableAbsoluteBoundPair; 0] = [];
    /// bounds.sort_by(EmptiableAbsoluteBoundPair::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match (self, other) {
            (
                EmptiableAbsoluteBoundPair::Bound(og_abs_bound_pair),
                EmptiableAbsoluteBoundPair::Bound(other_abs_bound_pair),
            ) => og_abs_bound_pair.ord_by_start_and_inv_length(other_abs_bound_pair),
            _ => self.cmp(other),
        }
    }
}

impl Interval for EmptiableAbsoluteBoundPair {}

impl HasEmptiableAbsoluteBoundPair for EmptiableAbsoluteBoundPair {
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsoluteBoundPair {
        self.clone()
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(bounds.start()),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(bounds.end()),
        }
    }
}

impl Emptiable for EmptiableAbsoluteBoundPair {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableAbsoluteBoundPair {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(Duration::ZERO, Epsilon::None),
        }
    }
}

impl HasOpenness for EmptiableAbsoluteBoundPair {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableAbsoluteBoundPair {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl PartialOrd for EmptiableAbsoluteBoundPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableAbsoluteBoundPair {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableAbsoluteBoundPair::Empty, EmptiableAbsoluteBoundPair::Empty) => Ordering::Equal,
            (EmptiableAbsoluteBoundPair::Empty, EmptiableAbsoluteBoundPair::Bound(_)) => Ordering::Less,
            (EmptiableAbsoluteBoundPair::Bound(_), EmptiableAbsoluteBoundPair::Empty) => Ordering::Greater,
            (
                EmptiableAbsoluteBoundPair::Bound(og_abs_bound_pair),
                EmptiableAbsoluteBoundPair::Bound(other_abs_bound_pair),
            ) => og_abs_bound_pair.cmp(other_abs_bound_pair),
        }
    }
}

/// Converts `(bool, AbsoluteStartBound, AbsoluteEndBound)` into [`EmptiableAbsoluteBoundPair`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an empty interval.
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, AbsoluteStartBound, AbsoluteEndBound)> for EmptiableAbsoluteBoundPair {
    fn from((is_empty, start, end): (bool, AbsoluteStartBound, AbsoluteEndBound)) -> Self {
        if is_empty {
            return Self::Empty;
        }

        Self::from(AbsoluteBoundPair::new(start, end))
    }
}

/// Converts `(bool, Option<Timestamp>, Option<Timestamp>)` into
/// [`EmptiableAbsoluteBoundPair`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an empty interval.
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, Option<Timestamp>, Option<Timestamp>)> for EmptiableAbsoluteBoundPair {
    fn from((is_empty, start_opt, end_opt): (bool, Option<Timestamp>, Option<Timestamp>)) -> Self {
        let start = AbsoluteStartBound::from(start_opt);
        let end = AbsoluteEndBound::from(end_opt);
        Self::from((is_empty, start, end))
    }
}

/// Converts `(bool, Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp, BoundInclusivity)>)`
/// into [`EmptiableAbsoluteBoundPair`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an empty interval.
/// If it is set to `true`, the next elements are ignored altogether.
impl
    From<(
        bool,
        Option<(Timestamp, BoundInclusivity)>,
        Option<(Timestamp, BoundInclusivity)>,
    )> for EmptiableAbsoluteBoundPair
{
    fn from(
        (is_empty, start_opt, end_opt): (
            bool,
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        ),
    ) -> Self {
        let start = AbsoluteStartBound::from(start_opt);
        let end = AbsoluteEndBound::from(end_opt);
        Self::from((is_empty, start, end))
    }
}

impl From<AbsoluteBoundPair> for EmptiableAbsoluteBoundPair {
    fn from(value: AbsoluteBoundPair) -> Self {
        EmptiableAbsoluteBoundPair::Bound(value)
    }
}

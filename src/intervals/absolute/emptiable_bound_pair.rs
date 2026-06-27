//! Emptiable absolute bound pair
//!
//! Similar to [absolute bound pair](crate::intervals::absolute::bound_pair),
//! but has the extra ability of being able to represent an [empty interval](EmptyInterval).

use std::cmp::Ordering;
use std::ops::RangeBounds;
use std::time::Duration;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasIntervalTypeWithRel,
    HasOpenness,
    HasRelativity,
    Interval,
    IntervalTypeWithRel,
    IsEmpty,
    Openness,
    Relativity,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Possession of a possibly empty absolute bound pair
pub trait HasEmptiableAbsBoundPair {
    /// Returns the emptiable absolute bound pair
    #[must_use]
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsBoundPair;

    /// Returns [the absolute start bound](AbsStartBound), if applicable
    #[must_use]
    fn partial_abs_start(&self) -> Option<AbsStartBound>;

    /// Returns [the absolute end bound](AbsEndBound), if applicable
    #[must_use]
    fn partial_abs_end(&self) -> Option<AbsEndBound>;
}

/// All implementors of [`HasAbsBoundPair`] implement
/// [`HasEmptiableAbsBoundPair`]. This could change in the future to
/// separate emptiable from non-emptiable bound pairs.
impl<T> HasEmptiableAbsBoundPair for T
where
    T: HasAbsBoundPair,
{
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsBoundPair {
        EmptiableAbsBoundPair::Bound(self.abs_bound_pair())
    }

    fn partial_abs_start(&self) -> Option<AbsStartBound> {
        Some(self.abs_start())
    }

    fn partial_abs_end(&self) -> Option<AbsEndBound> {
        Some(self.abs_end())
    }
}

/// Emptiable [`AbsBoundPair`]
///
/// Similar to [`AbsBoundPair`], but with support for [empty intervals](EmptyInterval)
///
/// For more information, check [`AbsBoundPair`],
/// [`EmptyInterval`], or [`intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableAbsBoundPair {
    Bound(AbsBoundPair),
    Empty,
}

impl EmptiableAbsBoundPair {
    /// Creates an [`EmptiableAbsBoundPair`] from a [`Timestamp`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let emptiable_bounds = EmptiableAbsBoundPair::from_range(start..end);
    ///
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bound_pair| bound_pair.start()),
    ///     Some(AbsFiniteBoundPos::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bound_pair| bound_pair.end()),
    ///     Some(AbsFiniteBoundPos::new_with_incl(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        AbsBoundPair::from_range(range).to_emptiable()
    }

    /// Compares two [`EmptiableAbsBoundPair`], if they have the same start, order by decreasing length
    ///
    /// Uses [`AbsBoundPair::ord_by_start_and_inv_length`] under the hood
    /// for the [`Bound`](EmptiableAbsBoundPair::Bound) variant and
    /// [`EmptiableAbsBoundPair::cmp`] for the [`Empty`](EmptiableAbsBoundPair::Empty) variant
    /// (which will just place all empty bounds before any bound bound pairs).
    ///
    /// Don't rely on this method for checking equality of starts, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::EmptiableAbsBoundPair;
    /// # let mut bounds: [EmptiableAbsBoundPair; 0] = [];
    /// bounds.sort_by(EmptiableAbsBoundPair::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        if let EmptiableAbsBoundPair::Bound(lhs_abs_bound_pair) = self
            && let EmptiableAbsBoundPair::Bound(rhs_abs_bound_pair) = other
        {
            lhs_abs_bound_pair.ord_by_start_and_inv_length(rhs_abs_bound_pair)
        } else {
            self.cmp(other)
        }
    }

    /// Returns the content of the [`Bound`](EmptiableAbsBoundPair::Bound)
    /// variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableAbsBoundPair::Bound) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::{
    /// #     AbsBoundPair, AbsEndBound, AbsStartBound, EmptiableAbsBoundPair,
    /// # };
    /// let bound_pair = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
    /// let bound_emptiable_bound_pair = EmptiableAbsBoundPair::Bound(bound_pair.clone());
    /// let empty_emptiable_bound_pair = EmptiableAbsBoundPair::Empty;
    ///
    /// assert_eq!(bound_emptiable_bound_pair.bound(), Some(bound_pair));
    /// assert_eq!(empty_emptiable_bound_pair.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<AbsBoundPair> {
        match self {
            EmptiableAbsBoundPair::Bound(bound) => Some(bound),
            EmptiableAbsBoundPair::Empty => None,
        }
    }

    /// Converts `self` into [`EmptiableAbsInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableAbsInterval {
        EmptiableAbsInterval::from(self)
    }
}

impl Interval for EmptiableAbsBoundPair {}

impl HasEmptiableAbsBoundPair for EmptiableAbsBoundPair {
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsBoundPair {
        self.clone()
    }

    fn partial_abs_start(&self) -> Option<AbsStartBound> {
        match self {
            Self::Bound(bounds) => Some(bounds.start()),
            Self::Empty => None,
        }
    }

    fn partial_abs_end(&self) -> Option<AbsEndBound> {
        match self {
            Self::Bound(bounds) => Some(bounds.end()),
            Self::Empty => None,
        }
    }
}

impl IsEmpty for EmptiableAbsBoundPair {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableAbsBoundPair {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(Duration::ZERO, Epsilon::None),
        }
    }
}

impl HasOpenness for EmptiableAbsBoundPair {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableAbsBoundPair {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bound(bound) => bound.relativity(),
            Self::Empty => Relativity::Any,
        }
    }
}

impl HasIntervalTypeWithRel for EmptiableAbsBoundPair {
    fn interval_type_with_rel(&self) -> IntervalTypeWithRel {
        match self {
            Self::Empty => IntervalTypeWithRel::Empty,
            Self::Bound(bound_pair) => bound_pair.interval_type_with_rel(),
        }
    }
}

impl PartialOrd for EmptiableAbsBoundPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableAbsBoundPair {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Empty) => Ordering::Equal,
            (EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Bound(_)) => Ordering::Less,
            (EmptiableAbsBoundPair::Bound(_), EmptiableAbsBoundPair::Empty) => Ordering::Greater,
            (EmptiableAbsBoundPair::Bound(og_abs_bound_pair), EmptiableAbsBoundPair::Bound(other_abs_bound_pair)) => {
                og_abs_bound_pair.cmp(other_abs_bound_pair)
            },
        }
    }
}

/// Converts `Option<(AbsStartBound, AbsEndBound)>` into [`EmptiableAbsBoundPair`]
///
/// The option represents whether the interval is an empty interval.
impl From<Option<(AbsStartBound, AbsEndBound)>> for EmptiableAbsBoundPair {
    fn from(opt_start_end: Option<(AbsStartBound, AbsEndBound)>) -> Self {
        if let Some((start, end)) = opt_start_end {
            Self::from(AbsBoundPair::new(start, end))
        } else {
            Self::Empty
        }
    }
}

/// Converts `Option<(Option<Timestamp>, Option<Timestamp>)>` into [`EmptiableAbsBoundPair`]
///
/// The option represents whether the interval is an empty interval.
impl From<Option<(Option<Timestamp>, Option<Timestamp>)>> for EmptiableAbsBoundPair {
    fn from(opt_start_opt_end_opt: Option<(Option<Timestamp>, Option<Timestamp>)>) -> Self {
        if let Some((start_opt, end_opt)) = opt_start_opt_end_opt {
            Self::from(AbsBoundPair::new(
                AbsStartBound::from(start_opt),
                AbsEndBound::from(end_opt),
            ))
        } else {
            Self::Empty
        }
    }
}

/// Converts `Option<(Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp, BoundInclusivity)>)>`
/// into [`EmptiableAbsBoundPair`]
///
/// The option represents whether the interval is an empty interval.
impl
    From<
        Option<(
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        )>,
    > for EmptiableAbsBoundPair
{
    fn from(
        opt_start_incl_opt_end_incl_opt: Option<(
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        )>,
    ) -> Self {
        if let Some((start_incl_opt, end_incl_opt)) = opt_start_incl_opt_end_incl_opt {
            Self::from(AbsBoundPair::new(
                AbsStartBound::from(start_incl_opt),
                AbsEndBound::from(end_incl_opt),
            ))
        } else {
            Self::Empty
        }
    }
}

impl From<AbsBoundPair> for EmptiableAbsBoundPair {
    fn from(value: AbsBoundPair) -> Self {
        EmptiableAbsBoundPair::Bound(value)
    }
}

impl From<BoundedAbsInterval> for EmptiableAbsBoundPair {
    fn from(value: BoundedAbsInterval) -> Self {
        value.emptiable_abs_bound_pair()
    }
}

impl From<HalfBoundedAbsInterval> for EmptiableAbsBoundPair {
    fn from(value: HalfBoundedAbsInterval) -> Self {
        value.emptiable_abs_bound_pair()
    }
}

impl From<AbsInterval> for EmptiableAbsBoundPair {
    fn from(value: AbsInterval) -> Self {
        value.emptiable_abs_bound_pair()
    }
}

impl From<EmptiableAbsInterval> for EmptiableAbsBoundPair {
    fn from(value: EmptiableAbsInterval) -> Self {
        value.emptiable_abs_bound_pair()
    }
}

impl From<UnboundedInterval> for EmptiableAbsBoundPair {
    fn from(value: UnboundedInterval) -> Self {
        value.emptiable_abs_bound_pair()
    }
}

impl From<EmptyInterval> for EmptiableAbsBoundPair {
    fn from(value: EmptyInterval) -> Self {
        value.emptiable_abs_bound_pair()
    }
}

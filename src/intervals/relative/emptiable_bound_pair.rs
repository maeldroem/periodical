//! Emptiable absolute bound pair
//!
//! Similar to [absolute bound pair](crate::intervals::absolute::bound_pair),
//! but has the extra ability of being able to represent an [empty interval](EmptyInterval).

use std::cmp::Ordering;
use std::ops::RangeBounds;
use std::time::Duration;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    IsEmpty,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Possession of a possibly empty relative bound pair
pub trait HasEmptiableRelBoundPair {
    /// Returns the emptiable relative bound pair
    #[must_use]
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelBoundPair;

    /// Returns [the relative start bound](RelStartBound), if applicable
    #[must_use]
    fn partial_rel_start(&self) -> Option<RelStartBound>;

    /// Returns [the relative end bound](RelEndBound), if applicable
    #[must_use]
    fn partial_rel_end(&self) -> Option<RelEndBound>;
}

/// All implementors of [`HasRelBoundPair`] implement
/// [`HasEmptiableRelBoundPair`]. This could change in the future to
/// separate emptiable from non-emptiable bounds.
impl<T> HasEmptiableRelBoundPair for T
where
    T: HasRelBoundPair,
{
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelBoundPair {
        EmptiableRelBoundPair::Bound(self.rel_bound_pair())
    }

    fn partial_rel_start(&self) -> Option<RelStartBound> {
        Some(self.rel_start())
    }

    fn partial_rel_end(&self) -> Option<RelEndBound> {
        Some(self.rel_end())
    }
}

/// Emptiable [`RelBoundPair`]
///
/// Similar to [`RelBoundPair`], but with support for [empty intervals](EmptyInterval)
///
/// For more information, check [`RelBoundPair`],
/// [`EmptyInterval`], or [`intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableRelBoundPair {
    Bound(RelBoundPair),
    Empty,
}

impl EmptiableRelBoundPair {
    /// Creates an [`EmptiableRelBoundPair`] from a [`SignedDuration`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos, EmptiableRelBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = SignedDuration::from_hours(8);
    /// let end = SignedDuration::from_hours(16);
    ///
    /// let emptiable_bounds = EmptiableRelBoundPair::from_range(start..end);
    ///
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bound_pair| bound_pair.start()),
    ///     Some(RelFiniteBoundPos::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bound_pair| bound_pair.end()),
    ///     Some(RelFiniteBoundPos::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        RelBoundPair::from_range(range).to_emptiable()
    }

    /// Compares two [`EmptiableRelBoundPair`], if they have the same start, order by decreasing length
    ///
    /// Uses [`RelBoundPair::ord_by_start_and_inv_length`] under the hood
    /// for the [`Bound`](EmptiableRelBoundPair::Bound) variant and
    /// [`EmptiableRelBoundPair::cmp`] for the [`Empty`](EmptiableRelBoundPair::Empty) variant
    /// (which will just place all empty bounds before any bound bound pairs).
    ///
    /// Don't rely on this method for checking equality of starts, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::EmptiableRelBoundPair;
    /// # let mut bounds: [EmptiableRelBoundPair; 0] = [];
    /// bounds.sort_by(EmptiableRelBoundPair::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        if let EmptiableRelBoundPair::Bound(lhs_rel_bound_pair) = self
            && let EmptiableRelBoundPair::Bound(rhs_rel_bound_pair) = other
        {
            lhs_rel_bound_pair.ord_by_start_and_inv_length(rhs_rel_bound_pair)
        } else {
            self.cmp(other)
        }
    }

    /// Returns the content of the [`Bound`](EmptiableRelBoundPair::Bound)
    /// variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableRelBoundPair::Bound) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::{
    /// #     EmptiableRelBoundPair, RelBoundPair, RelEndBound, RelStartBound,
    /// # };
    /// let bound_pair = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);
    /// let bound_emptiable_bound_pair = EmptiableRelBoundPair::Bound(bound_pair.clone());
    /// let empty_emptiable_bound_pair = EmptiableRelBoundPair::Empty;
    ///
    /// assert_eq!(bound_emptiable_bound_pair.bound(), Some(bound_pair));
    /// assert_eq!(empty_emptiable_bound_pair.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<RelBoundPair> {
        match self {
            EmptiableRelBoundPair::Bound(bound) => Some(bound),
            EmptiableRelBoundPair::Empty => None,
        }
    }

    /// Converts `self` into [`EmptiableRelInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableRelInterval {
        EmptiableRelInterval::from(self)
    }
}

impl Interval for EmptiableRelBoundPair {}

impl HasEmptiableRelBoundPair for EmptiableRelBoundPair {
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelBoundPair {
        self.clone()
    }

    fn partial_rel_start(&self) -> Option<RelStartBound> {
        match self {
            Self::Bound(bounds) => Some(bounds.start()),
            Self::Empty => None,
        }
    }

    fn partial_rel_end(&self) -> Option<RelEndBound> {
        match self {
            Self::Bound(bounds) => Some(bounds.end()),
            Self::Empty => None,
        }
    }
}

impl IsEmpty for EmptiableRelBoundPair {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableRelBoundPair {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(Duration::ZERO, Epsilon::None),
        }
    }
}

impl HasOpenness for EmptiableRelBoundPair {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableRelBoundPair {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bound(bound) => bound.relativity(),
            Self::Empty => Relativity::Any,
        }
    }
}

impl PartialOrd for EmptiableRelBoundPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableRelBoundPair {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Empty) => Ordering::Equal,
            (EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Bound(_)) => Ordering::Less,
            (EmptiableRelBoundPair::Bound(_), EmptiableRelBoundPair::Empty) => Ordering::Greater,
            (EmptiableRelBoundPair::Bound(og_rel_bound_pair), EmptiableRelBoundPair::Bound(other_rel_bound_pair)) => {
                og_rel_bound_pair.cmp(other_rel_bound_pair)
            },
        }
    }
}

/// Converts `Option<(RelStartBound, RelEndBound)>` into [`EmptiableRelBoundPair`]
///
/// The option represents whether the interval is an empty interval.
impl From<Option<(RelStartBound, RelEndBound)>> for EmptiableRelBoundPair {
    fn from(opt_start_end: Option<(RelStartBound, RelEndBound)>) -> Self {
        if let Some((start, end)) = opt_start_end {
            Self::from(RelBoundPair::new(start, end))
        } else {
            Self::Empty
        }
    }
}

/// Converts `Option<(Option<SignedDuration>, Option<SignedDuration>)>` into [`EmptiableRelBoundPair`]
///
/// The option represents whether the interval is an empty interval.
impl From<Option<(Option<SignedDuration>, Option<SignedDuration>)>> for EmptiableRelBoundPair {
    fn from(opt_start_opt_end_opt: Option<(Option<SignedDuration>, Option<SignedDuration>)>) -> Self {
        if let Some((start_opt, end_opt)) = opt_start_opt_end_opt {
            Self::from(RelBoundPair::new(
                RelStartBound::from(start_opt),
                RelEndBound::from(end_opt),
            ))
        } else {
            Self::Empty
        }
    }
}

/// Converts `Option<(Option<(SignedDuration, BoundInclusivity)>, Option<(SignedDuration, BoundInclusivity)>)>`
/// into [`EmptiableRelBoundPair`]
///
/// The option represents whether the interval is an empty interval.
impl
    From<
        Option<(
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        )>,
    > for EmptiableRelBoundPair
{
    fn from(
        opt_start_incl_opt_end_incl_opt: Option<(
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        )>,
    ) -> Self {
        if let Some((start_incl_opt, end_incl_opt)) = opt_start_incl_opt_end_incl_opt {
            Self::from(RelBoundPair::new(
                RelStartBound::from(start_incl_opt),
                RelEndBound::from(end_incl_opt),
            ))
        } else {
            Self::Empty
        }
    }
}

impl From<RelBoundPair> for EmptiableRelBoundPair {
    fn from(value: RelBoundPair) -> Self {
        EmptiableRelBoundPair::Bound(value)
    }
}

impl From<BoundedRelInterval> for EmptiableRelBoundPair {
    fn from(value: BoundedRelInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<HalfBoundedRelInterval> for EmptiableRelBoundPair {
    fn from(value: HalfBoundedRelInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<RelInterval> for EmptiableRelBoundPair {
    fn from(value: RelInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<EmptiableRelInterval> for EmptiableRelBoundPair {
    fn from(value: EmptiableRelInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<UnboundedInterval> for EmptiableRelBoundPair {
    fn from(value: UnboundedInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<EmptyInterval> for EmptiableRelBoundPair {
    fn from(value: EmptyInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

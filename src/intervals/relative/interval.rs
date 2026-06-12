//! Relative interval
//!
//! Represents any form of specific relative intervals,
//! besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
//! That includes [`BoundedRelInterval`], [`HalfBoundedRelInterval`],
//! and [`UnboundedInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`RelBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is used for dealing with relative intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`RelBoundPair`].
//!
//! If you want to include
//! [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
//! variant, see [`EmptiableRelInterval`].

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::RangeBounds;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{
    Duration as IntervalDuration,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HalfBoundedToFutureRelInterval,
    HalfBoundedToPastRelInterval,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelStartBound,
};
use crate::intervals::special::UnboundedInterval;

/// Relative interval
///
/// Represents any form of specific relative intervals,
/// besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
/// That includes [`BoundedRelInterval`], [`HalfBoundedRelInterval`],
/// and [`UnboundedInterval`].
///
/// The contained intervals conserve the [openness](Openness) invariant, but the
/// chosen variant can change. Compared to [`RelBoundPair`], thanks to the
/// variants we know exactly the kind of interval that is stored without needing
/// to check inner data.
///
/// Usually this structure is used for dealing with relative intervals as a single
/// type in a way that conserves the [openness](Openness) invariant, contrary to
/// [`RelBoundPair`].
///
/// If you want to include
/// [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
/// variant, see [`EmptiableRelInterval`].
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RelInterval {
    Bounded(BoundedRelInterval),
    HalfBounded(HalfBoundedRelInterval),
    Unbounded(UnboundedInterval),
}

impl RelInterval {
    /// Creates an [`RelInterval`] from a [`SignedDuration`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, RelInterval, HasRelBoundPair};
    /// let start = SignedDuration::from_hours(8);
    /// let end = SignedDuration::from_hours(16);
    ///
    /// let interval = RelInterval::from_range(start..end);
    ///
    /// assert_eq!(
    ///     interval.rel_start(),
    ///     RelFiniteBoundPos::new(start).to_start_bound(),
    /// );
    /// assert_eq!(
    ///     interval.rel_end(),
    ///     RelFiniteBoundPos::new_with_incl(end, BoundInclusivity::Exclusive).to_end_bound(),
    /// );
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        Self::from(RelBoundPair::from_range(range))
    }

    /// Compares two [`RelInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of starts, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelInterval;
    /// # let mut bounds: [RelInterval; 0] = [];
    /// bounds.sort_by(RelInterval::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.rel_bound_pair()
            .ord_by_start_and_inv_length(&other.rel_bound_pair())
    }

    /// Returns the content of the [`Bounded`](RelInterval::Bounded) variant
    ///
    /// Consumes `self` and puts the content of the [`Bounded`](RelInterval::Bounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::BoundedRelInterval;
    /// let bounded_interval = BoundedRelInterval::from_offsets(
    ///     SignedDuration::from_hours(8),
    ///     SignedDuration::from_hours(16),
    /// );
    ///
    /// let interval = bounded_interval.clone().to_interval();
    ///
    /// assert_eq!(interval.bounded(), Some(bounded_interval));
    /// ```
    #[must_use]
    pub fn bounded(self) -> Option<BoundedRelInterval> {
        match self {
            Self::Bounded(interval) => Some(interval),
            _ => None,
        }
    }

    /// Returns the content of the [`HalfBounded`](RelInterval::HalfBounded) variant
    ///
    /// Consumes `self` and puts the content of the [`HalfBounded`](RelInterval::HalfBounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::HalfBoundedRelInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let half_bounded_interval = HalfBoundedRelInterval::from_offset(
    ///     SignedDuration::from_hours(8),
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// let interval = half_bounded_interval.clone().to_interval();
    ///
    /// assert_eq!(interval.half_bounded(), Some(half_bounded_interval));
    /// ```
    #[must_use]
    pub fn half_bounded(self) -> Option<HalfBoundedRelInterval> {
        match self {
            Self::HalfBounded(interval) => Some(interval),
            _ => None,
        }
    }

    /// Returns the content of the [`Unbounded`](RelInterval::Unbounded) variant
    ///
    /// Consumes `self` and puts the content of the [`Unbounded`](RelInterval::Unbounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelInterval;
    /// # use periodical::intervals::special::UnboundedInterval;
    /// let interval = RelInterval::Unbounded(UnboundedInterval);
    ///
    /// assert_eq!(interval.unbounded(), Some(UnboundedInterval));
    /// ```
    #[must_use]
    pub fn unbounded(self) -> Option<UnboundedInterval> {
        match self {
            Self::Unbounded(interval) => Some(interval),
            _ => None,
        }
    }

    /// Wraps `self` in [`EmptiableRelInterval`]
    #[must_use]
    pub fn to_emptiable(self) -> EmptiableRelInterval {
        EmptiableRelInterval::from(self)
    }
}

impl Interval for RelInterval {}

impl HasRelBoundPair for RelInterval {
    fn rel_bound_pair(&self) -> RelBoundPair {
        match self {
            Self::Bounded(bounded) => bounded.rel_bound_pair(),
            Self::HalfBounded(half_bounded) => half_bounded.rel_bound_pair(),
            Self::Unbounded(unbounded) => unbounded.rel_bound_pair(),
        }
    }

    fn rel_start(&self) -> RelStartBound {
        match self {
            Self::Bounded(bounded) => bounded.rel_start(),
            Self::HalfBounded(half_bounded) => half_bounded.rel_start(),
            Self::Unbounded(unbounded) => unbounded.rel_start(),
        }
    }

    fn rel_end(&self) -> RelEndBound {
        match self {
            Self::Bounded(bounded) => bounded.rel_end(),
            Self::HalfBounded(half_bounded) => half_bounded.rel_end(),
            Self::Unbounded(unbounded) => unbounded.rel_end(),
        }
    }
}

impl HasDuration for RelInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for RelInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for RelInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
        }
    }
}

impl PartialOrd for RelInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rel_bound_pair().cmp(&other.rel_bound_pair())
    }
}

impl IsEmpty for RelInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<BoundedRelInterval> for RelInterval {
    fn from(value: BoundedRelInterval) -> Self {
        RelInterval::Bounded(value)
    }
}

impl From<HalfBoundedToFutureRelInterval> for RelInterval {
    fn from(value: HalfBoundedToFutureRelInterval) -> Self {
        Self::from(HalfBoundedRelInterval::from(value))
    }
}

impl From<HalfBoundedToPastRelInterval> for RelInterval {
    fn from(value: HalfBoundedToPastRelInterval) -> Self {
        Self::from(HalfBoundedRelInterval::from(value))
    }
}

impl From<HalfBoundedRelInterval> for RelInterval {
    fn from(value: HalfBoundedRelInterval) -> Self {
        RelInterval::HalfBounded(value)
    }
}

impl From<UnboundedInterval> for RelInterval {
    fn from(value: UnboundedInterval) -> Self {
        RelInterval::Unbounded(value)
    }
}

impl From<RelBoundPair> for RelInterval {
    fn from(value: RelBoundPair) -> Self {
        type StartB = RelStartBound;
        type EndB = RelEndBound;

        match (value.start(), value.end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => RelInterval::Unbounded(UnboundedInterval),
            (StartB::InfinitePast, EndB::Finite(finite_end)) => {
                RelInterval::HalfBounded(HalfBoundedRelInterval::new(finite_end.pos(), OpeningDirection::ToPast))
            },
            (StartB::Finite(finite_start), EndB::InfiniteFuture) => RelInterval::HalfBounded(
                HalfBoundedRelInterval::new(finite_start.pos(), OpeningDirection::ToFuture),
            ),
            (StartB::Finite(finite_start), EndB::Finite(finite_end)) => {
                RelInterval::Bounded(BoundedRelInterval::unchecked_new(finite_start, finite_end))
            },
        }
    }
}

/// Error that can occur when converting an [`EmptiableRelBoundPair`] to [`RelInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelIntervalTryFromEmptiableRelBoundPairError;

impl Display for RelIntervalTryFromEmptiableRelBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Failed to convert the emptiable relative bound pair into an relative interval"
        )
    }
}

impl Error for RelIntervalTryFromEmptiableRelBoundPairError {}

impl TryFrom<EmptiableRelBoundPair> for RelInterval {
    type Error = RelIntervalTryFromEmptiableRelBoundPairError;

    fn try_from(value: EmptiableRelBoundPair) -> Result<Self, Self::Error> {
        Ok(Self::from(
            value.bound().ok_or(RelIntervalTryFromEmptiableRelBoundPairError)?,
        ))
    }
}

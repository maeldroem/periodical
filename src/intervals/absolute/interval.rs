//! Absolute interval
//!
//! Represents any form of specific absolute intervals,
//! besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
//! That includes [`BoundedAbsInterval`], [`HalfBoundedAbsInterval`],
//! and [`UnboundedInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`AbsBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is used for dealing with absolute intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`AbsBoundPair`].
//!
//! If you want to include
//! [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
//! variant, see [`EmptiableAbsInterval`].

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::RangeBounds;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasAbsBoundPair,
};
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
use crate::intervals::special::UnboundedInterval;

/// Absolute interval
///
/// Represents any form of specific absolute intervals,
/// besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
/// That includes [`BoundedAbsInterval`], [`HalfBoundedAbsInterval`],
/// and [`UnboundedInterval`].
///
/// The contained intervals conserve the [openness](Openness) invariant, but the
/// chosen variant can change. Compared to [`AbsBoundPair`], thanks to the
/// variants we know exactly the kind of interval that is stored without needing
/// to check inner data.
///
/// Usually this structure is used for dealing with absolute intervals as a single
/// type in a way that conserves the [openness](Openness) invariant, contrary to
/// [`AbsBoundPair`].
///
/// If you want to include
/// [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
/// variant, see [`EmptiableAbsInterval`].
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbsInterval {
    Bounded(BoundedAbsInterval),
    HalfBounded(HalfBoundedAbsInterval),
    Unbounded(UnboundedInterval),
}

impl AbsInterval {
    /// Creates an [`AbsInterval`] from a [`Timestamp`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsInterval, HasAbsBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let interval = AbsInterval::from_range(start..end);
    ///
    /// assert_eq!(
    ///     interval.abs_start(),
    ///     AbsFiniteBoundPos::new(start).to_start_bound(),
    /// );
    /// assert_eq!(
    ///     interval.abs_end(),
    ///     AbsFiniteBoundPos::new_with_incl(end, BoundInclusivity::Exclusive).to_end_bound(),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        Self::from(AbsBoundPair::from_range(range))
    }

    /// Compares two [`AbsInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of starts, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsInterval;
    /// # let mut bounds: [AbsInterval; 0] = [];
    /// bounds.sort_by(AbsInterval::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.abs_bound_pair()
            .ord_by_start_and_inv_length(&other.abs_bound_pair())
    }

    /// Returns the content of the [`Bounded`](AbsInterval::Bounded) variant
    ///
    /// Consumes `self` and puts the content of the [`Bounded`](AbsInterval::Bounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let bounded_interval = BoundedAbsInterval::from_times(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// let interval = bounded_interval.clone().to_interval();
    ///
    /// assert_eq!(interval.bounded(), Some(bounded_interval));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn bounded(self) -> Option<BoundedAbsInterval> {
        match self {
            Self::Bounded(interval) => Some(interval),
            _ => None,
        }
    }

    /// Returns the content of the [`HalfBounded`](AbsInterval::HalfBounded) variant
    ///
    /// Consumes `self` and puts the content of the [`HalfBounded`](AbsInterval::HalfBounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::HalfBoundedAbsInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let half_bounded_interval = HalfBoundedAbsInterval::from_time(
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// let interval = half_bounded_interval.clone().to_interval();
    ///
    /// assert_eq!(interval.half_bounded(), Some(half_bounded_interval));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn half_bounded(self) -> Option<HalfBoundedAbsInterval> {
        match self {
            Self::HalfBounded(interval) => Some(interval),
            _ => None,
        }
    }

    /// Returns the content of the [`Unbounded`](AbsInterval::Unbounded) variant
    ///
    /// Consumes `self` and puts the content of the [`Unbounded`](AbsInterval::Unbounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsInterval;
    /// # use periodical::intervals::special::UnboundedInterval;
    /// let interval = AbsInterval::Unbounded(UnboundedInterval);
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

    /// Wraps `self` in [`EmptiableAbsInterval`]
    #[must_use]
    pub fn to_emptiable(self) -> EmptiableAbsInterval {
        EmptiableAbsInterval::from(self)
    }
}

impl Interval for AbsInterval {}

impl HasAbsBoundPair for AbsInterval {
    fn abs_bound_pair(&self) -> AbsBoundPair {
        match self {
            Self::Bounded(bounded) => bounded.abs_bound_pair(),
            Self::HalfBounded(half_bounded) => half_bounded.abs_bound_pair(),
            Self::Unbounded(unbounded) => unbounded.abs_bound_pair(),
        }
    }

    fn abs_start(&self) -> AbsStartBound {
        match self {
            Self::Bounded(bounded) => bounded.abs_start(),
            Self::HalfBounded(half_bounded) => half_bounded.abs_start(),
            Self::Unbounded(unbounded) => unbounded.abs_start(),
        }
    }

    fn abs_end(&self) -> AbsEndBound {
        match self {
            Self::Bounded(bounded) => bounded.abs_end(),
            Self::HalfBounded(half_bounded) => half_bounded.abs_end(),
            Self::Unbounded(unbounded) => unbounded.abs_end(),
        }
    }
}

impl HasDuration for AbsInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for AbsInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for AbsInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
        }
    }
}

impl PartialOrd for AbsInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.abs_bound_pair().cmp(&other.abs_bound_pair())
    }
}

impl IsEmpty for AbsInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<BoundedAbsInterval> for AbsInterval {
    fn from(value: BoundedAbsInterval) -> Self {
        Self::Bounded(value)
    }
}

impl From<HalfBoundedToFutureAbsInterval> for AbsInterval {
    fn from(value: HalfBoundedToFutureAbsInterval) -> Self {
        Self::from(HalfBoundedAbsInterval::from(value))
    }
}

impl From<HalfBoundedToPastAbsInterval> for AbsInterval {
    fn from(value: HalfBoundedToPastAbsInterval) -> Self {
        Self::from(HalfBoundedAbsInterval::from(value))
    }
}

impl From<HalfBoundedAbsInterval> for AbsInterval {
    fn from(value: HalfBoundedAbsInterval) -> Self {
        Self::HalfBounded(value)
    }
}

impl From<UnboundedInterval> for AbsInterval {
    fn from(value: UnboundedInterval) -> Self {
        Self::Unbounded(value)
    }
}

impl From<AbsBoundPair> for AbsInterval {
    fn from(value: AbsBoundPair) -> Self {
        type StartB = AbsStartBound;
        type EndB = AbsEndBound;

        match (value.start(), value.end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => AbsInterval::Unbounded(UnboundedInterval),
            (StartB::InfinitePast, EndB::Finite(finite_end)) => {
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::new(finite_end.pos(), OpeningDirection::ToPast))
            },
            (StartB::Finite(finite_start), EndB::InfiniteFuture) => AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::new(finite_start.pos(), OpeningDirection::ToFuture),
            ),
            (StartB::Finite(finite_start), EndB::Finite(finite_end)) => {
                AbsInterval::Bounded(BoundedAbsInterval::unchecked_new(finite_start, finite_end))
            },
        }
    }
}

/// Error that can occur when converting an [`EmptiableAbsBoundPair`] to [`AbsInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsIntervalTryFromEmptiableAbsBoundPairError;

impl Display for AbsIntervalTryFromEmptiableAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Failed to convert the emptiable absolute bound pair into an absolute interval"
        )
    }
}

impl Error for AbsIntervalTryFromEmptiableAbsBoundPairError {}

impl TryFrom<EmptiableAbsBoundPair> for AbsInterval {
    type Error = AbsIntervalTryFromEmptiableAbsBoundPairError;

    fn try_from(value: EmptiableAbsBoundPair) -> Result<Self, Self::Error> {
        Ok(Self::from(
            value.bound().ok_or(AbsIntervalTryFromEmptiableAbsBoundPairError)?,
        ))
    }
}

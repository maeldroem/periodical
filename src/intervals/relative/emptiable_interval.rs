//! Relative emptiable interval
//!
//! Represents any form of specific relative intervals, including
//! [`EmptyInterval`]. That includes [`BoundedRelInterval`],
//! [`HalfBoundedRelInterval`], [`UnboundedInterval`],
//! and [`EmptyInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`RelBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is for dealing with relative intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`RelBoundPair`].
//!
//! If you want to exclude [`EmptyInterval`] as a possible variant, see
//! [`RelInterval`].

use std::cmp::Ordering;
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
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    HalfBoundedRelInterval,
    HalfBoundedToFutureRelInterval,
    HalfBoundedToPastRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableRelInterval {
    Bound(RelInterval),
    Empty(EmptyInterval),
}

impl EmptiableRelInterval {
    /// Creates an [`EmptiableRelInterval`] from a [`SignedDuration`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{
    /// #     RelFiniteBoundPos, RelInterval, EmptiableRelInterval, HasEmptiableRelBoundPair,
    /// # };
    /// let start = SignedDuration::from_hours(8);
    /// let end = SignedDuration::from_hours(16);
    ///
    /// let interval = EmptiableRelInterval::from_range(start..end);
    ///
    /// assert_eq!(
    ///     interval.partial_rel_start(),
    ///     Some(RelFiniteBoundPos::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     interval.partial_rel_end(),
    ///     Some(RelFiniteBoundPos::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        RelInterval::from_range(range).to_emptiable()
    }

    /// Returns the content of the [`Bound`](EmptiableRelInterval::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableRelInterval::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     EmptiableRelInterval, RelInterval, BoundedRelInterval,
    /// # };
    /// # use periodical::intervals::special::EmptyInterval;
    /// let interval = BoundedRelInterval::new(
    ///     SignedDuration::from_hours(8),
    ///     SignedDuration::from_hours(16),
    /// )
    /// .to_interval();
    ///
    /// let bound_emptiable_interval = EmptiableRelInterval::Bound(interval.clone());
    /// let empty_emptiable_interval = EmptiableRelInterval::Empty(EmptyInterval);
    ///
    /// assert_eq!(bound_emptiable_interval.bound(), Some(interval));
    /// assert_eq!(empty_emptiable_interval.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<RelInterval> {
        match self {
            Self::Bound(interval) => Some(interval),
            Self::Empty(_) => None,
        }
    }

    /// Compares two [`RelInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Uses [`EmptiableRelBoundPair::ord_by_start_and_inv_length`] under
    /// the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will
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
        self.emptiable_rel_bound_pair()
            .ord_by_start_and_inv_length(&other.emptiable_rel_bound_pair())
    }
}

impl Interval for EmptiableRelInterval {}

impl HasDuration for EmptiableRelInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(interval) => interval.duration(),
            Self::Empty(empty) => empty.duration(),
        }
    }
}

impl HasRelativity for EmptiableRelInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bound(interval) => interval.relativity(),
            Self::Empty(empty) => empty.relativity(),
        }
    }
}

impl HasOpenness for EmptiableRelInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(interval) => interval.openness(),
            Self::Empty(empty) => empty.openness(),
        }
    }
}

impl HasEmptiableRelBoundPair for EmptiableRelInterval {
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelBoundPair {
        match self {
            Self::Bound(interval) => EmptiableRelBoundPair::from(interval.rel_bound_pair()),
            Self::Empty(interval) => interval.emptiable_rel_bound_pair(),
        }
    }

    fn partial_rel_start(&self) -> Option<RelStartBound> {
        match self {
            Self::Bound(interval) => interval.partial_rel_start(),
            Self::Empty(empty) => empty.partial_rel_start(),
        }
    }

    fn partial_rel_end(&self) -> Option<RelEndBound> {
        match self {
            Self::Bound(interval) => interval.partial_rel_end(),
            Self::Empty(empty) => empty.partial_rel_end(),
        }
    }
}

impl IsEmpty for EmptiableRelInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for EmptiableRelInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableRelInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_rel_bound_pair().cmp(&other.emptiable_rel_bound_pair())
    }
}

impl From<BoundedRelInterval> for EmptiableRelInterval {
    fn from(value: BoundedRelInterval) -> Self {
        EmptiableRelInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedToFutureRelInterval> for EmptiableRelInterval {
    fn from(value: HalfBoundedToFutureRelInterval) -> Self {
        EmptiableRelInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedToPastRelInterval> for EmptiableRelInterval {
    fn from(value: HalfBoundedToPastRelInterval) -> Self {
        EmptiableRelInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedRelInterval> for EmptiableRelInterval {
    fn from(value: HalfBoundedRelInterval) -> Self {
        EmptiableRelInterval::Bound(value.to_interval())
    }
}

impl From<UnboundedInterval> for EmptiableRelInterval {
    fn from(value: UnboundedInterval) -> Self {
        EmptiableRelInterval::Bound(RelInterval::Unbounded(value))
    }
}

impl From<EmptyInterval> for EmptiableRelInterval {
    fn from(value: EmptyInterval) -> Self {
        EmptiableRelInterval::Empty(value)
    }
}

impl From<RelBoundPair> for EmptiableRelInterval {
    fn from(value: RelBoundPair) -> Self {
        EmptiableRelInterval::Bound(RelInterval::from(value))
    }
}

impl From<EmptiableRelBoundPair> for EmptiableRelInterval {
    fn from(value: EmptiableRelBoundPair) -> Self {
        match value.bound() {
            Some(rel_bound_pair) => Self::from(rel_bound_pair),
            None => Self::Empty(EmptyInterval),
        }
    }
}

impl From<RelInterval> for EmptiableRelInterval {
    fn from(value: RelInterval) -> Self {
        Self::Bound(value)
    }
}

impl From<()> for EmptiableRelInterval {
    fn from(_value: ()) -> Self {
        EmptiableRelInterval::Empty(EmptyInterval)
    }
}

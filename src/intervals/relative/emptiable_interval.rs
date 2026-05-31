//! Relative emptiable interval
//!
//! Represents any form of specific relative intervals, including
//! [`EmptyInterval`]. That includes [`BoundedRelativeInterval`],
//! [`HalfBoundedRelativeInterval`], [`UnboundedInterval`],
//! and [`EmptyInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`RelativeBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is for dealing with relative intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`RelativeBoundPair`].
//!
//! If you want to exclude [`EmptyInterval`] as a possible variant, see
//! [`RelativeInterval`].

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
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    HalfBoundedRelativeInterval,
    HalfBoundedToFutureRelativeInterval,
    HalfBoundedToPastRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableRelativeInterval {
    Bound(RelativeInterval),
    Empty(EmptyInterval),
}

impl EmptiableRelativeInterval {
    /// Creates an [`EmptiableRelativeInterval`] from a [`SignedDuration`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{
    /// #     RelativeFiniteBoundPosition, RelativeInterval, EmptiableRelativeInterval, HasEmptiableRelativeBoundPair,
    /// # };
    /// let start = SignedDuration::from_hours(8);
    /// let end = SignedDuration::from_hours(16);
    ///
    /// let interval = EmptiableRelativeInterval::from_range(start..end);
    ///
    /// assert_eq!(
    ///     interval.partial_rel_start(),
    ///     Some(RelativeFiniteBoundPosition::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     interval.partial_rel_end(),
    ///     Some(RelativeFiniteBoundPosition::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        RelativeInterval::from_range(range).to_emptiable()
    }

    /// Returns the content of the [`Bound`](EmptiableRelativeInterval::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableRelativeInterval::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     EmptiableRelativeInterval, RelativeInterval, BoundedRelativeInterval,
    /// # };
    /// # use periodical::intervals::special::EmptyInterval;
    /// let interval = BoundedRelativeInterval::new(
    ///     SignedDuration::from_hours(8),
    ///     SignedDuration::from_hours(16),
    /// )
    /// .to_interval();
    ///
    /// let bound_emptiable_interval = EmptiableRelativeInterval::Bound(interval.clone());
    /// let empty_emptiable_interval = EmptiableRelativeInterval::Empty(EmptyInterval);
    ///
    /// assert_eq!(bound_emptiable_interval.bound(), Some(interval));
    /// assert_eq!(empty_emptiable_interval.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<RelativeInterval> {
        match self {
            Self::Bound(interval) => Some(interval),
            Self::Empty(_) => None,
        }
    }

    /// Compares two [`RelativeInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Uses [`EmptiableRelativeBoundPair::ord_by_start_and_inv_length`] under
    /// the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelativeInterval;
    /// # let mut bounds: [RelativeInterval; 0] = [];
    /// bounds.sort_by(RelativeInterval::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.emptiable_rel_bound_pair()
            .ord_by_start_and_inv_length(&other.emptiable_rel_bound_pair())
    }
}

impl Interval for EmptiableRelativeInterval {}

impl HasDuration for EmptiableRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(interval) => interval.duration(),
            Self::Empty(empty) => empty.duration(),
        }
    }
}

impl HasRelativity for EmptiableRelativeInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bound(interval) => interval.relativity(),
            Self::Empty(empty) => empty.relativity(),
        }
    }
}

impl HasOpenness for EmptiableRelativeInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(interval) => interval.openness(),
            Self::Empty(empty) => empty.openness(),
        }
    }
}

impl HasEmptiableRelativeBoundPair for EmptiableRelativeInterval {
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelativeBoundPair {
        match self {
            Self::Bound(interval) => EmptiableRelativeBoundPair::from(interval.rel_bound_pair()),
            Self::Empty(interval) => interval.emptiable_rel_bound_pair(),
        }
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Bound(interval) => interval.partial_rel_start(),
            Self::Empty(empty) => empty.partial_rel_start(),
        }
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Bound(interval) => interval.partial_rel_end(),
            Self::Empty(empty) => empty.partial_rel_end(),
        }
    }
}

impl IsEmpty for EmptiableRelativeInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for EmptiableRelativeInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableRelativeInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_rel_bound_pair().cmp(&other.emptiable_rel_bound_pair())
    }
}

impl From<BoundedRelativeInterval> for EmptiableRelativeInterval {
    fn from(value: BoundedRelativeInterval) -> Self {
        EmptiableRelativeInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedToFutureRelativeInterval> for EmptiableRelativeInterval {
    fn from(value: HalfBoundedToFutureRelativeInterval) -> Self {
        EmptiableRelativeInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedToPastRelativeInterval> for EmptiableRelativeInterval {
    fn from(value: HalfBoundedToPastRelativeInterval) -> Self {
        EmptiableRelativeInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedRelativeInterval> for EmptiableRelativeInterval {
    fn from(value: HalfBoundedRelativeInterval) -> Self {
        EmptiableRelativeInterval::Bound(value.to_interval())
    }
}

impl From<UnboundedInterval> for EmptiableRelativeInterval {
    fn from(value: UnboundedInterval) -> Self {
        EmptiableRelativeInterval::Bound(RelativeInterval::Unbounded(value))
    }
}

impl From<EmptyInterval> for EmptiableRelativeInterval {
    fn from(value: EmptyInterval) -> Self {
        EmptiableRelativeInterval::Empty(value)
    }
}

impl From<RelativeBoundPair> for EmptiableRelativeInterval {
    fn from(value: RelativeBoundPair) -> Self {
        EmptiableRelativeInterval::Bound(RelativeInterval::from(value))
    }
}

impl From<EmptiableRelativeBoundPair> for EmptiableRelativeInterval {
    fn from(value: EmptiableRelativeBoundPair) -> Self {
        match value.bound() {
            Some(rel_bound_pair) => Self::from(rel_bound_pair),
            None => Self::Empty(EmptyInterval),
        }
    }
}

impl From<RelativeInterval> for EmptiableRelativeInterval {
    fn from(value: RelativeInterval) -> Self {
        Self::Bound(value)
    }
}

impl From<()> for EmptiableRelativeInterval {
    fn from(_value: ()) -> Self {
        EmptiableRelativeInterval::Empty(EmptyInterval)
    }
}

//! Absolute emptiable interval
//!
//! Represents any form of specific absolute intervals, including
//! [`EmptyInterval`]. That includes [`BoundedAbsInterval`],
//! [`HalfBoundedAbsInterval`], [`UnboundedInterval`],
//! and [`EmptyInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`AbsBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is for dealing with absolute intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`AbsBoundPair`].
//!
//! If you want to exclude [`EmptyInterval`] as a possible variant, see
//! [`AbsInterval`].

use std::cmp::Ordering;
use std::ops::RangeBounds;

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
    EmptiableAbsBoundPair,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
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
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableAbsInterval {
    Bound(AbsInterval),
    Empty(EmptyInterval),
}

impl EmptiableAbsInterval {
    /// Creates an [`EmptiableAbsInterval`] from a [`Timestamp`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsFiniteBoundPos, AbsInterval, EmptiableAbsInterval, HasEmptiableAbsBoundPair,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let interval = EmptiableAbsInterval::from_range(start..end);
    ///
    /// assert_eq!(
    ///     interval.partial_abs_start(),
    ///     Some(AbsFiniteBoundPos::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     interval.partial_abs_end(),
    ///     Some(AbsFiniteBoundPos::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        AbsInterval::from_range(range).to_emptiable()
    }

    /// Returns the content of the [`Bound`](EmptiableAbsInterval::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableAbsInterval::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{
    /// #     EmptiableAbsInterval, AbsInterval, BoundedAbsInterval,
    /// # };
    /// # use periodical::intervals::special::EmptyInterval;
    /// let interval = BoundedAbsInterval::new(
    ///     "2026-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     "2026-01-01 16:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// )
    /// .to_interval();
    ///
    /// let bound_emptiable_interval = EmptiableAbsInterval::Bound(interval.clone());
    /// let empty_emptiable_interval = EmptiableAbsInterval::Empty(EmptyInterval);
    ///
    /// assert_eq!(bound_emptiable_interval.bound(), Some(interval));
    /// assert_eq!(empty_emptiable_interval.bound(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<AbsInterval> {
        match self {
            Self::Bound(interval) => Some(interval),
            Self::Empty(_) => None,
        }
    }

    /// Compares two [`AbsInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Uses [`EmptiableAbsBoundPair::ord_by_start_and_inv_length`] under
    /// the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will
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
        self.emptiable_abs_bound_pair()
            .ord_by_start_and_inv_length(&other.emptiable_abs_bound_pair())
    }
}

impl Interval for EmptiableAbsInterval {}

impl HasDuration for EmptiableAbsInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(interval) => interval.duration(),
            Self::Empty(empty) => empty.duration(),
        }
    }
}

impl HasRelativity for EmptiableAbsInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bound(interval) => interval.relativity(),
            Self::Empty(empty) => empty.relativity(),
        }
    }
}

impl HasOpenness for EmptiableAbsInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(interval) => interval.openness(),
            Self::Empty(empty) => empty.openness(),
        }
    }
}

impl HasEmptiableAbsBoundPair for EmptiableAbsInterval {
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsBoundPair {
        match self {
            Self::Bound(interval) => EmptiableAbsBoundPair::from(interval.abs_bound_pair()),
            Self::Empty(interval) => interval.emptiable_abs_bound_pair(),
        }
    }

    fn partial_abs_start(&self) -> Option<AbsStartBound> {
        match self {
            Self::Bound(interval) => interval.partial_abs_start(),
            Self::Empty(interval) => interval.partial_abs_start(),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsEndBound> {
        match self {
            Self::Bound(interval) => interval.partial_abs_end(),
            Self::Empty(interval) => interval.partial_abs_end(),
        }
    }
}

impl IsEmpty for EmptiableAbsInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for EmptiableAbsInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableAbsInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_abs_bound_pair().cmp(&other.emptiable_abs_bound_pair())
    }
}

impl From<BoundedAbsInterval> for EmptiableAbsInterval {
    fn from(value: BoundedAbsInterval) -> Self {
        EmptiableAbsInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedToFutureAbsInterval> for EmptiableAbsInterval {
    fn from(value: HalfBoundedToFutureAbsInterval) -> Self {
        EmptiableAbsInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedToPastAbsInterval> for EmptiableAbsInterval {
    fn from(value: HalfBoundedToPastAbsInterval) -> Self {
        EmptiableAbsInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedAbsInterval> for EmptiableAbsInterval {
    fn from(value: HalfBoundedAbsInterval) -> Self {
        EmptiableAbsInterval::Bound(value.to_interval())
    }
}

impl From<UnboundedInterval> for EmptiableAbsInterval {
    fn from(value: UnboundedInterval) -> Self {
        EmptiableAbsInterval::Bound(AbsInterval::Unbounded(value))
    }
}

impl From<EmptyInterval> for EmptiableAbsInterval {
    fn from(value: EmptyInterval) -> Self {
        EmptiableAbsInterval::Empty(value)
    }
}

impl From<AbsBoundPair> for EmptiableAbsInterval {
    fn from(value: AbsBoundPair) -> Self {
        EmptiableAbsInterval::Bound(AbsInterval::from(value))
    }
}

impl From<EmptiableAbsBoundPair> for EmptiableAbsInterval {
    fn from(value: EmptiableAbsBoundPair) -> Self {
        match value.bound() {
            Some(abs_bound_pair) => Self::from(abs_bound_pair),
            None => Self::Empty(EmptyInterval),
        }
    }
}

impl From<AbsInterval> for EmptiableAbsInterval {
    fn from(value: AbsInterval) -> Self {
        Self::Bound(value)
    }
}

impl From<()> for EmptiableAbsInterval {
    fn from(_value: ()) -> Self {
        EmptiableAbsInterval::Empty(EmptyInterval)
    }
}

//! Absolute emptiable interval
//!
//! Represents any form of specific absolute intervals, including
//! [`EmptyInterval`]. That includes [`BoundedAbsoluteInterval`],
//! [`HalfBoundedAbsoluteInterval`], [`UnboundedInterval`],
//! and [`EmptyInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`AbsoluteBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is for dealing with absolute intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`AbsoluteBoundPair`].
//!
//! If you want to exclude [`EmptyInterval`] as a possible variant, see
//! [`AbsoluteInterval`].

use std::cmp::Ordering;
use std::ops::RangeBounds;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
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
pub enum EmptiableAbsoluteInterval {
    Bound(AbsoluteInterval),
    Empty(EmptyInterval),
}

impl EmptiableAbsoluteInterval {
    /// Creates an [`EmptiableAbsoluteInterval`] from a [`Timestamp`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteFiniteBound, AbsoluteInterval, EmptiableAbsoluteInterval, HasEmptiableAbsoluteBoundPair,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let interval = EmptiableAbsoluteInterval::from_range(start..end);
    ///
    /// assert_eq!(
    ///     interval.partial_abs_start(),
    ///     Some(AbsoluteFiniteBound::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     interval.partial_abs_end(),
    ///     Some(AbsoluteFiniteBound::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        AbsoluteInterval::from_range(range).to_emptiable()
    }

    /// Returns the content of the [`Bound`](EmptiableAbsoluteInterval::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableAbsoluteInterval::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{
    /// #     EmptiableAbsoluteInterval, AbsoluteInterval, BoundedAbsoluteInterval,
    /// # };
    /// # use periodical::intervals::special::EmptyInterval;
    /// let interval = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     "2026-01-01 16:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// )
    /// .to_interval();
    ///
    /// let bound_emptiable_interval = EmptiableAbsoluteInterval::Bound(interval.clone());
    /// let empty_emptiable_interval = EmptiableAbsoluteInterval::Empty(EmptyInterval);
    ///
    /// assert_eq!(bound_emptiable_interval.bound(), Some(interval));
    /// assert_eq!(empty_emptiable_interval.bound(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<AbsoluteInterval> {
        match self {
            Self::Bound(interval) => Some(interval),
            Self::Empty(_) => None,
        }
    }

    /// Compares two [`AbsoluteInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Uses [`EmptiableAbsoluteBoundPair::ord_by_start_and_inv_length`] under
    /// the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteInterval;
    /// # let mut bounds: [AbsoluteInterval; 0] = [];
    /// bounds.sort_by(AbsoluteInterval::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.emptiable_abs_bound_pair()
            .ord_by_start_and_inv_length(&other.emptiable_abs_bound_pair())
    }
}

impl Interval for EmptiableAbsoluteInterval {}

impl HasDuration for EmptiableAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(interval) => interval.duration(),
            Self::Empty(empty) => empty.duration(),
        }
    }
}

impl HasRelativity for EmptiableAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bound(interval) => interval.relativity(),
            Self::Empty(empty) => empty.relativity(),
        }
    }
}

impl HasOpenness for EmptiableAbsoluteInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(interval) => interval.openness(),
            Self::Empty(empty) => empty.openness(),
        }
    }
}

impl HasEmptiableAbsoluteBoundPair for EmptiableAbsoluteInterval {
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsoluteBoundPair {
        match self {
            Self::Bound(interval) => EmptiableAbsoluteBoundPair::from(interval.abs_bound_pair()),
            Self::Empty(interval) => interval.emptiable_abs_bound_pair(),
        }
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Bound(interval) => interval.partial_abs_start(),
            Self::Empty(interval) => interval.partial_abs_start(),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Bound(interval) => interval.partial_abs_end(),
            Self::Empty(interval) => interval.partial_abs_end(),
        }
    }
}

impl IsEmpty for EmptiableAbsoluteInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for EmptiableAbsoluteInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableAbsoluteInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_abs_bound_pair().cmp(&other.emptiable_abs_bound_pair())
    }
}

impl From<BoundedAbsoluteInterval> for EmptiableAbsoluteInterval {
    fn from(value: BoundedAbsoluteInterval) -> Self {
        EmptiableAbsoluteInterval::Bound(value.to_interval())
    }
}

impl From<HalfBoundedAbsoluteInterval> for EmptiableAbsoluteInterval {
    fn from(value: HalfBoundedAbsoluteInterval) -> Self {
        EmptiableAbsoluteInterval::Bound(value.to_interval())
    }
}

impl From<UnboundedInterval> for EmptiableAbsoluteInterval {
    fn from(value: UnboundedInterval) -> Self {
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Unbounded(value))
    }
}

impl From<EmptyInterval> for EmptiableAbsoluteInterval {
    fn from(value: EmptyInterval) -> Self {
        EmptiableAbsoluteInterval::Empty(value)
    }
}

impl From<AbsoluteBoundPair> for EmptiableAbsoluteInterval {
    fn from(value: AbsoluteBoundPair) -> Self {
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::from(value))
    }
}

impl From<EmptiableAbsoluteBoundPair> for EmptiableAbsoluteInterval {
    fn from(value: EmptiableAbsoluteBoundPair) -> Self {
        match value.bound() {
            Some(abs_bound_pair) => Self::from(abs_bound_pair),
            None => Self::Empty(EmptyInterval),
        }
    }
}

impl From<AbsoluteInterval> for EmptiableAbsoluteInterval {
    fn from(value: AbsoluteInterval) -> Self {
        Self::Bound(value)
    }
}

/// Converts `(Option<Timestamp>, Option<Timestamp>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl From<(Option<Timestamp>, Option<Timestamp>)> for EmptiableAbsoluteInterval {
    fn from((from_opt, to_opt): (Option<Timestamp>, Option<Timestamp>)) -> Self {
        Self::from(AbsoluteBoundPair::from((from_opt, to_opt)).to_emptiable())
    }
}

/// Converts `(Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp,
/// BoundInclusivity)>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl
    From<(
        Option<(Timestamp, BoundInclusivity)>,
        Option<(Timestamp, BoundInclusivity)>,
    )> for EmptiableAbsoluteInterval
{
    fn from(
        value: (
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        ),
    ) -> Self {
        Self::from(AbsoluteBoundPair::from(value))
    }
}

/// Converts `(bool, AbsoluteStartBound, AbsoluteEndBound)` into [`EmptiableAbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an empty interval.
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, AbsoluteStartBound, AbsoluteEndBound)> for EmptiableAbsoluteInterval {
    fn from(value: (bool, AbsoluteStartBound, AbsoluteEndBound)) -> Self {
        Self::from(EmptiableAbsoluteBoundPair::from(value))
    }
}

/// Converts `(bool, Option<Timestamp>, Option<Timestamp>)` into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, Option<Timestamp>, Option<Timestamp>)> for EmptiableAbsoluteInterval {
    fn from(value: (bool, Option<Timestamp>, Option<Timestamp>)) -> Self {
        Self::from(EmptiableAbsoluteBoundPair::from(value))
    }
}

/// Converts `(bool, Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp,
/// BoundInclusivity)>)` into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl
    From<(
        bool,
        Option<(Timestamp, BoundInclusivity)>,
        Option<(Timestamp, BoundInclusivity)>,
    )> for EmptiableAbsoluteInterval
{
    fn from(
        value: (
            bool,
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        ),
    ) -> Self {
        Self::from(EmptiableAbsoluteBoundPair::from(value))
    }
}

impl From<()> for EmptiableAbsoluteInterval {
    fn from(_value: ()) -> Self {
        EmptiableAbsoluteInterval::Empty(EmptyInterval)
    }
}

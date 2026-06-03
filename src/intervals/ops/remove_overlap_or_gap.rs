//! Removal of overlaps or gaps between intervals
//!
//! Given two intervals, adjusts the first interval so that no gap nor overlap
//! exist between the two intervals.
//!
//! This module combines [filling the gap](crate::intervals::ops::fill_gap) if
//! no overlap is present, and [removing the overlap](crate::intervals::ops::remove_overlap) in the contrary.

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::remove_overlap::{remove_end_overlap_abs, remove_start_overlap_abs};
use super::shrink::{ShrinkableEndBound, ShrinkableStartBound};
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, Interval};
use crate::intervals::ops::Complementable;
use crate::intervals::ops::remove_overlap::{remove_end_overlap_rel, remove_start_overlap_rel};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::ComplementResult;

/// Result of an overlap/gap removal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum OverlapOrGapRemovalResult<T> {
    /// Resulted in a single element
    ///
    /// An empty interval counts as one too.
    Single(T),
    /// Resulted in two split elements
    Split(T, T),
}

impl<T> OverlapOrGapRemovalResult<T> {
    /// Whether it is of the [`Single`](OverlapOrGapRemovalResult::Single)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap_or_gap::OverlapOrGapRemovalResult;
    /// assert!(OverlapOrGapRemovalResult::<()>::Single(()).is_single());
    /// assert!(!OverlapOrGapRemovalResult::<()>::Split((), ()).is_single());
    /// ```
    #[must_use]
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Whether it is of the [`Split`](OverlapOrGapRemovalResult::Split) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap_or_gap::OverlapOrGapRemovalResult;
    /// assert!(OverlapOrGapRemovalResult::<()>::Split((), ()).is_split());
    /// assert!(!OverlapOrGapRemovalResult::<()>::Single(()).is_split());
    /// ```
    #[must_use]
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Returns the content of the [`Single`](OverlapOrGapRemovalResult::Single)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Single`](OverlapOrGapRemovalResult::Single) variant
    /// in an [`Option`]. If instead `self` is another variant, the method
    /// returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap_or_gap::OverlapOrGapRemovalResult;
    /// assert_eq!(
    ///     OverlapOrGapRemovalResult::<u8>::Single(10).single(),
    ///     Some(10)
    /// );
    /// assert_eq!(
    ///     OverlapOrGapRemovalResult::<u8>::Split(10, 20).single(),
    ///     None
    /// );
    /// ```
    #[must_use]
    pub fn single(self) -> Option<T> {
        match self {
            Self::Single(s) => Some(s),
            Self::Split(..) => None,
        }
    }

    /// Returns the content of the [`Split`](OverlapOrGapRemovalResult::Split)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Split`](OverlapOrGapRemovalResult::Split) variant
    /// in an [`Option`]. If instead `self` is another variant, the method
    /// returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap_or_gap::OverlapOrGapRemovalResult;
    /// assert_eq!(
    ///     OverlapOrGapRemovalResult::<u8>::Split(10, 20).split(),
    ///     Some((10, 20))
    /// );
    /// assert_eq!(OverlapOrGapRemovalResult::<u8>::Single(10).split(), None);
    /// ```
    #[must_use]
    pub fn split(self) -> Option<(T, T)> {
        match self {
            Self::Single(_) => None,
            Self::Split(s1, s2) => Some((s1, s2)),
        }
    }

    /// Maps the contents of the [`Single`](OverlapOrGapRemovalResult::Single)
    /// and [`Split`](OverlapOrGapRemovalResult::Split) variants
    ///
    /// Uses a closure that describes the transformation from `T` to `U`, used
    /// for each element in the enum.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap_or_gap::OverlapOrGapRemovalResult;
    /// assert_eq!(
    ///     OverlapOrGapRemovalResult::<u8>::Single(10).map(|x| x * 2),
    ///     OverlapOrGapRemovalResult::<u8>::Single(20),
    /// );
    /// assert_eq!(
    ///     OverlapOrGapRemovalResult::<u8>::Split(10, 20).map(|x| x * 2),
    ///     OverlapOrGapRemovalResult::<u8>::Split(20, 40),
    /// );
    /// ```
    #[must_use]
    pub fn map<F, U>(self, mut f: F) -> OverlapOrGapRemovalResult<U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Self::Single(s) => OverlapOrGapRemovalResult::Single((f)(s)),
            Self::Split(s1, s2) => OverlapOrGapRemovalResult::Split((f)(s1), (f)(s2)),
        }
    }
}

/// Capacity to remove overlaps or gaps between two intervals
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.remove_overlap_or_gap(&second_interval),
///     OverlapOrGapRemovalResult::Single(AbsBoundPair::new(
///         AbsFiniteBoundPos::new(
///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_start_bound(),
///         AbsFiniteBoundPos::new_with_inclusivity(
///             "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///             BoundInclusivity::Exclusive,
///         ).to_end_bound(),
///     ).to_emptiable()),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait RemovableOverlapOrGap<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns the [`OverlapOrGapRemovalResult`] of the interval
    ///
    /// A copy of the main interval, `self`, is created without any overlap or
    /// gap with the second given interval remaining.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
    /// let first_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 17:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.remove_overlap_or_gap(&second_interval),
    ///     OverlapOrGapRemovalResult::Split(
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new(
    ///                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             ).to_start_bound(),
    ///             AbsFiniteBoundPos::new_with_inclusivity(
    ///                 "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_end_bound(),
    ///         ).to_emptiable(),
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new_with_inclusivity(
    ///                 "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_start_bound(),
    ///             AbsFiniteBoundPos::new(
    ///                 "2025-01-01 17:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             ).to_end_bound(),
    ///         ).to_emptiable(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output>;
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsBoundPair;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelBoundPair;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<AbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableAbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableAbsBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<AbsInterval> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableAbsInterval> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableAbsInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<BoundedAbsInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &BoundedAbsInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => OverlapOrGapRemovalResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                OverlapOrGapRemovalResult::Split(split_before, split_after)
            },
        }
    }
}

impl RemovableOverlapOrGap<HalfBoundedAbsInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfBoundedAbsInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => OverlapOrGapRemovalResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                OverlapOrGapRemovalResult::Split(split_before, split_after)
            },
        }
    }
}

impl RemovableOverlapOrGap<RelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableRelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableRelBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<RelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableRelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableRelInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<BoundedRelInterval> for UnboundedInterval {
    type Output = HalfBoundedRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &BoundedRelInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => OverlapOrGapRemovalResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                OverlapOrGapRemovalResult::Split(split_before, split_after)
            },
        }
    }
}

impl RemovableOverlapOrGap<HalfBoundedRelInterval> for UnboundedInterval {
    type Output = HalfBoundedRelInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfBoundedRelInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => OverlapOrGapRemovalResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                OverlapOrGapRemovalResult::Split(split_before, split_after)
            },
        }
    }
}

impl RemovableOverlapOrGap<UnboundedInterval> for UnboundedInterval {
    type Output = EmptyInterval;

    fn remove_overlap_or_gap(&self, _rhs: &UnboundedInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        OverlapOrGapRemovalResult::Single(EmptyInterval)
    }
}

impl RemovableOverlapOrGap<EmptyInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn remove_overlap_or_gap(&self, _rhs: &EmptyInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        OverlapOrGapRemovalResult::Single(*self)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = EmptyInterval;

    fn remove_overlap_or_gap(&self, _rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        OverlapOrGapRemovalResult::Single(*self)
    }
}

/// Removes any overlap or gap between two [`AbsBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_abs_bound_pair(
    a: &AbsBoundPair,
    b: &AbsBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableAbsBoundPair> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
                );
            };

            let new_end_bound = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::from(a.grow_end(new_end_bound)))
        },
        Dop::OutsideAfter => {
            let AbsEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
                );
            };

            let new_start_bound = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::from(a.grow_start(new_start_bound)))
        },
        Dop::EndsOnStart => {
            let AbsStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `EndsOnStart`"
                );
            };

            let new_end_bound = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(a.shrink_end(new_end_bound)))
        },
        Dop::StartsOnEnd => {
            let AbsEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `StartsOnEnd`"
                );
            };

            let new_start_bound = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(a.shrink_start(new_start_bound)))
        },
        Dop::CrossesStart => {
            let AbsStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end_bound = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::from(a.shrink_end(new_end_bound)))
        },
        Dop::CrossesEnd => {
            let AbsEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start_bound = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::from(a.shrink_start(new_start_bound)))
        },
        Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd | Dop::Equal => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty)
        },
        Dop::ContainsAndSameStart => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::from(remove_end_overlap_abs(a, b)))
        },
        Dop::ContainsAndSameEnd => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::from(remove_start_overlap_abs(a, b)))
        },
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            EmptiableAbsBoundPair::from(remove_start_overlap_abs(a, b)),
            EmptiableAbsBoundPair::from(remove_end_overlap_abs(a, b)),
        ),
    }
}

/// Removes any overlap or gap between an [`AbsBoundPair`] and an
/// [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableAbsBoundPair> {
    let EmptiableAbsBoundPair::Bound(b_abs_bound_pair) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::from(a.clone()));
    };

    remove_overlap_or_gap_abs_bound_pair(a, b_abs_bound_pair)
}

/// Removes any overlap or gap between two [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_emptiable_abs_bound_pair(
    a: &EmptiableAbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableAbsBoundPair> {
    if let (EmptiableAbsBoundPair::Bound(a_abs_bound_pair), EmptiableAbsBoundPair::Bound(b_abs_bound_pair)) = (a, b) {
        return remove_overlap_or_gap_abs_bound_pair(a_abs_bound_pair, b_abs_bound_pair);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

/// Removes any overlap or gap between two [`RelBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_rel_bound_pair(
    a: &RelBoundPair,
    b: &RelBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableRelBoundPair> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let RelStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
                );
            };

            let new_end_bound = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::from(a.grow_end(new_end_bound)))
        },
        Dop::OutsideAfter => {
            let RelEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
                );
            };

            let new_start_bound = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::from(a.grow_start(new_start_bound)))
        },
        Dop::EndsOnStart => {
            let RelStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `EndsOnStart`"
                );
            };

            let new_end_bound = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::Bound(a.shrink_end(new_end_bound)))
        },
        Dop::StartsOnEnd => {
            let RelEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `StartsOnEnd`"
                );
            };

            let new_start_bound = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::Bound(a.shrink_start(new_start_bound)))
        },
        Dop::CrossesStart => {
            let RelStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end_bound = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::from(a.shrink_end(new_end_bound)))
        },
        Dop::CrossesEnd => {
            let RelEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start_bound = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::from(a.shrink_start(new_start_bound)))
        },
        Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd | Dop::Equal => {
            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::Empty)
        },
        Dop::ContainsAndSameStart => {
            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::from(remove_end_overlap_rel(a, b)))
        },
        Dop::ContainsAndSameEnd => {
            OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::from(remove_start_overlap_rel(a, b)))
        },
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            EmptiableRelBoundPair::from(remove_start_overlap_rel(a, b)),
            EmptiableRelBoundPair::from(remove_end_overlap_rel(a, b)),
        ),
    }
}

/// Removes any overlap or gap between an [`RelBoundPair`] and an
/// [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelBoundPair,
    b: &EmptiableRelBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableRelBoundPair> {
    let EmptiableRelBoundPair::Bound(b_rel_bound_pair) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableRelBoundPair::from(a.clone()));
    };

    remove_overlap_or_gap_rel_bound_pair(a, b_rel_bound_pair)
}

/// Removes any overlap or gap between two [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_emptiable_rel_bound_pair(
    a: &EmptiableRelBoundPair,
    b: &EmptiableRelBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableRelBoundPair> {
    if let (EmptiableRelBoundPair::Bound(a_rel_bound_pair), EmptiableRelBoundPair::Bound(b_rel_bound_pair)) = (a, b) {
        return remove_overlap_or_gap_rel_bound_pair(a_rel_bound_pair, b_rel_bound_pair);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

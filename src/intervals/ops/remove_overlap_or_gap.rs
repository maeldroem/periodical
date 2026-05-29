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
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, Interval};
use crate::intervals::ops::Complementable;
use crate::intervals::ops::remove_overlap::{remove_end_overlap_rel, remove_start_overlap_rel};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeInterval,
    RelativeStartBound,
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
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.remove_overlap_or_gap(&second_interval),
///     OverlapOrGapRemovalResult::Single(AbsoluteBoundPair::new(
///         AbsoluteFiniteBoundPosition::new(
///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_start_bound(),
///         AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 17:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.remove_overlap_or_gap(&second_interval),
    ///     OverlapOrGapRemovalResult::Split(
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBoundPosition::new(
    ///                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             ).to_start_bound(),
    ///             AbsoluteFiniteBoundPosition::new_with_inclusivity(
    ///                 "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_end_bound(),
    ///         ).to_emptiable(),
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBoundPosition::new_with_inclusivity(
    ///                 "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_start_bound(),
    ///             AbsoluteFiniteBoundPosition::new(
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

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteBoundPair;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
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

impl<Rhs> RemovableOverlapOrGap<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeBoundPair;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
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

impl<Rhs> RemovableOverlapOrGap<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<AbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsoluteBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableAbsoluteBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<AbsoluteInterval> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableAbsoluteInterval> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableAbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &BoundedAbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => OverlapOrGapRemovalResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                OverlapOrGapRemovalResult::Split(split_before, split_after)
            },
        }
    }
}

impl RemovableOverlapOrGap<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfBoundedAbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => OverlapOrGapRemovalResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                OverlapOrGapRemovalResult::Split(split_before, split_after)
            },
        }
    }
}

impl RemovableOverlapOrGap<RelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelativeBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableRelativeBoundPair) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<RelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<EmptiableRelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableRelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(Self::Output::from)
    }
}

impl RemovableOverlapOrGap<BoundedRelativeInterval> for UnboundedInterval {
    type Output = HalfBoundedRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &BoundedRelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => OverlapOrGapRemovalResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                OverlapOrGapRemovalResult::Split(split_before, split_after)
            },
        }
    }
}

impl RemovableOverlapOrGap<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = HalfBoundedRelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfBoundedRelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
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

/// Removes any overlap or gap between two [`AbsoluteBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &AbsoluteBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBoundPair> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsoluteStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.time(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(a.grow_end(new_end_bound)))
        },
        Dop::OutsideAfter => {
            let AbsoluteEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.time(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(a.grow_start(new_start_bound)))
        },
        Dop::EndsOnStart => {
            let AbsoluteStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `EndsOnStart`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.time(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(a.shrink_end(new_end_bound)))
        },
        Dop::StartsOnEnd => {
            let AbsoluteEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `StartsOnEnd`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.time(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(a.shrink_start(new_start_bound)))
        },
        Dop::CrossesStart => {
            let AbsoluteStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.time(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(a.shrink_end(new_end_bound)))
        },
        Dop::CrossesEnd => {
            let AbsoluteEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.time(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(a.shrink_start(new_start_bound)))
        },
        Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd | Dop::Equal => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty)
        },
        Dop::ContainsAndSameStart => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(remove_end_overlap_abs(a, b)))
        },
        Dop::ContainsAndSameEnd => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(remove_start_overlap_abs(a, b)))
        },
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            EmptiableAbsoluteBoundPair::from(remove_start_overlap_abs(a, b)),
            EmptiableAbsoluteBoundPair::from(remove_end_overlap_abs(a, b)),
        ),
    }
}

/// Removes any overlap or gap between an [`AbsoluteBoundPair`] and an
/// [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBoundPair> {
    let EmptiableAbsoluteBoundPair::Bound(b_abs_bound_pair) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(a.clone()));
    };

    remove_overlap_or_gap_abs_bound_pair(a, b_abs_bound_pair)
}

/// Removes any overlap or gap between two [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBoundPair> {
    if let (EmptiableAbsoluteBoundPair::Bound(a_abs_bound_pair), EmptiableAbsoluteBoundPair::Bound(b_abs_bound_pair)) =
        (a, b)
    {
        return remove_overlap_or_gap_abs_bound_pair(a_abs_bound_pair, b_abs_bound_pair);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

/// Removes any overlap or gap between two [`RelativeBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &RelativeBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableRelativeBoundPair> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let RelativeStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
                );
            };

            let new_end_bound = RelativeEndBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.offset(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::from(a.grow_end(new_end_bound)))
        },
        Dop::OutsideAfter => {
            let RelativeEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
                );
            };

            let new_start_bound = RelativeStartBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.offset(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::from(a.grow_start(new_start_bound)))
        },
        Dop::EndsOnStart => {
            let RelativeStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `EndsOnStart`"
                );
            };

            let new_end_bound = RelativeEndBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.offset(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::Bound(a.shrink_end(new_end_bound)))
        },
        Dop::StartsOnEnd => {
            let RelativeEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `StartsOnEnd`"
                );
            };

            let new_start_bound = RelativeStartBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.offset(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::Bound(a.shrink_start(new_start_bound)))
        },
        Dop::CrossesStart => {
            let RelativeStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end_bound = RelativeEndBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.offset(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::from(a.shrink_end(new_end_bound)))
        },
        Dop::CrossesEnd => {
            let RelativeEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start_bound = RelativeStartBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                finite_bound_position.offset(),
                finite_bound_position.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::from(a.shrink_start(new_start_bound)))
        },
        Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd | Dop::Equal => {
            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::Empty)
        },
        Dop::ContainsAndSameStart => {
            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::from(remove_end_overlap_rel(a, b)))
        },
        Dop::ContainsAndSameEnd => {
            OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::from(remove_start_overlap_rel(a, b)))
        },
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            EmptiableRelativeBoundPair::from(remove_start_overlap_rel(a, b)),
            EmptiableRelativeBoundPair::from(remove_end_overlap_rel(a, b)),
        ),
    }
}

/// Removes any overlap or gap between an [`RelativeBoundPair`] and an
/// [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableRelativeBoundPair> {
    let EmptiableRelativeBoundPair::Bound(b_rel_bound_pair) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableRelativeBoundPair::from(a.clone()));
    };

    remove_overlap_or_gap_rel_bound_pair(a, b_rel_bound_pair)
}

/// Removes any overlap or gap between two [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more information.
#[must_use]
pub fn remove_overlap_or_gap_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> OverlapOrGapRemovalResult<EmptiableRelativeBoundPair> {
    if let (EmptiableRelativeBoundPair::Bound(a_rel_bound_pair), EmptiableRelativeBoundPair::Bound(b_rel_bound_pair)) =
        (a, b)
    {
        return remove_overlap_or_gap_rel_bound_pair(a_rel_bound_pair, b_rel_bound_pair);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

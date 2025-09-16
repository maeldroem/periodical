//! Removal of overlaps or gaps between intervals
//!
//! Given two intervals, adjusts the first interval so that no gap nor overlap exist between the two intervals.
//!
//! This module combines [filling the gap](crate::intervals::ops::fill_gap) if no overlap is present,
//! and [removing the overlap](crate::intervals::ops::remove_overlap) in the contrary.

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::prelude::*;
use super::remove_overlap::{remove_end_overlap_abs, remove_start_overlap_abs};
use super::shrink::{ShrinkableEndBound, ShrinkableStartBound};

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    BoundedAbsoluteInterval, EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval, HasAbsoluteBounds,
    HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::remove_overlap::{remove_end_overlap_rel, remove_start_overlap_rel};
use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBounds, HalfBoundedRelativeInterval, RelativeBounds, RelativeEndBound,
    RelativeFiniteBound, RelativeInterval, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Result of an overlap/gap removal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapOrGapRemovalResult<T> {
    /// Resulted in a single element
    ///
    /// An empty interval counts as one too.
    Single(T),
    /// Resulted in two split elements
    Split(T, T),
}

impl<T> OverlapOrGapRemovalResult<T> {
    /// Whether it is of the [`Single`](OverlapOrGapRemovalResult::Single) variant
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

    /// Returns the content of the [`Single`](OverlapOrGapRemovalResult::Single) variant
    ///
    /// Consumes `self` and puts the content of the [`Single`](OverlapOrGapRemovalResult::Single) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap_or_gap::OverlapOrGapRemovalResult;
    /// assert_eq!(OverlapOrGapRemovalResult::<u8>::Single(10).single(), Some(10));
    /// assert_eq!(OverlapOrGapRemovalResult::<u8>::Split(10, 20).single(), None);
    /// ```
    #[must_use]
    pub fn single(self) -> Option<T> {
        match self {
            Self::Single(s) => Some(s),
            Self::Split(..) => None,
        }
    }

    /// Returns the content of the [`Split`](OverlapOrGapRemovalResult::Split) variant
    ///
    /// Consumes `self` and puts the content of the [`Split`](OverlapOrGapRemovalResult::Split) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap_or_gap::OverlapOrGapRemovalResult;
    /// assert_eq!(OverlapOrGapRemovalResult::<u8>::Split(10, 20).split(), Some((10, 20)));
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
    /// Uses a closure that describes the transformation from `T` to `U`, used for each element in the enum.
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
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
/// let first_interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// let second_interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// assert_eq!(
///     first_interval.remove_overlap_or_gap(&second_interval),
///     OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
///             BoundInclusivity::Exclusive,
///         )),
///     ))),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait RemovableOverlapOrGap<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns the [`OverlapOrGapRemovalResult`] of the interval
    ///
    /// A copy of the main interval, `self`, is created without any overlap or gap
    /// with the second given interval remaining.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
    /// let first_interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 17:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let second_interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.remove_overlap_or_gap(&second_interval),
    ///     OverlapOrGapRemovalResult::Split(
    ///         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )),
    ///         )),
    ///         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )),
    ///             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 17:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///         )),
    ///     ),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output>;
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = EmptiableAbsoluteBounds;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = EmptiableRelativeBounds;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<AbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsoluteBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<EmptiableAbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableAbsoluteBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<AbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &BoundedAbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfBoundedAbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<RelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelativeBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<EmptiableRelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableRelativeBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<RelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<BoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &BoundedRelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfBoundedRelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map(RelativeInterval::from)
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

/// Removes any overlap or gap between two [`AbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap_or_gap) for more information.
#[must_use]
pub fn remove_overlap_or_gap_abs_bounds(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OutsideBefore`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.grow_end(new_end_bound)))
        },
        Dop::OutsideAfter => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OutsideAfter`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.grow_start(new_start_bound)))
        },
        Dop::EndsOnStart => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `EndsOnStart`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(a.shrink_end(new_end_bound)))
        },
        Dop::StartsOnEnd => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `StartsOnEnd`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(a.shrink_start(new_start_bound)))
        },
        Dop::CrossesStart => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `CrossesStart`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.shrink_end(new_end_bound)))
        },
        Dop::CrossesEnd => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `CrossesEnd`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.shrink_start(new_start_bound)))
        },
        Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd | Dop::Equal => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty)
        },
        Dop::ContainsAndSameStart => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(remove_end_overlap_abs(a, b)))
        },
        Dop::ContainsAndSameEnd => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(remove_start_overlap_abs(a, b)))
        },
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            EmptiableAbsoluteBounds::from(remove_start_overlap_abs(a, b)),
            EmptiableAbsoluteBounds::from(remove_end_overlap_abs(a, b)),
        ),
    }
}

/// Removes any overlap or gap between an [`AbsoluteBounds`] and an [`EmptiableAbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap_or_gap) for more information.
#[must_use]
pub fn remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(b_abs_bounds) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.clone()));
    };

    remove_overlap_or_gap_abs_bounds(a, b_abs_bounds)
}

/// Removes any overlap or gap between two [`EmptiableAbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap_or_gap) for more information.
#[must_use]
pub fn remove_overlap_or_gap_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    if let (EmptiableAbsoluteBounds::Bound(a_abs_bounds), EmptiableAbsoluteBounds::Bound(b_abs_bounds)) = (a, b) {
        return remove_overlap_or_gap_abs_bounds(a_abs_bounds, b_abs_bounds);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

/// Removes any overlap or gap between two [`RelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap_or_gap) for more information.
#[must_use]
pub fn remove_overlap_or_gap_rel_bounds(
    a: &RelativeBounds,
    b: &RelativeBounds,
) -> OverlapOrGapRemovalResult<EmptiableRelativeBounds> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OutsideBefore`"
                );
            };

            let new_end_bound = RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(a.grow_end(new_end_bound)))
        },
        Dop::OutsideAfter => {
            let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OutsideAfter`"
                );
            };

            let new_start_bound = RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(a.grow_start(new_start_bound)))
        },
        Dop::EndsOnStart => {
            let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `EndsOnStart`"
                );
            };

            let new_end_bound = RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::Bound(a.shrink_end(new_end_bound)))
        },
        Dop::StartsOnEnd => {
            let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `StartsOnEnd`"
                );
            };

            let new_start_bound = RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::Bound(a.shrink_start(new_start_bound)))
        },
        Dop::CrossesStart => {
            let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `CrossesStart`"
                );
            };

            let new_end_bound = RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(a.shrink_end(new_end_bound)))
        },
        Dop::CrossesEnd => {
            let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `CrossesEnd`"
                );
            };

            let new_start_bound = RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(a.shrink_start(new_start_bound)))
        },
        Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd | Dop::Equal => {
            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::Empty)
        },
        Dop::ContainsAndSameStart => {
            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(remove_end_overlap_rel(a, b)))
        },
        Dop::ContainsAndSameEnd => {
            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(remove_start_overlap_rel(a, b)))
        },
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            EmptiableRelativeBounds::from(remove_start_overlap_rel(a, b)),
            EmptiableRelativeBounds::from(remove_end_overlap_rel(a, b)),
        ),
    }
}

/// Removes any overlap or gap between an [`RelativeBounds`] and an [`EmptiableRelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap_or_gap) for more information.
#[must_use]
pub fn remove_overlap_or_gap_rel_bounds_with_emptiable_rel_bounds(
    a: &RelativeBounds,
    b: &EmptiableRelativeBounds,
) -> OverlapOrGapRemovalResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(b_rel_bounds) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(a.clone()));
    };

    remove_overlap_or_gap_rel_bounds(a, b_rel_bounds)
}

/// Removes any overlap or gap between two [`EmptiableRelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap_or_gap) for more information.
#[must_use]
pub fn remove_overlap_or_gap_emptiable_rel_bounds(
    a: &EmptiableRelativeBounds,
    b: &EmptiableRelativeBounds,
) -> OverlapOrGapRemovalResult<EmptiableRelativeBounds> {
    if let (EmptiableRelativeBounds::Bound(a_rel_bounds), EmptiableRelativeBounds::Bound(b_rel_bounds)) = (a, b) {
        return remove_overlap_or_gap_rel_bounds(a_rel_bounds, b_rel_bounds);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

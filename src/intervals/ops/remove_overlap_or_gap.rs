//! Removal of overlaps and gaps between intervals

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap_position::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::prelude::*;
use super::remove_overlap::{remove_end_overlap_abs, remove_start_overlap_abs};
use super::shrink::{ShrinkableEndBound, ShrinkableStartBound};

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::remove_overlap::{remove_end_overlap_rel, remove_start_overlap_rel};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, RelativeBounds, RelativeEndBound, RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};

/// Result of an overlap/gap removal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapOrGapRemovalResult<T> {
    /// The operation was successful and resulted into a single element (an empty interval counts as one too)
    Single(T),
    /// The operation was successful and resulted into two split elements
    Split(T, T),
}

impl<T> OverlapOrGapRemovalResult<T> {
    /// Whether the [`OverlapOrGapRemovalResult`] is of the [`Single`](OverlapOrGapRemovalResult::Single) variant
    #[must_use]
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Whether the [`OverlapOrGapRemovalResult`] is of the [`Split`](OverlapOrGapRemovalResult::Split) variant
    #[must_use]
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Maps the contents of the [`Single`](OverlapOrGapRemovalResult::Single)
    /// and [`Split`](OverlapOrGapRemovalResult::Split) variants
    ///
    /// Uses a closure that describes the transformation from `T` to `U`, used for each element in the enum.
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

/// Capacity to remove any overlap or gap between two intervals
pub trait RemovableOverlapOrGap<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns a result that contains a version (or multiple versions, if split) of `self` without overlap or gap
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

impl<Rhs> RemovableOverlapOrGap<Rhs> for ClosedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfOpenAbsoluteInterval
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

impl<Rhs> RemovableOverlapOrGap<Rhs> for ClosedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for HalfOpenRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &Rhs) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<AbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsoluteBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<EmptiableAbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableAbsoluteBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<AbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &AbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<ClosedAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &ClosedAbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<HalfOpenAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfOpenAbsoluteInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl RemovableOverlapOrGap<RelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelativeBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<EmptiableRelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &EmptiableRelativeBounds) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<RelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &RelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<ClosedRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &ClosedRelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<HalfOpenRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap_or_gap(&self, rhs: &HalfOpenRelativeInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map(RelativeInterval::from)
    }
}

impl RemovableOverlapOrGap<OpenInterval> for OpenInterval {
    type Output = EmptyInterval;

    fn remove_overlap_or_gap(&self, _rhs: &OpenInterval) -> OverlapOrGapRemovalResult<Self::Output> {
        OverlapOrGapRemovalResult::Single(EmptyInterval)
    }
}

impl RemovableOverlapOrGap<EmptyInterval> for OpenInterval {
    type Output = OpenInterval;

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
        Dop::OnStart | Dop::OnEnd => {
            // No gaps nor overlaps already
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.clone()))
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
        Dop::OnStart | Dop::OnEnd => {
            // No gaps nor overlaps already
            OverlapOrGapRemovalResult::Single(EmptiableRelativeBounds::from(a.clone()))
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

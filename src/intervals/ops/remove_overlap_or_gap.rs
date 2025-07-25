//! Removal of overlaps and gaps between intervals

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap_position::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::prelude::*;
use super::remove_overlap::{remove_end_overlap, remove_start_overlap};
use super::shrink::{ShrinkableEndBound, ShrinkableStartBound};

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};

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
    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output>;
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = EmptiableAbsoluteBounds;

    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set)
    }
}

impl<Rhs> RemovableOverlapOrGap<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap_or_gap(&self, rhs: &Rhs, rule_set: OverlapRuleSet) -> OverlapOrGapRemovalResult<Self::Output> {
        remove_overlap_or_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds(), rule_set)
            .map(AbsoluteInterval::from)
    }
}

/// Removes any overlap or gap between two [`AbsoluteBounds`]
#[must_use]
pub fn remove_overlap_or_gap_abs_bounds(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, rule_set);

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
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(remove_end_overlap(a, b)))
        },
        Dop::ContainsAndSameEnd => {
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(remove_start_overlap(a, b)))
        },
        Dop::Contains => OverlapOrGapRemovalResult::Split(
            EmptiableAbsoluteBounds::from(remove_start_overlap(a, b)),
            EmptiableAbsoluteBounds::from(remove_end_overlap(a, b)),
        ),
    }
}

/// Removes any overlap or gap between an [`AbsoluteBounds`] and an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn remove_overlap_or_gap_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(b_abs_bounds) = b else {
        return OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.clone()));
    };

    remove_overlap_or_gap_abs_bounds(a, b_abs_bounds, rule_set)
}

/// Removes any overlap or gap between two [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn remove_overlap_or_gap_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
) -> OverlapOrGapRemovalResult<EmptiableAbsoluteBounds> {
    if let (EmptiableAbsoluteBounds::Bound(a_abs_bounds), EmptiableAbsoluteBounds::Bound(b_abs_bounds)) = (a, b) {
        return remove_overlap_or_gap_abs_bounds(a_abs_bounds, b_abs_bounds, rule_set);
    }

    OverlapOrGapRemovalResult::Single(a.clone())
}

//! Fill gaps between non-overlapping intervals

use super::grow::Growable;
use super::overlap_position::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};

/// Errors that can be produced when using [`GapFillable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GapFillError {
    Overlap,
}

/// Capacity to fill the gap between two intervals if they don't strictly overlap
pub trait GapFillable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns a result that contains a version of `self` that no longer has a strict gap with the given `rhs`
    ///
    /// # Errors
    ///
    /// If the two intervals are not overlapping, it should result in [`GapFillError::Overlap`].
    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError>;
}

impl<Rhs> GapFillable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
///
/// # Errors
///
/// If the given bounds overlap, this method fails with [`GapFillError::Overlap`]
pub fn fill_gap_abs_bounds(a: &AbsoluteBounds, b: &AbsoluteBounds) -> Result<AbsoluteBounds, GapFillError> {
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

            Ok(a.grow_end(new_end_bound))
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

            Ok(a.grow_start(new_start_bound))
        },
        _ => Err(GapFillError::Overlap),
    }
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
///
/// # Errors
///
/// If the given bounds overlap, this method fails with [`GapFillError::Overlap`]
pub fn fill_gap_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<AbsoluteBounds, GapFillError> {
    let EmptiableAbsoluteBounds::Bound(b_abs_bounds) = b else {
        return Ok(a.clone());
    };

    fill_gap_abs_bounds(a, b_abs_bounds)
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
///
/// # Errors
///
/// If the given bounds overlap, this method fails with [`GapFillError::Overlap`]
pub fn fill_gap_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<EmptiableAbsoluteBounds, GapFillError> {
    let EmptiableAbsoluteBounds::Bound(a_abs_bounds) = a else {
        return Ok(a.clone());
    };

    fill_gap_abs_bounds_with_emptiable_abs_bounds(a_abs_bounds, b).map(EmptiableAbsoluteBounds::from)
}

//! Fill gaps between non-overlapping intervals

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, RelativeBounds, RelativeEndBound, RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};

/// Errors that can be produced when using [`GapFillable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GapFillError {
    /// The two given intervals were overlapping
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

impl<Rhs> GapFillable<Rhs> for ClosedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfOpenAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for ClosedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfOpenRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl GapFillable<AbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &AbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<EmptiableAbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &EmptiableAbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<AbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &AbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<ClosedAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &ClosedAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<HalfOpenAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &HalfOpenAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<RelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &RelativeBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<EmptiableRelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &EmptiableRelativeBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<RelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &RelativeInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<ClosedRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &ClosedRelativeInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<HalfOpenRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &HalfOpenRelativeInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<OpenInterval> for OpenInterval {
    type Output = OpenInterval;

    fn fill_gap(&self, _rhs: &OpenInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<EmptyInterval> for OpenInterval {
    type Output = EmptyInterval;

    fn fill_gap(&self, _rhs: &EmptyInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<AbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &AbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<EmptiableAbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &EmptiableAbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<AbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &AbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Ok(rhs.clone())
    }
}

impl GapFillable<ClosedAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &ClosedAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<HalfOpenAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &HalfOpenAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<RelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &RelativeBounds) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<EmptiableRelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &EmptiableRelativeBounds) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<RelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &RelativeInterval) -> Result<Self::Output, GapFillError> {
        Ok(rhs.clone())
    }
}

impl GapFillable<ClosedRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &ClosedRelativeInterval) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<HalfOpenRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &HalfOpenRelativeInterval) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<OpenInterval> for EmptyInterval {
    type Output = OpenInterval;

    fn fill_gap(&self, rhs: &OpenInterval) -> Result<Self::Output, GapFillError> {
        Ok(*rhs)
    }
}

impl GapFillable<EmptyInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn fill_gap(&self, rhs: &EmptyInterval) -> Result<Self::Output, GapFillError> {
        Ok(*rhs)
    }
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
///
/// # Errors
///
/// If the given bounds overlap, this method fails with [`GapFillError::Overlap`]
pub fn fill_gap_abs_bounds(a: &AbsoluteBounds, b: &AbsoluteBounds) -> Result<AbsoluteBounds, GapFillError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

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
        return Ok(b.clone());
    };

    fill_gap_abs_bounds_with_emptiable_abs_bounds(a_abs_bounds, b).map(EmptiableAbsoluteBounds::from)
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
///
/// # Errors
///
/// If the given bounds overlap, this method fails with [`GapFillError::Overlap`]
pub fn fill_gap_rel_bounds(a: &RelativeBounds, b: &RelativeBounds) -> Result<RelativeBounds, GapFillError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

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

            Ok(a.grow_end(new_end_bound))
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
pub fn fill_gap_rel_bounds_with_emptiable_rel_bounds(
    a: &RelativeBounds,
    b: &EmptiableRelativeBounds,
) -> Result<RelativeBounds, GapFillError> {
    let EmptiableRelativeBounds::Bound(b_rel_bounds) = b else {
        return Ok(a.clone());
    };

    fill_gap_rel_bounds(a, b_rel_bounds)
}

/// Returns a result that contains a version of `a` that no longer has a strict gap with the given `b`
///
/// # Errors
///
/// If the given bounds overlap, this method fails with [`GapFillError::Overlap`]
pub fn fill_gap_emptiable_rel_bounds(
    a: &EmptiableRelativeBounds,
    b: &EmptiableRelativeBounds,
) -> Result<EmptiableRelativeBounds, GapFillError> {
    let EmptiableRelativeBounds::Bound(a_rel_bounds) = a else {
        return Ok(b.clone());
    };

    fill_gap_rel_bounds_with_emptiable_rel_bounds(a_rel_bounds, b).map(EmptiableRelativeBounds::from)
}

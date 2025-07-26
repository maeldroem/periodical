//! Interval extension

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfOpenAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, RelativeBounds, RelativeEndBound, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};

/// Capacity to extend an interval with another
pub trait Extensible<Rhs = Self> {
    /// Output type
    type Output;

    /// Creates an extended interval from the current one and given one
    ///
    /// Instead of uniting two intervals, this method takes the lowest point of both intervals' lower bound and the
    /// highest point of both intervals' upper bound, then creates an interval that spans those two points.
    ///
    /// Regarding bound inclusivity, for each point we will get the bound inclusivity of the interval from which
    /// the point was taken. If they were equal, we choose the most inclusive bound.
    ///
    /// If both intervals are empty, the method just returns an empty interval.
    ///
    /// If one of the intervals is empty, the method just return a clone of the other non-empty interval.
    #[must_use]
    fn extend(&self, rhs: &Rhs) -> Self::Output;
}

impl<Rhs> Extensible<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        AbsoluteInterval::from(extend_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for ClosedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        AbsoluteInterval::from(extend_abs_bounds_with_emptiable_abs_bounds(
            &self.abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for HalfOpenAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        AbsoluteInterval::from(extend_abs_bounds_with_emptiable_abs_bounds(
            &self.abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Extensible<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        RelativeInterval::from(extend_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for ClosedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        RelativeInterval::from(extend_rel_bounds_with_emptiable_rel_bounds(
            &self.rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for HalfOpenRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        RelativeInterval::from(extend_rel_bounds_with_emptiable_rel_bounds(
            &self.rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        ))
    }
}

impl Extensible<AbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, _rhs: &AbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(*self)
    }
}

impl Extensible<EmptiableAbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, _rhs: &EmptiableAbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(*self)
    }
}

impl Extensible<AbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, _rhs: &AbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(*self)
    }
}

impl Extensible<ClosedAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, _rhs: &ClosedAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(*self)
    }
}

impl Extensible<HalfOpenAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, _rhs: &HalfOpenAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(*self)
    }
}

impl Extensible<RelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn extend(&self, _rhs: &RelativeBounds) -> Self::Output {
        RelativeInterval::from(*self)
    }
}

impl Extensible<EmptiableRelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn extend(&self, _rhs: &EmptiableRelativeBounds) -> Self::Output {
        RelativeInterval::from(*self)
    }
}

impl Extensible<RelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn extend(&self, _rhs: &RelativeInterval) -> Self::Output {
        RelativeInterval::from(*self)
    }
}

impl Extensible<ClosedRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn extend(&self, _rhs: &ClosedRelativeInterval) -> Self::Output {
        RelativeInterval::from(*self)
    }
}

impl Extensible<HalfOpenRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn extend(&self, _rhs: &HalfOpenRelativeInterval) -> Self::Output {
        RelativeInterval::from(*self)
    }
}

impl Extensible<OpenInterval> for OpenInterval {
    type Output = OpenInterval;

    fn extend(&self, _rhs: &OpenInterval) -> Self::Output {
        *self
    }
}

impl Extensible<EmptyInterval> for OpenInterval {
    type Output = OpenInterval;

    fn extend(&self, _rhs: &EmptyInterval) -> Self::Output {
        *self
    }
}

impl Extensible<AbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &AbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Extensible<EmptiableAbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &EmptiableAbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Extensible<AbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &AbsoluteInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<ClosedAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &ClosedAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Extensible<HalfOpenAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &HalfOpenAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Extensible<RelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn extend(&self, rhs: &RelativeBounds) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Extensible<EmptiableRelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn extend(&self, rhs: &EmptiableRelativeBounds) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Extensible<RelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn extend(&self, rhs: &RelativeInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<ClosedRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn extend(&self, rhs: &ClosedRelativeInterval) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Extensible<HalfOpenRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn extend(&self, rhs: &HalfOpenRelativeInterval) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Extensible<OpenInterval> for EmptyInterval {
    type Output = OpenInterval;

    fn extend(&self, rhs: &OpenInterval) -> Self::Output {
        *rhs
    }
}

impl Extensible<EmptyInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn extend(&self, _rhs: &EmptyInterval) -> Self::Output {
        *self
    }
}

/// Extends two [`AbsoluteBounds`]
#[must_use]
pub fn extend_abs_bounds(og_bounds: &AbsoluteBounds, other_bounds: &AbsoluteBounds) -> AbsoluteBounds {
    let new_start_bound = match (og_bounds.abs_start(), other_bounds.abs_start()) {
        (bound @ AbsoluteStartBound::InfinitePast, _) | (_, bound @ AbsoluteStartBound::InfinitePast) => bound,
        (og_bound @ AbsoluteStartBound::Finite(..), other_bound @ AbsoluteStartBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    let new_end_bound = match (og_bounds.abs_end(), other_bounds.abs_end()) {
        (bound @ AbsoluteEndBound::InfiniteFuture, _) | (_, bound @ AbsoluteEndBound::InfiniteFuture) => bound,
        (og_bound @ AbsoluteEndBound::Finite(..), other_bound @ AbsoluteEndBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    AbsoluteBounds::new(new_start_bound, new_end_bound)
}

/// Extends an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn extend_abs_bounds_with_emptiable_abs_bounds(
    og_bounds: &AbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> AbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    extend_abs_bounds(og_bounds, other_non_empty_bounds)
}

/// Extends two [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn extend_emptiable_abs_bounds(
    og_bounds: &EmptiableAbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> EmptiableAbsoluteBounds {
    match (og_bounds, other_bounds) {
        (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Empty) => EmptiableAbsoluteBounds::Empty,
        (EmptiableAbsoluteBounds::Empty, bound @ EmptiableAbsoluteBounds::Bound(..))
        | (bound @ EmptiableAbsoluteBounds::Bound(..), EmptiableAbsoluteBounds::Empty) => bound.clone(),
        (EmptiableAbsoluteBounds::Bound(og_bounds), EmptiableAbsoluteBounds::Bound(other_bounds)) => {
            EmptiableAbsoluteBounds::Bound(og_bounds.extend(other_bounds))
        },
    }
}

/// Extends two [`RelativeBounds`]
#[must_use]
pub fn extend_rel_bounds(og_bounds: &RelativeBounds, other_bounds: &RelativeBounds) -> RelativeBounds {
    let new_start_bound = match (og_bounds.rel_start(), other_bounds.rel_start()) {
        (bound @ RelativeStartBound::InfinitePast, _) | (_, bound @ RelativeStartBound::InfinitePast) => bound,
        (og_bound @ RelativeStartBound::Finite(..), other_bound @ RelativeStartBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    let new_end_bound = match (og_bounds.rel_end(), other_bounds.rel_end()) {
        (bound @ RelativeEndBound::InfiniteFuture, _) | (_, bound @ RelativeEndBound::InfiniteFuture) => bound,
        (og_bound @ RelativeEndBound::Finite(..), other_bound @ RelativeEndBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    RelativeBounds::new(new_start_bound, new_end_bound)
}

/// Extends an [`RelativeBounds`] with an [`EmptiableRelativeBounds`]
#[must_use]
pub fn extend_rel_bounds_with_emptiable_rel_bounds(
    og_bounds: &RelativeBounds,
    other_bounds: &EmptiableRelativeBounds,
) -> RelativeBounds {
    let EmptiableRelativeBounds::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    extend_rel_bounds(og_bounds, other_non_empty_bounds)
}

/// Extends two [`EmptiableRelativeBounds`]
#[must_use]
pub fn extend_emptiable_rel_bounds(
    og_bounds: &EmptiableRelativeBounds,
    other_bounds: &EmptiableRelativeBounds,
) -> EmptiableRelativeBounds {
    match (og_bounds, other_bounds) {
        (EmptiableRelativeBounds::Empty, EmptiableRelativeBounds::Empty) => EmptiableRelativeBounds::Empty,
        (EmptiableRelativeBounds::Empty, bound @ EmptiableRelativeBounds::Bound(..))
        | (bound @ EmptiableRelativeBounds::Bound(..), EmptiableRelativeBounds::Empty) => bound.clone(),
        (EmptiableRelativeBounds::Bound(og_bounds), EmptiableRelativeBounds::Bound(other_bounds)) => {
            EmptiableRelativeBounds::Bound(og_bounds.extend(other_bounds))
        },
    }
}

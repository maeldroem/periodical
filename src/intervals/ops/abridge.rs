//! Interval abridging

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfOpenAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds, swap_absolute_bounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, HasEmptiableRelativeBounds, HasRelativeBounds, RelativeBounds,
    RelativeEndBound, RelativeStartBound, swap_relative_bounds,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};

/// Capacity to abridge an interval with another, think of it as the inverse of [`Extensible`]
pub trait Abridgable<Rhs = Self> {
    /// Output type
    type Output;

    /// Creates an abridged interval from the current one and given one
    ///
    /// Instead of intersecting two intervals, this method takes the highest point of both intervals' lower bound
    /// and the lowest point of both intervals' upper bound, then create an interval that spans those two points.
    ///
    /// Regarding bound inclusivity, for each point we will get the bound inclusivity of the interval from which
    /// the point was taken. If they were equal, we choose the most exclusive bound.
    ///
    /// If the intervals don't strictly overlap, the method returns the interval that spans the gap between the two
    /// intervals. This sort of gap interval will have opposite bound inclusivities from the points it was created from.
    ///
    /// If both intervals are empty, the method just returns an empty interval.
    ///
    /// If one of the intervals is empty, the method just returns a clone of the other non-empty interval.
    #[must_use]
    fn abridge(&self, rhs: &Rhs) -> Self::Output;
}

impl<Rhs> Abridgable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::from(self.emptiable_abs_bounds().abridge(&rhs.emptiable_abs_bounds()))
    }
}

impl<Rhs> Abridgable<Rhs> for ClosedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        AbsoluteInterval::from(abridge_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        ))
    }
}

impl<Rhs> Abridgable<Rhs> for HalfOpenAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        AbsoluteInterval::from(abridge_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        ))
    }
}

impl<Rhs> Abridgable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Abridgable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        RelativeInterval::from(abridge_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        ))
    }
}

impl<Rhs> Abridgable<Rhs> for ClosedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        RelativeInterval::from(abridge_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        ))
    }
}

impl<Rhs> Abridgable<Rhs> for HalfOpenRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        RelativeInterval::from(abridge_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        ))
    }
}

impl Abridgable<AbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &AbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<EmptiableAbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &EmptiableAbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<AbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &AbsoluteInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Abridgable<ClosedAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &ClosedAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<HalfOpenAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &HalfOpenAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<RelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &RelativeBounds) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<EmptiableRelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &EmptiableRelativeBounds) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<RelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &RelativeInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Abridgable<ClosedRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &ClosedRelativeInterval) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<HalfOpenRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &HalfOpenRelativeInterval) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<OpenInterval> for OpenInterval {
    type Output = OpenInterval;

    fn abridge(&self, _rhs: &OpenInterval) -> Self::Output {
        self.clone()
    }
}

impl Abridgable<EmptyInterval> for OpenInterval {
    type Output = EmptyInterval;

    fn abridge(&self, rhs: &EmptyInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Abridgable<AbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &AbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<EmptiableAbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &EmptiableAbsoluteBounds) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<AbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &AbsoluteInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Abridgable<ClosedAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &ClosedAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<HalfOpenAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn abridge(&self, rhs: &HalfOpenAbsoluteInterval) -> Self::Output {
        AbsoluteInterval::from(rhs.clone())
    }
}

impl Abridgable<RelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &RelativeBounds) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<EmptiableRelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &EmptiableRelativeBounds) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<RelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &RelativeInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Abridgable<ClosedRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &ClosedRelativeInterval) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<HalfOpenRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn abridge(&self, rhs: &HalfOpenRelativeInterval) -> Self::Output {
        RelativeInterval::from(rhs.clone())
    }
}

impl Abridgable<OpenInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn abridge(&self, _rhs: &OpenInterval) -> Self::Output {
        self.clone()
    }
}

impl Abridgable<EmptyInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn abridge(&self, _rhs: &EmptyInterval) -> Self::Output {
        self.clone()
    }
}

/// Abridges two [`AbsoluteBounds`]
#[must_use]
pub fn abridge_abs_bounds(og_bounds: &AbsoluteBounds, other_bounds: &AbsoluteBounds) -> AbsoluteBounds {
    let mut highest_start = match (og_bounds.abs_start(), other_bounds.abs_start()) {
        (AbsoluteStartBound::InfinitePast, bound @ AbsoluteStartBound::Finite(..))
        | (
            bound @ (AbsoluteStartBound::Finite(..) | AbsoluteStartBound::InfinitePast),
            AbsoluteStartBound::InfinitePast,
        ) => bound,
        (og_bound @ AbsoluteStartBound::Finite(..), other_bound @ AbsoluteStartBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    let mut lowest_end = match (og_bounds.abs_end(), other_bounds.abs_end()) {
        (AbsoluteEndBound::InfiniteFuture, bound @ AbsoluteEndBound::Finite(..))
        | (
            bound @ (AbsoluteEndBound::Finite(..) | AbsoluteEndBound::InfiniteFuture),
            AbsoluteEndBound::InfiniteFuture,
        ) => bound,
        (og_bound @ AbsoluteEndBound::Finite(..), other_bound @ AbsoluteEndBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    if highest_start > lowest_end {
        swap_absolute_bounds(&mut highest_start, &mut lowest_end);

        if let AbsoluteStartBound::Finite(ref mut finite_start) = highest_start {
            finite_start.set_inclusivity(finite_start.inclusivity().opposite());
        }

        if let AbsoluteEndBound::Finite(ref mut finite_end) = lowest_end {
            finite_end.set_inclusivity(finite_end.inclusivity().opposite());
        }
    }

    AbsoluteBounds::unchecked_new(highest_start, lowest_end)
}

/// Abridges an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn abridge_abs_bounds_with_emptiable_abs_bounds(
    og_bounds: &AbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> AbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    abridge_abs_bounds(og_bounds, other_non_empty_bounds)
}

/// Abridges two [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn abridge_emptiable_abs_bounds(
    og_bounds: &EmptiableAbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> EmptiableAbsoluteBounds {
    match (og_bounds, other_bounds) {
        (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Empty) => EmptiableAbsoluteBounds::Empty,
        (EmptiableAbsoluteBounds::Empty, bound @ EmptiableAbsoluteBounds::Bound(..))
        | (bound @ EmptiableAbsoluteBounds::Bound(..), EmptiableAbsoluteBounds::Empty) => bound.clone(),
        (EmptiableAbsoluteBounds::Bound(og_bounds), EmptiableAbsoluteBounds::Bound(other_bounds)) => {
            EmptiableAbsoluteBounds::Bound(og_bounds.abridge(other_bounds))
        },
    }
}

/// Abridges two [`RelativeBounds`]
#[must_use]
pub fn abridge_rel_bounds(og_bounds: &RelativeBounds, other_bounds: &RelativeBounds) -> RelativeBounds {
    let mut highest_start = match (og_bounds.rel_start(), other_bounds.rel_start()) {
        (RelativeStartBound::InfinitePast, bound @ RelativeStartBound::Finite(..))
        | (
            bound @ (RelativeStartBound::Finite(..) | RelativeStartBound::InfinitePast),
            RelativeStartBound::InfinitePast,
        ) => bound,
        (og_bound @ RelativeStartBound::Finite(..), other_bound @ RelativeStartBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    let mut lowest_end = match (og_bounds.rel_end(), other_bounds.rel_end()) {
        (RelativeEndBound::InfiniteFuture, bound @ RelativeEndBound::Finite(..))
        | (
            bound @ (RelativeEndBound::Finite(..) | RelativeEndBound::InfiniteFuture),
            RelativeEndBound::InfiniteFuture,
        ) => bound,
        (og_bound @ RelativeEndBound::Finite(..), other_bound @ RelativeEndBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    if highest_start > lowest_end {
        swap_relative_bounds(&mut highest_start, &mut lowest_end);

        if let RelativeStartBound::Finite(ref mut finite_start) = highest_start {
            finite_start.set_inclusivity(finite_start.inclusivity().opposite());
        }

        if let RelativeEndBound::Finite(ref mut finite_end) = lowest_end {
            finite_end.set_inclusivity(finite_end.inclusivity().opposite());
        }
    }

    RelativeBounds::unchecked_new(highest_start, lowest_end)
}

/// Abridges an [`RelativeBounds`] with an [`EmptiableRelativeBounds`]
#[must_use]
pub fn abridge_rel_bounds_with_emptiable_rel_bounds(
    og_bounds: &RelativeBounds,
    other_bounds: &EmptiableRelativeBounds,
) -> RelativeBounds {
    let EmptiableRelativeBounds::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    abridge_rel_bounds(og_bounds, other_non_empty_bounds)
}

/// Abridges two [`EmptiableRelativeBounds`]
#[must_use]
pub fn abridge_emptiable_rel_bounds(
    og_bounds: &EmptiableRelativeBounds,
    other_bounds: &EmptiableRelativeBounds,
) -> EmptiableRelativeBounds {
    match (og_bounds, other_bounds) {
        (EmptiableRelativeBounds::Empty, EmptiableRelativeBounds::Empty) => EmptiableRelativeBounds::Empty,
        (EmptiableRelativeBounds::Empty, bound @ EmptiableRelativeBounds::Bound(..))
        | (bound @ EmptiableRelativeBounds::Bound(..), EmptiableRelativeBounds::Empty) => bound.clone(),
        (EmptiableRelativeBounds::Bound(og_bounds), EmptiableRelativeBounds::Bound(other_bounds)) => {
            EmptiableRelativeBounds::Bound(og_bounds.abridge(other_bounds))
        },
    }
}

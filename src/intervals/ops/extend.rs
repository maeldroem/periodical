//! Interval extension

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds, HasAbsoluteBounds,
    HasEmptiableAbsoluteBounds,
};

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
        AbsoluteInterval::from(self.emptiable_abs_bounds().extend(&rhs.emptiable_abs_bounds()))
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

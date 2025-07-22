//! Interval growth

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds, HasAbsoluteBounds,
    HasEmptiableAbsoluteBounds,
};

/// Capacity to grow an interval up to a given bound
pub trait Growable {
    /// Output type
    type Output;

    /// Grows the start of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the start bound is more in the past than the original one.
    /// Of course, it only happens if the passed new start bound is actually more in the past than the original one.
    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output;

    /// Grows the end of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the end bound is more in the future than the original one.
    /// Of course, it only happens if the passed new end bound is actually more in the future than the original one.
    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output;
}

impl Growable for AbsoluteBounds {
    type Output = Self;

    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output {
        grow_start_abs_bounds(self, at)
    }

    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output {
        grow_end_abs_bounds(self, at)
    }
}

impl Growable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output {
        grow_start_emptiable_abs_bounds(self, at)
    }

    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output {
        grow_end_emptiable_abs_bounds(self, at)
    }
}

impl Growable for AbsoluteInterval {
    type Output = Self;

    fn grow_start(&self, at: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(grow_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }

    fn grow_end(&self, at: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(grow_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }
}

/// Makes the start of the passed [`AbsoluteBounds`] grow up to the given bound if it is lesser than the original
#[must_use]
pub fn grow_start_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteStartBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.abs_start().min(at));
    new_bounds
}

/// Makes the end of the passed [`AbsoluteBounds`] grow up to the given bound if it is greater than the original
#[must_use]
pub fn grow_end_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteEndBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.abs_end().max(at));
    new_bounds
}

/// Makes the start of the passed [`EmptiableAbsoluteBounds`] grow up to the given bound if it is lesser than the original
#[must_use]
pub fn grow_start_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteStartBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(grow_start_abs_bounds(bounds, at))
}

/// Makes the end of the passed [`EmptiableAbsoluteBounds`] grow up to the given bound if it is greater than the original
#[must_use]
pub fn grow_end_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteEndBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(grow_end_abs_bounds(bounds, at))
}

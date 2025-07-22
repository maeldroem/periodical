//! Interval shrinking

use std::cmp::Ordering;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds, HasAbsoluteBounds,
    HasEmptiableAbsoluteBounds,
};

/// Capacity to shrink an interval up to a given time
pub trait Shrinkable {
    /// Output type
    type Output;

    /// Shrinks the start bound up to the given time
    ///
    /// If the given bound is already after the interval's end,
    /// nothing happens and it just returns a clone of the interval
    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output;

    /// Shrinks the end bound up to the given time
    ///
    /// If the given bound is already before the interval's start,
    /// nothing happens and it just returns a clone of the interval
    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output;
}

impl Shrinkable for AbsoluteBounds {
    type Output = Self;

    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output {
        shrink_start_abs_bounds(self, at)
    }

    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output {
        shrink_end_abs_bounds(self, at)
    }
}

impl Shrinkable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output {
        shrink_start_emptiable_abs_bounds(self, at)
    }

    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output {
        shrink_end_emptiable_abs_bounds(self, at)
    }
}

impl Shrinkable for AbsoluteInterval {
    type Output = Self;

    fn shrink_start(&self, at: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }

    fn shrink_end(&self, at: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at))
    }
}

/// Shrinks the start bound of the given [`AbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_start_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteStartBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    let max_start = new_bounds.abs_start().max(at);

    match max_start.partial_cmp(&new_bounds.abs_end()) {
        // Would create an invalid interval, so we just return a clone of the original bounds
        None | Some(Ordering::Greater) => {},
        Some(Ordering::Equal | Ordering::Less) => {
            new_bounds.set_start(max_start);
        },
    }

    new_bounds
}

/// Shrinks the end bound of the given [`AbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_end_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteEndBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    let min_end = new_bounds.abs_end().min(at);

    match new_bounds.abs_start().partial_cmp(&min_end) {
        // Would create an invalid interval, so we just return a clone of the original bounds
        None | Some(Ordering::Greater) => {},
        Some(Ordering::Equal | Ordering::Less) => {
            new_bounds.set_end(min_end);
        },
    }

    new_bounds
}

/// Shrinks the start bound of the given [`EmptiableAbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_start_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteStartBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(shrink_start_abs_bounds(bounds, at))
}

/// Shrinks the end bound of the given [`EmptiableAbsoluteBounds`] to the given time
#[must_use]
pub fn shrink_end_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
    at: AbsoluteEndBound,
) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBounds::from(shrink_end_abs_bounds(bounds, at))
}

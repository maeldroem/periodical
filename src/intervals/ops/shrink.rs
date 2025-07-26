//! Interval shrinking

use std::cmp::Ordering;

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

/// Capacity to shrink an interval up to a given time
///
/// The generic type parameter `P` corresponds to the position type, usually a `*StartBound`.
pub trait ShrinkableStartBound<P> {
    /// Output type
    type Output;

    /// Shrinks the start bound up to the given time
    ///
    /// If the given bound is already after the interval's end,
    /// nothing happens and it just returns a clone of the interval
    fn shrink_start(&self, position: P) -> Self::Output;
}

/// Capacity to shrink an interval up to a given time
///
/// The generic type parameter `P` corresponds to the position type, usually a `*EndBound`.
pub trait ShrinkableEndBound<P> {
    /// Output type
    type Output;

    /// Shrinks the end bound up to the given time
    ///
    /// If the given bound is already before the interval's start,
    /// nothing happens and it just returns a clone of the interval
    fn shrink_end(&self, position: P) -> Self::Output;
}

impl ShrinkableStartBound<AbsoluteStartBound> for AbsoluteBounds {
    type Output = Self;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        shrink_start_abs_bounds(self, position)
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for AbsoluteBounds {
    type Output = Self;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        shrink_end_abs_bounds(self, position)
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for EmptiableAbsoluteBounds {
    type Output = Self;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        shrink_start_emptiable_abs_bounds(self, position)
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for EmptiableAbsoluteBounds {
    type Output = Self;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        shrink_end_emptiable_abs_bounds(self, position)
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for AbsoluteInterval {
    type Output = Self;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for AbsoluteInterval {
    type Output = Self;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for ClosedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for ClosedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for HalfOpenAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for HalfOpenAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for RelativeBounds {
    type Output = Self;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        shrink_start_rel_bounds(self, position)
    }
}

impl ShrinkableEndBound<RelativeEndBound> for RelativeBounds {
    type Output = Self;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        shrink_end_rel_bounds(self, position)
    }
}

impl ShrinkableStartBound<RelativeStartBound> for EmptiableRelativeBounds {
    type Output = Self;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        shrink_start_emptiable_rel_bounds(self, position)
    }
}

impl ShrinkableEndBound<RelativeEndBound> for EmptiableRelativeBounds {
    type Output = Self;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        shrink_end_emptiable_rel_bounds(self, position)
    }
}

impl ShrinkableStartBound<RelativeStartBound> for RelativeInterval {
    type Output = Self;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(shrink_start_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for RelativeInterval {
    type Output = Self;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(shrink_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for ClosedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(shrink_start_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for ClosedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(shrink_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for HalfOpenRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(shrink_start_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for HalfOpenRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(shrink_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for OpenInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for OpenInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for OpenInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(shrink_start_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for OpenInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(shrink_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_start(&self, _position: AbsoluteStartBound) -> Self::Output {
        *self
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_end(&self, _position: AbsoluteEndBound) -> Self::Output {
        *self
    }
}

impl ShrinkableStartBound<RelativeStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_start(&self, _position: RelativeStartBound) -> Self::Output {
        *self
    }
}

impl ShrinkableEndBound<RelativeEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_end(&self, _position: RelativeEndBound) -> Self::Output {
        *self
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

/// Shrinks the start bound of the given [`RelativeBounds`] to the given time
#[must_use]
pub fn shrink_start_rel_bounds(bounds: &RelativeBounds, at: RelativeStartBound) -> RelativeBounds {
    let mut new_bounds = bounds.clone();
    let max_start = new_bounds.rel_start().max(at);

    match max_start.partial_cmp(&new_bounds.rel_end()) {
        // Would create an invalid interval, so we just return a clone of the original bounds
        None | Some(Ordering::Greater) => {},
        Some(Ordering::Equal | Ordering::Less) => {
            new_bounds.set_start(max_start);
        },
    }

    new_bounds
}

/// Shrinks the start bound of the given [`EmptiableRelativeBounds`] to the given time
#[must_use]
pub fn shrink_start_emptiable_rel_bounds(
    emptiable_bounds: &EmptiableRelativeBounds,
    at: RelativeStartBound,
) -> EmptiableRelativeBounds {
    let EmptiableRelativeBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBounds::from(shrink_start_rel_bounds(bounds, at))
}

/// Shrinks the end bound of the given [`RelativeBounds`] to the given time
#[must_use]
pub fn shrink_end_rel_bounds(bounds: &RelativeBounds, at: RelativeEndBound) -> RelativeBounds {
    let mut new_bounds = bounds.clone();
    let min_end = new_bounds.rel_end().min(at);

    match new_bounds.rel_start().partial_cmp(&min_end) {
        // Would create an invalid interval, so we just return a clone of the original bounds
        None | Some(Ordering::Greater) => {},
        Some(Ordering::Equal | Ordering::Less) => {
            new_bounds.set_end(min_end);
        },
    }

    new_bounds
}

/// Shrinks the end bound of the given [`EmptiableRelativeBounds`] to the given time
#[must_use]
pub fn shrink_end_emptiable_rel_bounds(
    emptiable_bounds: &EmptiableRelativeBounds,
    at: RelativeEndBound,
) -> EmptiableRelativeBounds {
    let EmptiableRelativeBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBounds::from(shrink_end_rel_bounds(bounds, at))
}

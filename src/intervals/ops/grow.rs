//! Interval growth

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

/// Capacity to grow an interval's start bound up to a given new start bound
///
/// The generic type parameter `P` corresponds to the position type, usually a `*StartBound`.
pub trait GrowableStartBound<P> {
    /// Output type
    type Output;

    /// Grows the start of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the start bound is more in the past than the original one.
    /// Of course, it only happens if the passed new start bound is actually more in the past than the original one.
    fn grow_start(&self, position: P) -> Self::Output;
}

/// Capacity to grow an interval's end bound up to a given new end bound
///
/// The generic type parameter `P` corresponds to the position type, usually a `*EndBound`.
pub trait GrowableEndBound<P> {
    /// Output type
    type Output;

    /// Grows the end of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the end bound is more in the future than the original one.
    /// Of course, it only happens if the passed new end bound is actually more in the future than the original one.
    fn grow_end(&self, position: P) -> Self::Output;
}

impl GrowableStartBound<AbsoluteStartBound> for AbsoluteBounds {
    type Output = Self;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        grow_start_abs_bounds(self, position)
    }
}

impl GrowableEndBound<AbsoluteEndBound> for AbsoluteBounds {
    type Output = Self;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        grow_end_abs_bounds(self, position)
    }
}

impl GrowableStartBound<AbsoluteStartBound> for EmptiableAbsoluteBounds {
    type Output = Self;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        grow_start_emptiable_abs_bounds(self, position)
    }
}

impl GrowableEndBound<AbsoluteEndBound> for EmptiableAbsoluteBounds {
    type Output = Self;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        grow_end_emptiable_abs_bounds(self, position)
    }
}

impl GrowableStartBound<AbsoluteStartBound> for AbsoluteInterval {
    type Output = Self;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(grow_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for AbsoluteInterval {
    type Output = Self;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(grow_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for ClosedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(grow_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for ClosedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(grow_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for HalfOpenAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(grow_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for HalfOpenAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(grow_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for RelativeBounds {
    type Output = Self;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        grow_start_rel_bounds(self, position)
    }
}

impl GrowableEndBound<RelativeEndBound> for RelativeBounds {
    type Output = Self;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        grow_end_rel_bounds(self, position)
    }
}

impl GrowableStartBound<RelativeStartBound> for EmptiableRelativeBounds {
    type Output = Self;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        grow_start_emptiable_rel_bounds(self, position)
    }
}

impl GrowableEndBound<RelativeEndBound> for EmptiableRelativeBounds {
    type Output = Self;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        grow_end_emptiable_rel_bounds(self, position)
    }
}

impl GrowableStartBound<RelativeStartBound> for RelativeInterval {
    type Output = Self;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(grow_start_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for RelativeInterval {
    type Output = Self;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(grow_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for ClosedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(grow_start_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for ClosedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(grow_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for HalfOpenRelativeInterval {
    type Output = RelativeInterval;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(grow_start_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for HalfOpenRelativeInterval {
    type Output = RelativeInterval;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(grow_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for OpenInterval {
    type Output = OpenInterval;

    fn grow_start(&self, _position: AbsoluteStartBound) -> Self::Output {
        self.clone()
    }
}

impl GrowableEndBound<AbsoluteEndBound> for OpenInterval {
    type Output = OpenInterval;

    fn grow_end(&self, _position: AbsoluteEndBound) -> Self::Output {
        self.clone()
    }
}

impl GrowableStartBound<RelativeStartBound> for OpenInterval {
    type Output = OpenInterval;

    fn grow_start(&self, _position: RelativeStartBound) -> Self::Output {
        self.clone()
    }
}

impl GrowableEndBound<RelativeEndBound> for OpenInterval {
    type Output = OpenInterval;

    fn grow_end(&self, _position: RelativeEndBound) -> Self::Output {
        self.clone()
    }
}

impl GrowableStartBound<AbsoluteStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_start(&self, _position: AbsoluteStartBound) -> Self::Output {
        self.clone()
    }
}

impl GrowableEndBound<AbsoluteEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_end(&self, _position: AbsoluteEndBound) -> Self::Output {
        self.clone()
    }
}

impl GrowableStartBound<RelativeStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_start(&self, _position: RelativeStartBound) -> Self::Output {
        self.clone()
    }
}

impl GrowableEndBound<RelativeEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_end(&self, _position: RelativeEndBound) -> Self::Output {
        self.clone()
    }
}

/// Makes the start of the passed [`AbsoluteBounds`] grow up to the given bound if it is lesser than the original
#[must_use]
pub fn grow_start_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteStartBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.abs_start().min(at));
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

/// Makes the end of the passed [`AbsoluteBounds`] grow up to the given bound if it is greater than the original
#[must_use]
pub fn grow_end_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteEndBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.abs_end().max(at));
    new_bounds
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

/// Makes the start of the passed [`RelativeBounds`] grow up to the given bound if it is lesser than the original
#[must_use]
pub fn grow_start_rel_bounds(bounds: &RelativeBounds, at: RelativeStartBound) -> RelativeBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.rel_start().min(at));
    new_bounds
}

/// Makes the start of the passed [`EmptiableRelativeBounds`] grow up to the given bound if it is lesser than the original
#[must_use]
pub fn grow_start_emptiable_rel_bounds(
    emptiable_bounds: &EmptiableRelativeBounds,
    at: RelativeStartBound,
) -> EmptiableRelativeBounds {
    let EmptiableRelativeBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBounds::from(grow_start_rel_bounds(bounds, at))
}

/// Makes the end of the passed [`RelativeBounds`] grow up to the given bound if it is greater than the original
#[must_use]
pub fn grow_end_rel_bounds(bounds: &RelativeBounds, at: RelativeEndBound) -> RelativeBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.rel_end().max(at));
    new_bounds
}

/// Makes the end of the passed [`EmptiableRelativeBounds`] grow up to the given bound if it is greater than the original
#[must_use]
pub fn grow_end_emptiable_rel_bounds(
    emptiable_bounds: &EmptiableRelativeBounds,
    at: RelativeEndBound,
) -> EmptiableRelativeBounds {
    let EmptiableRelativeBounds::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBounds::from(grow_end_rel_bounds(bounds, at))
}

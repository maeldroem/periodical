//! Continuation, both past and future, of intervals

use super::prelude::*;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{
    AbsoluteBounds, AbsoluteInterval, BoundedAbsoluteInterval, BoundedRelativeInterval, EmptiableAbsoluteBounds,
    EmptiableRelativeBounds, HalfBoundedAbsoluteInterval, HalfBoundedRelativeInterval, RelativeInterval,
};

/// Capacity to get the past and future continuation of an interval
pub trait Continuable {
    /// Output type
    type Output;

    /// Returns the past continuation of the interval
    #[must_use]
    fn past_continuation(&self) -> Self::Output;

    /// Returns the future continuation of the interval
    #[must_use]
    fn future_continuation(&self) -> Self::Output;
}

impl Continuable for AbsoluteBounds {
    type Output = EmptiableAbsoluteBounds;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_abs_bounds(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_abs_bounds(self)
    }
}

impl Continuable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_emptiable_abs_bounds(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_emptiable_abs_bounds(self)
    }
}

impl Continuable for AbsoluteInterval {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        AbsoluteInterval::from(past_continuation_emptiable_abs_bounds(&self.emptiable_abs_bounds()))
    }

    fn future_continuation(&self) -> Self::Output {
        AbsoluteInterval::from(future_continuation_emptiable_abs_bounds(&self.emptiable_abs_bounds()))
    }
}

impl Continuable for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn past_continuation(&self) -> Self::Output {
        AbsoluteInterval::from(past_continuation_abs_bounds(&self.abs_bounds()))
    }

    fn future_continuation(&self) -> Self::Output {
        AbsoluteInterval::from(future_continuation_abs_bounds(&self.abs_bounds()))
    }
}

impl Continuable for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn past_continuation(&self) -> Self::Output {
        AbsoluteInterval::from(past_continuation_abs_bounds(&self.abs_bounds()))
    }

    fn future_continuation(&self) -> Self::Output {
        AbsoluteInterval::from(future_continuation_abs_bounds(&self.abs_bounds()))
    }
}

impl Continuable for RelativeBounds {
    type Output = EmptiableRelativeBounds;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_rel_bounds(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_rel_bounds(self)
    }
}

impl Continuable for EmptiableRelativeBounds {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_emptiable_rel_bounds(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_emptiable_rel_bounds(self)
    }
}

impl Continuable for RelativeInterval {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        RelativeInterval::from(past_continuation_emptiable_rel_bounds(&self.emptiable_rel_bounds()))
    }

    fn future_continuation(&self) -> Self::Output {
        RelativeInterval::from(future_continuation_emptiable_rel_bounds(&self.emptiable_rel_bounds()))
    }
}

impl Continuable for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn past_continuation(&self) -> Self::Output {
        RelativeInterval::from(past_continuation_rel_bounds(&self.rel_bounds()))
    }

    fn future_continuation(&self) -> Self::Output {
        RelativeInterval::from(future_continuation_rel_bounds(&self.rel_bounds()))
    }
}

impl Continuable for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn past_continuation(&self) -> Self::Output {
        RelativeInterval::from(past_continuation_rel_bounds(&self.rel_bounds()))
    }

    fn future_continuation(&self) -> Self::Output {
        RelativeInterval::from(future_continuation_rel_bounds(&self.rel_bounds()))
    }
}

impl Continuable for UnboundedInterval {
    type Output = EmptyInterval;

    fn past_continuation(&self) -> Self::Output {
        EmptyInterval
    }

    fn future_continuation(&self) -> Self::Output {
        EmptyInterval
    }
}

impl Continuable for EmptyInterval {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        *self
    }

    fn future_continuation(&self) -> Self::Output {
        *self
    }
}

/// Returns the past continuation of the given [`AbsoluteBounds`]
#[must_use]
pub fn past_continuation_abs_bounds(bounds: &AbsoluteBounds) -> EmptiableAbsoluteBounds {
    match bounds.abs_start() {
        AbsoluteStartBound::InfinitePast => EmptiableAbsoluteBounds::Empty,
        AbsoluteStartBound::Finite(finite) => EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                finite.time(),
                finite.inclusivity().opposite(),
            )),
        )),
    }
}

/// Returns the future continuation of the given [`AbsoluteBounds`]
#[must_use]
pub fn future_continuation_abs_bounds(bounds: &AbsoluteBounds) -> EmptiableAbsoluteBounds {
    match bounds.abs_end() {
        AbsoluteEndBound::InfiniteFuture => EmptiableAbsoluteBounds::Empty,
        AbsoluteEndBound::Finite(finite) => EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                finite.time(),
                finite.inclusivity().opposite(),
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
    }
}

/// Returns the past continuation of the given [`AbsoluteBounds`]
#[must_use]
pub fn past_continuation_emptiable_abs_bounds(bounds: &EmptiableAbsoluteBounds) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = bounds else {
        return EmptiableAbsoluteBounds::Empty;
    };

    past_continuation_abs_bounds(bounds)
}

/// Returns the future continuation of the given [`AbsoluteBounds`]
#[must_use]
pub fn future_continuation_emptiable_abs_bounds(bounds: &EmptiableAbsoluteBounds) -> EmptiableAbsoluteBounds {
    let EmptiableAbsoluteBounds::Bound(bounds) = bounds else {
        return EmptiableAbsoluteBounds::Empty;
    };

    future_continuation_abs_bounds(bounds)
}

/// Returns the past continuation of the given [`RelativeBounds`]
#[must_use]
pub fn past_continuation_rel_bounds(bounds: &RelativeBounds) -> EmptiableRelativeBounds {
    match bounds.rel_start() {
        RelativeStartBound::InfinitePast => EmptiableRelativeBounds::Empty,
        RelativeStartBound::Finite(finite) => EmptiableRelativeBounds::from(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                finite.offset(),
                finite.inclusivity().opposite(),
            )),
        )),
    }
}

/// Returns the future continuation of the given [`RelativeBounds`]
#[must_use]
pub fn future_continuation_rel_bounds(bounds: &RelativeBounds) -> EmptiableRelativeBounds {
    match bounds.rel_end() {
        RelativeEndBound::InfiniteFuture => EmptiableRelativeBounds::Empty,
        RelativeEndBound::Finite(finite) => EmptiableRelativeBounds::from(RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                finite.offset(),
                finite.inclusivity().opposite(),
            )),
            RelativeEndBound::InfiniteFuture,
        )),
    }
}

/// Returns the past continuation of the given [`RelativeBounds`]
#[must_use]
pub fn past_continuation_emptiable_rel_bounds(bounds: &EmptiableRelativeBounds) -> EmptiableRelativeBounds {
    let EmptiableRelativeBounds::Bound(bounds) = bounds else {
        return EmptiableRelativeBounds::Empty;
    };

    past_continuation_rel_bounds(bounds)
}

/// Returns the future continuation of the given [`RelativeBounds`]
#[must_use]
pub fn future_continuation_emptiable_rel_bounds(bounds: &EmptiableRelativeBounds) -> EmptiableRelativeBounds {
    let EmptiableRelativeBounds::Bound(bounds) = bounds else {
        return EmptiableRelativeBounds::Empty;
    };

    future_continuation_rel_bounds(bounds)
}

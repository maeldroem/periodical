//! Interval complement

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfOpenAbsoluteInterval, HasEmptiableAbsoluteBounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, RelativeBounds, RelativeEndBound, RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{AbsoluteInterval, ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};
use crate::ops::ComplementResult;

/// Capacity to get the complement of an interval
pub trait Complementable {
    /// Output type
    type Output;

    /// Returns the complement
    fn complement(&self) -> ComplementResult<Self::Output>;
}

impl Complementable for AbsoluteBounds {
    type Output = EmptiableAbsoluteBounds;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_abs_bounds(self)
    }
}

impl Complementable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(self)
    }
}

impl Complementable for AbsoluteInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(&self.emptiable_abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl Complementable for ClosedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(&self.emptiable_abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl Complementable for HalfOpenAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(&self.emptiable_abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl Complementable for RelativeBounds {
    type Output = EmptiableRelativeBounds;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_rel_bounds(self)
    }
}

impl Complementable for EmptiableRelativeBounds {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(self)
    }
}

impl Complementable for RelativeInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(&self.emptiable_rel_bounds()).map(RelativeInterval::from)
    }
}

impl Complementable for ClosedRelativeInterval {
    type Output = RelativeInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(&self.emptiable_rel_bounds()).map(RelativeInterval::from)
    }
}

impl Complementable for HalfOpenRelativeInterval {
    type Output = RelativeInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(&self.emptiable_rel_bounds()).map(RelativeInterval::from)
    }
}

impl Complementable for OpenInterval {
    type Output = EmptyInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        ComplementResult::Single(EmptyInterval)
    }
}

impl Complementable for EmptyInterval {
    type Output = OpenInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        ComplementResult::Single(OpenInterval)
    }
}

/// Returns the complement of an [`AbsoluteBounds`]
pub fn complement_abs_bounds(bounds: &AbsoluteBounds) -> ComplementResult<EmptiableAbsoluteBounds> {
    type Sb = AbsoluteStartBound;
    type Eb = AbsoluteEndBound;

    match (bounds.abs_start(), bounds.abs_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_abs_bounds()),
        (Sb::InfinitePast, Eb::Finite(finite)) => {
            ComplementResult::Single(EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite.time(),
                    finite.inclusivity().opposite(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            )))
        },
        (Sb::Finite(finite), Eb::InfiniteFuture) => {
            ComplementResult::Single(EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite.time(),
                    finite.inclusivity().opposite(),
                )),
            )))
        },
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity().opposite(),
                )),
            )),
            EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite_end.time(),
                    finite_end.inclusivity().opposite(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            )),
        ),
    }
}

/// Returns the complement of an [`EmptiableAbsoluteBounds`]
pub fn complement_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
) -> ComplementResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(OpenInterval.emptiable_abs_bounds());
    };

    complement_abs_bounds(bounds)
}

/// Returns the complement of an [`RelativeBounds`]
pub fn complement_rel_bounds(bounds: &RelativeBounds) -> ComplementResult<EmptiableRelativeBounds> {
    type Sb = RelativeStartBound;
    type Eb = RelativeEndBound;

    match (bounds.rel_start(), bounds.rel_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_rel_bounds()),
        (Sb::InfinitePast, Eb::Finite(finite)) => {
            ComplementResult::Single(EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite.offset(),
                    finite.inclusivity().opposite(),
                )),
                RelativeEndBound::InfiniteFuture,
            )))
        },
        (Sb::Finite(finite), Eb::InfiniteFuture) => {
            ComplementResult::Single(EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite.offset(),
                    finite.inclusivity().opposite(),
                )),
            )))
        },
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity().opposite(),
                )),
            )),
            EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite_end.offset(),
                    finite_end.inclusivity().opposite(),
                )),
                RelativeEndBound::InfiniteFuture,
            )),
        ),
    }
}

/// Returns the complement of an [`EmptiableRelativeBounds`]
pub fn complement_emptiable_rel_bounds(
    emptiable_bounds: &EmptiableRelativeBounds,
) -> ComplementResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(OpenInterval.emptiable_rel_bounds());
    };

    complement_rel_bounds(bounds)
}

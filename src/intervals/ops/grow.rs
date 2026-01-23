//! Interval growth
//!
//! Grows an interval up to a given point.
//!
//! To more explicitly grow an interval, the trait for growth is actually two traits.
//! One for growing the start bound of an interval, [`GrowableStartBound`],
//! and one for growing the end bound of an interval, [`GrowableEndBound`].
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::intervals::ops::grow::GrowableStartBound;
//! let interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! let grown_interval = interval.grow_start(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!     ))
//! );
//!
//! assert_eq!(grown_interval, AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! ));
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfBoundedAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfBoundedRelativeInterval, RelativeBounds, RelativeEndBound, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{BoundedAbsoluteInterval, BoundedRelativeInterval, RelativeInterval};

/// Capacity to grow an interval's start bound up to a given new start bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsoluteStartBound`] or [`RelativeStartBound`].
pub trait GrowableStartBound<P> {
    /// Output type
    type Output;

    /// Grows the start bound of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the start bound is more in the past than the original one.
    /// Of course, it only happens if the passed new start bound is actually more in the past than the original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::grow::GrowableStartBound;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let grown_interval = interval.grow_start(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))
    /// );
    ///
    /// assert_eq!(grown_interval, AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// ));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    fn grow_start(&self, position: P) -> Self::Output;
}

/// Capacity to grow an interval's end bound up to a given new end bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsoluteEndBound`] or [`RelativeEndBound`].
pub trait GrowableEndBound<P> {
    /// Output type
    type Output;

    /// Grows the end of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the end bound is more in the future than the original one.
    /// Of course, it only happens if the passed new end bound is actually more in the future than the original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::grow::GrowableEndBound;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let grown_interval = interval.grow_end(
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))
    /// );
    ///
    /// assert_eq!(grown_interval, AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// ));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
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

impl GrowableStartBound<AbsoluteStartBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(grow_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(grow_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(grow_start_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for HalfBoundedAbsoluteInterval {
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

impl GrowableStartBound<RelativeStartBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(grow_start_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(grow_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(grow_start_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(grow_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_start(&self, _position: AbsoluteStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<AbsoluteEndBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_end(&self, _position: AbsoluteEndBound) -> Self::Output {
        *self
    }
}

impl GrowableStartBound<RelativeStartBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_start(&self, _position: RelativeStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<RelativeEndBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_end(&self, _position: RelativeEndBound) -> Self::Output {
        *self
    }
}

impl GrowableStartBound<AbsoluteStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_start(&self, _position: AbsoluteStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<AbsoluteEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_end(&self, _position: AbsoluteEndBound) -> Self::Output {
        *self
    }
}

impl GrowableStartBound<RelativeStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_start(&self, _position: RelativeStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<RelativeEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_end(&self, _position: RelativeEndBound) -> Self::Output {
        *self
    }
}

/// Grows the start bound of an [`AbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteStartBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.abs_start().min(at));
    new_bounds
}

/// Grows the start bound of an [`EmptiableAbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
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

/// Grows the end bound of an [`AbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_abs_bounds(bounds: &AbsoluteBounds, at: AbsoluteEndBound) -> AbsoluteBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.abs_end().max(at));
    new_bounds
}

/// Grows the end bound of an [`EmptiableAbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
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

/// Grows the start bound of a [`RelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_rel_bounds(bounds: &RelativeBounds, at: RelativeStartBound) -> RelativeBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.rel_start().min(at));
    new_bounds
}

/// Grows the start bound of an [`EmptiableRelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
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

/// Grows the end bound of a [`RelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_rel_bounds(bounds: &RelativeBounds, at: RelativeEndBound) -> RelativeBounds {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.rel_end().max(at));
    new_bounds
}

/// Grows the end bound of an [`EmptiableRelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
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

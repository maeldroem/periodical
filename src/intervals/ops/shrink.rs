//! Interval shrinking
//!
//! Shrinks an interval up to a given point.
//!
//! To more explicitly shrink an interval, the trait for shrinking is actually two traits.
//! One for shrinking the start bound of an interval, [`ShrinkableStartBound`],
//! and one for shrinking the end bound of an interval, [`ShrinkableEndBound`].
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::intervals::ops::shrink::ShrinkableStartBound;
//! let interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! let shrunk_interval = interval.shrink_start(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!     ))
//! );
//!
//! assert_eq!(shrunk_interval, AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! ));
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::cmp::Ordering;

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

/// Capacity to shrink an interval's start bound up to a given new start bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsoluteStartBound`] or [`RelativeStartBound`].
pub trait ShrinkableStartBound<P> {
    /// Output type
    type Output;

    /// Shrinks the start bound of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the start bound is more in the future than the original one.
    /// Of course, it only happens if the passed new start bound is actually more in the future than the original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::shrink::ShrinkableStartBound;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let shrunk_interval = interval.shrink_start(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))
    /// );
    ///
    /// assert_eq!(shrunk_interval, AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// ));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    fn shrink_start(&self, position: P) -> Self::Output;
}

/// Capacity to shrink an interval's end bound up to a given new end bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsoluteEndBound`] or [`RelativeEndBound`].
pub trait ShrinkableEndBound<P> {
    /// Output type
    type Output;

    /// Shrinks the end bound of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the end bound is more in the past than the original one.
    /// Of course, it only happens if the passed new end bound is actually more in the past than the original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::shrink::ShrinkableEndBound;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let shrunk_interval = interval.shrink_end(
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))
    /// );
    ///
    /// assert_eq!(shrunk_interval, AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// ));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
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

impl ShrinkableStartBound<AbsoluteStartBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for HalfBoundedAbsoluteInterval {
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

impl ShrinkableStartBound<RelativeStartBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(shrink_start_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(shrink_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(shrink_start_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        RelativeInterval::from(shrink_end_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        AbsoluteInterval::from(shrink_start_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        AbsoluteInterval::from(shrink_end_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for UnboundedInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        RelativeInterval::from(shrink_start_emptiable_rel_bounds(
            &self.emptiable_rel_bounds(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for UnboundedInterval {
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

/// Shrinks the start bound of the given [`AbsoluteBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

/// Shrinks the start bound of the given [`EmptiableAbsoluteBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

/// Shrinks the end bound of the given [`AbsoluteBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

/// Shrinks the end bound of the given [`EmptiableAbsoluteBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

/// Shrinks the start bound of the given [`RelativeBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

/// Shrinks the start bound of the given [`EmptiableRelativeBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

/// Shrinks the end bound of the given [`RelativeBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

/// Shrinks the end bound of the given [`EmptiableRelativeBounds`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
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

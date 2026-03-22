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
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::ops::grow::GrowableStartBound;
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_end_bound(),
//! );
//!
//! let grown_interval = interval.grow_start(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_start_bound()
//! );
//!
//! assert_eq!(grown_interval, AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_end_bound(),
//! ));
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, BoundedAbsoluteInterval, EmptiableAbsoluteBoundPair, EmptiableAbsoluteInterval, HalfBoundedAbsoluteInterval, HasAbsoluteBoundPair, HasEmptiableAbsoluteBoundPair
};
use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBoundPair, EmptiableRelativeInterval, HalfBoundedRelativeInterval, HasEmptiableRelativeBoundPair, HasRelativeBoundPair, RelativeBoundPair, RelativeEndBound, RelativeInterval, RelativeStartBound
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

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
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::grow::GrowableStartBound;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let grown_interval = interval.grow_start(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound()
    /// );
    ///
    /// assert_eq!(grown_interval, AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// ));
    /// # Ok::<(), Box<dyn Error>>(())
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
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::grow::GrowableEndBound;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let grown_interval = interval.grow_end(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound()
    /// );
    ///
    /// assert_eq!(grown_interval, AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// ));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn grow_end(&self, position: P) -> Self::Output;
}

impl GrowableStartBound<AbsoluteStartBound> for AbsoluteBoundPair {
    type Output = Self;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        grow_start_abs_bound_pair(self, position)
    }
}

impl GrowableEndBound<AbsoluteEndBound> for AbsoluteBoundPair {
    type Output = Self;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        grow_end_abs_bound_pair(self, position)
    }
}

impl GrowableStartBound<AbsoluteStartBound> for EmptiableAbsoluteBoundPair {
    type Output = Self;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        grow_start_emptiable_abs_bound_pair(self, position)
    }
}

impl GrowableEndBound<AbsoluteEndBound> for EmptiableAbsoluteBoundPair {
    type Output = Self;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        grow_end_emptiable_abs_bound_pair(self, position)
    }
}

impl GrowableStartBound<AbsoluteStartBound> for AbsoluteInterval {
    type Output = Self;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(grow_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for AbsoluteInterval {
    type Output = Self;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(grow_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for EmptiableAbsoluteInterval {
    type Output = Self;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(grow_start_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for EmptiableAbsoluteInterval {
    type Output = Self;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(grow_end_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(grow_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(grow_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableStartBound<AbsoluteStartBound> for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(grow_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableEndBound<AbsoluteEndBound> for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn grow_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(grow_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for RelativeBoundPair {
    type Output = Self;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        grow_start_rel_bound_pair(self, position)
    }
}

impl GrowableEndBound<RelativeEndBound> for RelativeBoundPair {
    type Output = Self;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        grow_end_rel_bound_pair(self, position)
    }
}

impl GrowableStartBound<RelativeStartBound> for EmptiableRelativeBoundPair {
    type Output = Self;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        grow_start_emptiable_rel_bound_pair(self, position)
    }
}

impl GrowableEndBound<RelativeEndBound> for EmptiableRelativeBoundPair {
    type Output = Self;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        grow_end_emptiable_rel_bound_pair(self, position)
    }
}

impl GrowableStartBound<RelativeStartBound> for RelativeInterval {
    type Output = Self;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(grow_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for RelativeInterval {
    type Output = Self;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(grow_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for EmptiableRelativeInterval {
    type Output = Self;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(grow_start_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for EmptiableRelativeInterval {
    type Output = Self;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(grow_end_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(grow_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(grow_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableStartBound<RelativeStartBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(grow_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableEndBound<RelativeEndBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn grow_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(grow_end_rel_bound_pair(&self.rel_bound_pair(), position))
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

/// Grows the start bound of an [`AbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_abs_bound_pair(bounds: &AbsoluteBoundPair, at: AbsoluteStartBound) -> AbsoluteBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.abs_start().min(at));
    new_bounds
}

/// Grows the start bound of an [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsoluteBoundPair,
    at: AbsoluteStartBound,
) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBoundPair::from(grow_start_abs_bound_pair(bounds, at))
}

/// Grows the end bound of an [`AbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_abs_bound_pair(bounds: &AbsoluteBoundPair, at: AbsoluteEndBound) -> AbsoluteBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.abs_end().max(at));
    new_bounds
}

/// Grows the end bound of an [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsoluteBoundPair,
    at: AbsoluteEndBound,
) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBoundPair::from(grow_end_abs_bound_pair(bounds, at))
}

/// Grows the start bound of a [`RelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_rel_bound_pair(bounds: &RelativeBoundPair, at: RelativeStartBound) -> RelativeBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.rel_start().min(at));
    new_bounds
}

/// Grows the start bound of an [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelativeBoundPair,
    at: RelativeStartBound,
) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBoundPair::from(grow_start_rel_bound_pair(bounds, at))
}

/// Grows the end bound of a [`RelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_rel_bound_pair(bounds: &RelativeBoundPair, at: RelativeEndBound) -> RelativeBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.rel_end().max(at));
    new_bounds
}

/// Grows the end bound of an [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelativeBoundPair,
    at: RelativeEndBound,
) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBoundPair::from(grow_end_rel_bound_pair(bounds, at))
}

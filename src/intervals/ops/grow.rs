//! Interval growth
//!
//! Grows an interval up to a given point.
//!
//! To more explicitly grow an interval, the trait for growth is actually two
//! traits. One for growing the start bound of an interval,
//! [`GrowableStartBound`], and one for growing the end bound of an interval,
//! [`GrowableEndBound`].
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::ops::grow::GrowableStartBound;
//! let interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 10:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let grown_interval = interval.grow_start(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//! );
//!
//! assert_eq!(
//!     grown_interval,
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 14:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     )
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Capacity to grow an interval's start bound up to a given new start bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsStartBound`] or [`RelStartBound`].
pub trait GrowableStartBound<P> {
    /// Output type
    type Output;

    /// Grows the start bound of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the start bound is
    /// more in the past than the original one. Of course, it only happens
    /// if the passed new start bound is actually more in the past than the
    /// original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::grow::GrowableStartBound;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let grown_interval = interval.grow_start(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     grown_interval,
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn grow_start(&self, position: P) -> Self::Output;
}

/// Capacity to grow an interval's end bound up to a given new end bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsEndBound`] or [`RelEndBound`].
pub trait GrowableEndBound<P> {
    /// Output type
    type Output;

    /// Grows the end of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the end bound is
    /// more in the future than the original one. Of course, it only happens
    /// if the passed new end bound is actually more in the future than the
    /// original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::grow::GrowableEndBound;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let grown_interval = interval.grow_end(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     grown_interval,
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 10:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn grow_end(&self, position: P) -> Self::Output;
}

impl GrowableStartBound<AbsStartBound> for AbsBoundPair {
    type Output = Self;

    fn grow_start(&self, position: AbsStartBound) -> Self::Output {
        grow_start_abs_bound_pair(self, position)
    }
}

impl GrowableEndBound<AbsEndBound> for AbsBoundPair {
    type Output = Self;

    fn grow_end(&self, position: AbsEndBound) -> Self::Output {
        grow_end_abs_bound_pair(self, position)
    }
}

impl GrowableStartBound<AbsStartBound> for EmptiableAbsBoundPair {
    type Output = Self;

    fn grow_start(&self, position: AbsStartBound) -> Self::Output {
        grow_start_emptiable_abs_bound_pair(self, position)
    }
}

impl GrowableEndBound<AbsEndBound> for EmptiableAbsBoundPair {
    type Output = Self;

    fn grow_end(&self, position: AbsEndBound) -> Self::Output {
        grow_end_emptiable_abs_bound_pair(self, position)
    }
}

impl GrowableStartBound<AbsStartBound> for AbsInterval {
    type Output = Self;

    fn grow_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(grow_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableEndBound<AbsEndBound> for AbsInterval {
    type Output = Self;

    fn grow_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(grow_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableStartBound<AbsStartBound> for EmptiableAbsInterval {
    type Output = Self;

    fn grow_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(grow_start_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            position,
        ))
    }
}

impl GrowableEndBound<AbsEndBound> for EmptiableAbsInterval {
    type Output = Self;

    fn grow_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(grow_end_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            position,
        ))
    }
}

impl GrowableStartBound<AbsStartBound> for BoundedAbsInterval {
    type Output = AbsInterval;

    fn grow_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(grow_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableEndBound<AbsEndBound> for BoundedAbsInterval {
    type Output = AbsInterval;

    fn grow_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(grow_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableStartBound<AbsStartBound> for HalfBoundedAbsInterval {
    type Output = AbsInterval;

    fn grow_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(grow_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableEndBound<AbsEndBound> for HalfBoundedAbsInterval {
    type Output = AbsInterval;

    fn grow_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(grow_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl GrowableStartBound<RelStartBound> for RelBoundPair {
    type Output = Self;

    fn grow_start(&self, position: RelStartBound) -> Self::Output {
        grow_start_rel_bound_pair(self, position)
    }
}

impl GrowableEndBound<RelEndBound> for RelBoundPair {
    type Output = Self;

    fn grow_end(&self, position: RelEndBound) -> Self::Output {
        grow_end_rel_bound_pair(self, position)
    }
}

impl GrowableStartBound<RelStartBound> for EmptiableRelBoundPair {
    type Output = Self;

    fn grow_start(&self, position: RelStartBound) -> Self::Output {
        grow_start_emptiable_rel_bound_pair(self, position)
    }
}

impl GrowableEndBound<RelEndBound> for EmptiableRelBoundPair {
    type Output = Self;

    fn grow_end(&self, position: RelEndBound) -> Self::Output {
        grow_end_emptiable_rel_bound_pair(self, position)
    }
}

impl GrowableStartBound<RelStartBound> for RelInterval {
    type Output = Self;

    fn grow_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(grow_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableEndBound<RelEndBound> for RelInterval {
    type Output = Self;

    fn grow_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(grow_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableStartBound<RelStartBound> for EmptiableRelInterval {
    type Output = Self;

    fn grow_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(grow_start_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            position,
        ))
    }
}

impl GrowableEndBound<RelEndBound> for EmptiableRelInterval {
    type Output = Self;

    fn grow_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(grow_end_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            position,
        ))
    }
}

impl GrowableStartBound<RelStartBound> for BoundedRelInterval {
    type Output = RelInterval;

    fn grow_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(grow_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableEndBound<RelEndBound> for BoundedRelInterval {
    type Output = RelInterval;

    fn grow_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(grow_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableStartBound<RelStartBound> for HalfBoundedRelInterval {
    type Output = RelInterval;

    fn grow_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(grow_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableEndBound<RelEndBound> for HalfBoundedRelInterval {
    type Output = RelInterval;

    fn grow_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(grow_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl GrowableStartBound<AbsStartBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_start(&self, _position: AbsStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<AbsEndBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_end(&self, _position: AbsEndBound) -> Self::Output {
        *self
    }
}

impl GrowableStartBound<RelStartBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_start(&self, _position: RelStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<RelEndBound> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn grow_end(&self, _position: RelEndBound) -> Self::Output {
        *self
    }
}

impl GrowableStartBound<AbsStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_start(&self, _position: AbsStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<AbsEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_end(&self, _position: AbsEndBound) -> Self::Output {
        *self
    }
}

impl GrowableStartBound<RelStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_start(&self, _position: RelStartBound) -> Self::Output {
        *self
    }
}

impl GrowableEndBound<RelEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn grow_end(&self, _position: RelEndBound) -> Self::Output {
        *self
    }
}

/// Grows the start bound of an [`AbsBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_abs_bound_pair(bounds: &AbsBoundPair, at: AbsStartBound) -> AbsBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.abs_start().min(at));
    new_bounds
}

/// Grows the start bound of an [`EmptiableAbsBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsBoundPair,
    at: AbsStartBound,
) -> EmptiableAbsBoundPair {
    let EmptiableAbsBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsBoundPair::from(grow_start_abs_bound_pair(bounds, at))
}

/// Grows the end bound of an [`AbsBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_abs_bound_pair(bounds: &AbsBoundPair, at: AbsEndBound) -> AbsBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.abs_end().max(at));
    new_bounds
}

/// Grows the end bound of an [`EmptiableAbsBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsBoundPair,
    at: AbsEndBound,
) -> EmptiableAbsBoundPair {
    let EmptiableAbsBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsBoundPair::from(grow_end_abs_bound_pair(bounds, at))
}

/// Grows the start bound of a [`RelBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_rel_bound_pair(bounds: &RelBoundPair, at: RelStartBound) -> RelBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_start(new_bounds.rel_start().min(at));
    new_bounds
}

/// Grows the start bound of an [`EmptiableRelBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_start_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelBoundPair,
    at: RelStartBound,
) -> EmptiableRelBoundPair {
    let EmptiableRelBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelBoundPair::from(grow_start_rel_bound_pair(bounds, at))
}

/// Grows the end bound of a [`RelBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_rel_bound_pair(bounds: &RelBoundPair, at: RelEndBound) -> RelBoundPair {
    let mut new_bounds = bounds.clone();
    new_bounds.set_end(new_bounds.rel_end().max(at));
    new_bounds
}

/// Grows the end bound of an [`EmptiableRelBoundPair`]
///
/// See [module documentation](crate::intervals::ops::grow) for more info.
#[must_use]
pub fn grow_end_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelBoundPair,
    at: RelEndBound,
) -> EmptiableRelBoundPair {
    let EmptiableRelBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelBoundPair::from(grow_end_rel_bound_pair(bounds, at))
}

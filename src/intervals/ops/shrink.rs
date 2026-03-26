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
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::ops::shrink::ShrinkableStartBound;
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_end_bound(),
//! );
//!
//! let shrunk_interval = interval.shrink_start(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_start_bound()
//! );
//!
//! assert_eq!(shrunk_interval, AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_end_bound(),
//! ));
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use std::cmp::Ordering;

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, BoundedAbsoluteInterval, EmptiableAbsoluteBoundPair, EmptiableAbsoluteInterval, HalfBoundedAbsoluteInterval, HasAbsoluteBoundPair, HasEmptiableAbsoluteBoundPair
};
use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBoundPair, EmptiableRelativeInterval, HalfBoundedRelativeInterval, HasEmptiableRelativeBoundPair, HasRelativeBoundPair, RelativeBoundPair, RelativeEndBound, RelativeInterval, RelativeStartBound
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

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
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::shrink::ShrinkableStartBound;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let shrunk_interval = interval.shrink_start(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound()
    /// );
    ///
    /// assert_eq!(shrunk_interval, AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// ));
    /// # Ok::<(), Box<dyn Error>>(())
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
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::shrink::ShrinkableEndBound;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let shrunk_interval = interval.shrink_end(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound()
    /// );
    ///
    /// assert_eq!(shrunk_interval, AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// ));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn shrink_end(&self, position: P) -> Self::Output;
}

impl ShrinkableStartBound<AbsoluteStartBound> for AbsoluteBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        shrink_start_abs_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for AbsoluteBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        shrink_end_abs_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for EmptiableAbsoluteBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        shrink_start_emptiable_abs_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for EmptiableAbsoluteBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        shrink_end_emptiable_abs_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for AbsoluteInterval {
    type Output = Self;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(
            &self.abs_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for AbsoluteInterval {
    type Output = Self;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for EmptiableAbsoluteInterval {
    type Output = Self;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(shrink_start_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for EmptiableAbsoluteInterval {
    type Output = Self;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(shrink_end_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(
            &self.abs_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(
            &self.abs_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for RelativeBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        shrink_start_rel_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<RelativeEndBound> for RelativeBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        shrink_end_rel_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<RelativeStartBound> for EmptiableRelativeBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        shrink_start_emptiable_rel_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<RelativeEndBound> for EmptiableRelativeBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        shrink_end_emptiable_rel_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<RelativeStartBound> for RelativeInterval {
    type Output = Self;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(
            &self.rel_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for RelativeInterval {
    type Output = Self;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for EmptiableRelativeInterval {
    type Output = Self;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(shrink_start_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for EmptiableRelativeInterval {
    type Output = Self;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(shrink_end_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(
            &self.rel_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(
            &self.rel_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsoluteStartBound> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn shrink_start(&self, position: AbsoluteStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(
            &self.abs_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsoluteEndBound> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn shrink_end(&self, position: AbsoluteEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelativeStartBound> for UnboundedInterval {
    type Output = RelativeInterval;

    fn shrink_start(&self, position: RelativeStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(
            &self.rel_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelativeEndBound> for UnboundedInterval {
    type Output = RelativeInterval;

    fn shrink_end(&self, position: RelativeEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
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

/// Shrinks the start bound of the given [`AbsoluteBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_start_abs_bound_pair(bounds: &AbsoluteBoundPair, at: AbsoluteStartBound) -> AbsoluteBoundPair {
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

/// Shrinks the start bound of the given [`EmptiableAbsoluteBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_start_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsoluteBoundPair,
    at: AbsoluteStartBound,
) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBoundPair::from(shrink_start_abs_bound_pair(bounds, at))
}

/// Shrinks the end bound of the given [`AbsoluteBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_end_abs_bound_pair(bounds: &AbsoluteBoundPair, at: AbsoluteEndBound) -> AbsoluteBoundPair {
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

/// Shrinks the end bound of the given [`EmptiableAbsoluteBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_end_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsoluteBoundPair,
    at: AbsoluteEndBound,
) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsoluteBoundPair::from(shrink_end_abs_bound_pair(bounds, at))
}

/// Shrinks the start bound of the given [`RelativeBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_start_rel_bound_pair(bounds: &RelativeBoundPair, at: RelativeStartBound) -> RelativeBoundPair {
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

/// Shrinks the start bound of the given [`EmptiableRelativeBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_start_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelativeBoundPair,
    at: RelativeStartBound,
) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBoundPair::from(shrink_start_rel_bound_pair(bounds, at))
}

/// Shrinks the end bound of the given [`RelativeBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_end_rel_bound_pair(bounds: &RelativeBoundPair, at: RelativeEndBound) -> RelativeBoundPair {
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

/// Shrinks the end bound of the given [`EmptiableRelativeBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more information.
#[must_use]
pub fn shrink_end_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelativeBoundPair,
    at: RelativeEndBound,
) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelativeBoundPair::from(shrink_end_rel_bound_pair(bounds, at))
}

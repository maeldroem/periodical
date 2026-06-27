//! Interval shrinking
//!
//! Shrinks an interval up to a given point.
//!
//! To more explicitly shrink an interval, the trait for shrinking is actually
//! two traits. One for shrinking the start bound of an interval,
//! [`ShrinkableStartBound`], and one for shrinking the end bound of an
//! interval, [`ShrinkableEndBound`].
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::ops::shrink::ShrinkableStartBound;
//! let interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
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
//! let shrunk_interval = interval.shrink_start(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 10:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//! );
//!
//! assert_eq!(
//!     shrunk_interval,
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 10:00:00[Europe/Oslo]"
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
use crate::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
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

/// Capacity to shrink an interval's start bound up to a given new start bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsStartBound`] or [`RelStartBound`].
pub trait ShrinkableStartBound<P> {
    /// Output type
    type Output;

    /// Shrinks the start bound of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the start bound is
    /// more in the future than the original one. Of course, it only happens
    /// if the passed new start bound is actually more in the future than the
    /// original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::shrink::ShrinkableStartBound;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
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
    /// let shrunk_interval = interval.shrink_start(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     shrunk_interval,
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 10:00:00[Europe/Oslo]"
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
    fn shrink_start(&self, position: P) -> Self::Output;
}

/// Capacity to shrink an interval's end bound up to a given new end bound
///
/// The generic type parameter `P` corresponds to the position type,
/// usually an [`AbsEndBound`] or [`RelEndBound`].
pub trait ShrinkableEndBound<P> {
    /// Output type
    type Output;

    /// Shrinks the end bound of the given interval up to the given bound
    ///
    /// This method creates a version of the interval where the end bound is
    /// more in the past than the original one. Of course, it only happens
    /// if the passed new end bound is actually more in the past than the
    /// original one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::shrink::ShrinkableEndBound;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
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
    /// let shrunk_interval = interval.shrink_end(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     shrunk_interval,
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn shrink_end(&self, position: P) -> Self::Output;
}

impl ShrinkableStartBound<AbsStartBound> for AbsBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: AbsStartBound) -> Self::Output {
        shrink_start_abs_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<AbsEndBound> for AbsBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: AbsEndBound) -> Self::Output {
        shrink_end_abs_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<AbsStartBound> for EmptiableAbsBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: AbsStartBound) -> Self::Output {
        shrink_start_emptiable_abs_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<AbsEndBound> for EmptiableAbsBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: AbsEndBound) -> Self::Output {
        shrink_end_emptiable_abs_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<AbsStartBound> for AbsInterval {
    type Output = Self;

    fn shrink_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableEndBound<AbsEndBound> for AbsInterval {
    type Output = Self;

    fn shrink_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsStartBound> for EmptiableAbsInterval {
    type Output = Self;

    fn shrink_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(shrink_start_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<AbsEndBound> for EmptiableAbsInterval {
    type Output = Self;

    fn shrink_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(shrink_end_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableStartBound<AbsStartBound> for BoundedAbsInterval {
    type Output = AbsInterval;

    fn shrink_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableEndBound<AbsEndBound> for BoundedAbsInterval {
    type Output = AbsInterval;

    fn shrink_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsStartBound> for HalfBoundedAbsInterval {
    type Output = AbsInterval;

    fn shrink_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableEndBound<AbsEndBound> for HalfBoundedAbsInterval {
    type Output = AbsInterval;

    fn shrink_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelStartBound> for RelBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: RelStartBound) -> Self::Output {
        shrink_start_rel_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<RelEndBound> for RelBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: RelEndBound) -> Self::Output {
        shrink_end_rel_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<RelStartBound> for EmptiableRelBoundPair {
    type Output = Self;

    fn shrink_start(&self, position: RelStartBound) -> Self::Output {
        shrink_start_emptiable_rel_bound_pair(self, position)
    }
}

impl ShrinkableEndBound<RelEndBound> for EmptiableRelBoundPair {
    type Output = Self;

    fn shrink_end(&self, position: RelEndBound) -> Self::Output {
        shrink_end_emptiable_rel_bound_pair(self, position)
    }
}

impl ShrinkableStartBound<RelStartBound> for RelInterval {
    type Output = Self;

    fn shrink_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableEndBound<RelEndBound> for RelInterval {
    type Output = Self;

    fn shrink_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelStartBound> for EmptiableRelInterval {
    type Output = Self;

    fn shrink_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(shrink_start_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableEndBound<RelEndBound> for EmptiableRelInterval {
    type Output = Self;

    fn shrink_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(shrink_end_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            position,
        ))
    }
}

impl ShrinkableStartBound<RelStartBound> for BoundedRelInterval {
    type Output = RelInterval;

    fn shrink_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableEndBound<RelEndBound> for BoundedRelInterval {
    type Output = RelInterval;

    fn shrink_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelStartBound> for HalfBoundedRelInterval {
    type Output = RelInterval;

    fn shrink_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableEndBound<RelEndBound> for HalfBoundedRelInterval {
    type Output = RelInterval;

    fn shrink_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsStartBound> for UnboundedInterval {
    type Output = AbsInterval;

    fn shrink_start(&self, position: AbsStartBound) -> Self::Output {
        Self::Output::from(shrink_start_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableEndBound<AbsEndBound> for UnboundedInterval {
    type Output = AbsInterval;

    fn shrink_end(&self, position: AbsEndBound) -> Self::Output {
        Self::Output::from(shrink_end_abs_bound_pair(&self.abs_bound_pair(), position))
    }
}

impl ShrinkableStartBound<RelStartBound> for UnboundedInterval {
    type Output = RelInterval;

    fn shrink_start(&self, position: RelStartBound) -> Self::Output {
        Self::Output::from(shrink_start_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableEndBound<RelEndBound> for UnboundedInterval {
    type Output = RelInterval;

    fn shrink_end(&self, position: RelEndBound) -> Self::Output {
        Self::Output::from(shrink_end_rel_bound_pair(&self.rel_bound_pair(), position))
    }
}

impl ShrinkableStartBound<AbsStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_start(&self, _position: AbsStartBound) -> Self::Output {
        *self
    }
}

impl ShrinkableEndBound<AbsEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_end(&self, _position: AbsEndBound) -> Self::Output {
        *self
    }
}

impl ShrinkableStartBound<RelStartBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_start(&self, _position: RelStartBound) -> Self::Output {
        *self
    }
}

impl ShrinkableEndBound<RelEndBound> for EmptyInterval {
    type Output = EmptyInterval;

    fn shrink_end(&self, _position: RelEndBound) -> Self::Output {
        *self
    }
}

/// Shrinks the start bound of the given [`AbsBoundPair`] to the given
/// bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_start_abs_bound_pair(bounds: &AbsBoundPair, at: AbsStartBound) -> AbsBoundPair {
    let mut new_bounds = bounds.clone();
    let max_start = new_bounds.abs_start().max(at);

    if max_start.bound_le(&new_bounds.abs_end(), BoundOverlapDisambiguationRuleSet::Strict) {
        new_bounds.set_start(max_start);
    }

    new_bounds
}

/// Shrinks the start bound of the given [`EmptiableAbsBoundPair`] to the
/// given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_start_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsBoundPair,
    at: AbsStartBound,
) -> EmptiableAbsBoundPair {
    let EmptiableAbsBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsBoundPair::from(shrink_start_abs_bound_pair(bounds, at))
}

/// Shrinks the end bound of the given [`AbsBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_end_abs_bound_pair(bounds: &AbsBoundPair, at: AbsEndBound) -> AbsBoundPair {
    let mut new_bounds = bounds.clone();
    let min_end = new_bounds.abs_end().min(at);

    if new_bounds
        .abs_start()
        .bound_le(&min_end, BoundOverlapDisambiguationRuleSet::Strict)
    {
        new_bounds.set_end(min_end);
    }

    new_bounds
}

/// Shrinks the end bound of the given [`EmptiableAbsBoundPair`] to the
/// given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_end_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsBoundPair,
    at: AbsEndBound,
) -> EmptiableAbsBoundPair {
    let EmptiableAbsBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableAbsBoundPair::from(shrink_end_abs_bound_pair(bounds, at))
}

/// Shrinks the start bound of the given [`RelBoundPair`] to the given
/// bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_start_rel_bound_pair(bounds: &RelBoundPair, at: RelStartBound) -> RelBoundPair {
    let mut new_bounds = bounds.clone();
    let max_start = new_bounds.rel_start().max(at);

    if max_start.bound_le(&new_bounds.rel_end(), BoundOverlapDisambiguationRuleSet::Strict) {
        new_bounds.set_start(max_start);
    }

    new_bounds
}

/// Shrinks the start bound of the given [`EmptiableRelBoundPair`] to the
/// given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_start_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelBoundPair,
    at: RelStartBound,
) -> EmptiableRelBoundPair {
    let EmptiableRelBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelBoundPair::from(shrink_start_rel_bound_pair(bounds, at))
}

/// Shrinks the end bound of the given [`RelBoundPair`] to the given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_end_rel_bound_pair(bounds: &RelBoundPair, at: RelEndBound) -> RelBoundPair {
    let mut new_bounds = bounds.clone();
    let min_end = new_bounds.rel_end().min(at);

    if new_bounds
        .rel_start()
        .bound_le(&min_end, BoundOverlapDisambiguationRuleSet::Strict)
    {
        new_bounds.set_end(min_end);
    }

    new_bounds
}

/// Shrinks the end bound of the given [`EmptiableRelBoundPair`] to the
/// given bound
///
/// See [module documentation](crate::intervals::ops::shrink) for more
/// information.
#[must_use]
pub fn shrink_end_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelBoundPair,
    at: RelEndBound,
) -> EmptiableRelBoundPair {
    let EmptiableRelBoundPair::Bound(bounds) = emptiable_bounds else {
        return emptiable_bounds.clone();
    };

    EmptiableRelBoundPair::from(shrink_end_rel_bound_pair(bounds, at))
}

//! Continuation intervals, both towards past and future, of a given interval
//!
//! A continuation interval is similar to a
//! [complement](crate::intervals::ops::complement), but with the explicit
//! purpose of finding which interval, following a direction time, _continues_
//! before/after the given one.
//!
//! Contrary to complements, an empty interval doesn't possess any continuation
//! intervals.
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::continuation::Continuable;
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! assert_eq!(
//!     interval.past_continuation(),
//!     AbsoluteBoundPair::new(
//!         AbsoluteStartBound::InfinitePast,
//!         AbsoluteFiniteBound::new_with_inclusivity(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!             BoundInclusivity::Exclusive,
//!         )
//!         .to_end_bound(),
//!     )
//!     .to_emptiable(),
//! );
//! assert_eq!(
//!     interval.future_continuation(),
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new_with_inclusivity(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!             BoundInclusivity::Exclusive,
//!         )
//!         .to_start_bound(),
//!         AbsoluteEndBound::InfiniteFuture,
//!     )
//!     .to_emptiable(),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Capacity to get the past and future continuations of a given interval
///
/// A continuation interval is similar to a
/// [complement](crate::intervals::ops::complement), but with the explicit
/// purpose of finding which interval, following a direction time, _continues_
/// before/after the given one.
///
/// Contrary to complements, an empty interval doesn't possess any continuation
/// intervals.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::continuation::Continuable;
/// let interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 16:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.past_continuation(),
///     AbsoluteBoundPair::new(
///         AbsoluteStartBound::InfinitePast,
///         AbsoluteFiniteBound::new_with_inclusivity(
///             "2025-01-01 08:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///             BoundInclusivity::Exclusive,
///         )
///         .to_end_bound(),
///     )
///     .to_emptiable(),
/// );
/// assert_eq!(
///     interval.future_continuation(),
///     AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new_with_inclusivity(
///             "2025-01-01 16:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///             BoundInclusivity::Exclusive,
///         )
///         .to_start_bound(),
///         AbsoluteEndBound::InfiniteFuture,
///     )
///     .to_emptiable(),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Continuable {
    /// Output type
    type Output;

    /// Returns the past continuation of the given interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBoundPair, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::continuation::Continuable;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.past_continuation(),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteStartBound::InfinitePast,
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_end_bound(),
    ///     )
    ///     .to_emptiable(),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn past_continuation(&self) -> Self::Output;

    /// Returns the future continuation of the given interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::continuation::Continuable;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.future_continuation(),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteEndBound::InfiniteFuture,
    ///     )
    ///     .to_emptiable(),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn future_continuation(&self) -> Self::Output;
}

impl Continuable for AbsoluteBoundPair {
    type Output = EmptiableAbsoluteBoundPair;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_abs_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_abs_bound_pair(self)
    }
}

impl Continuable for EmptiableAbsoluteBoundPair {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_emptiable_abs_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_emptiable_abs_bound_pair(self)
    }
}

impl Continuable for AbsoluteInterval {
    type Output = EmptiableAbsoluteInterval;

    fn past_continuation(&self) -> Self::Output {
        Self::Output::from(past_continuation_abs_bound_pair(&self.abs_bound_pair()))
    }

    fn future_continuation(&self) -> Self::Output {
        Self::Output::from(future_continuation_abs_bound_pair(&self.abs_bound_pair()))
    }
}

impl Continuable for EmptiableAbsoluteInterval {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        Self::Output::from(past_continuation_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
        ))
    }

    fn future_continuation(&self) -> Self::Output {
        Self::Output::from(future_continuation_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
        ))
    }
}

impl Continuable for BoundedAbsoluteInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_bounded_abs_interval(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_bounded_abs_interval(self)
    }
}

impl Continuable for HalfBoundedAbsoluteInterval {
    type Output = EmptiableAbsoluteInterval;

    fn past_continuation(&self) -> Self::Output {
        EmptiableAbsoluteInterval::from(past_continuation_abs_bound_pair(&self.abs_bound_pair()))
    }

    fn future_continuation(&self) -> Self::Output {
        EmptiableAbsoluteInterval::from(future_continuation_abs_bound_pair(&self.abs_bound_pair()))
    }
}

impl Continuable for RelativeBoundPair {
    type Output = EmptiableRelativeBoundPair;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_rel_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_rel_bound_pair(self)
    }
}

impl Continuable for EmptiableRelativeBoundPair {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_emptiable_rel_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_emptiable_rel_bound_pair(self)
    }
}

impl Continuable for RelativeInterval {
    type Output = EmptiableRelativeInterval;

    fn past_continuation(&self) -> Self::Output {
        Self::Output::from(past_continuation_rel_bound_pair(&self.rel_bound_pair()))
    }

    fn future_continuation(&self) -> Self::Output {
        Self::Output::from(future_continuation_rel_bound_pair(&self.rel_bound_pair()))
    }
}

impl Continuable for EmptiableRelativeInterval {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        Self::Output::from(past_continuation_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
        ))
    }

    fn future_continuation(&self) -> Self::Output {
        Self::Output::from(future_continuation_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
        ))
    }
}

impl Continuable for BoundedRelativeInterval {
    type Output = HalfBoundedRelativeInterval;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_bounded_rel_interval(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_bounded_rel_interval(self)
    }
}

impl Continuable for HalfBoundedRelativeInterval {
    type Output = EmptiableRelativeInterval;

    fn past_continuation(&self) -> Self::Output {
        Self::Output::from(past_continuation_rel_bound_pair(&self.rel_bound_pair()))
    }

    fn future_continuation(&self) -> Self::Output {
        Self::Output::from(future_continuation_rel_bound_pair(&self.rel_bound_pair()))
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

/// Returns the past continuation of the given [`AbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_abs_bound_pair(bounds: &AbsoluteBoundPair) -> EmptiableAbsoluteBoundPair {
    match bounds.abs_start() {
        AbsoluteStartBound::InfinitePast => EmptiableAbsoluteBoundPair::Empty,
        AbsoluteStartBound::Finite(finite) => EmptiableAbsoluteBoundPair::from(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new_with_inclusivity(
                finite.time(),
                finite.inclusivity().opposite(),
            ).to_end_bound(),
        )),
    }
}

/// Returns the future continuation of the given [`AbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_abs_bound_pair(bounds: &AbsoluteBoundPair) -> EmptiableAbsoluteBoundPair {
    match bounds.abs_end() {
        AbsoluteEndBound::InfiniteFuture => EmptiableAbsoluteBoundPair::Empty,
        AbsoluteEndBound::Finite(finite) => EmptiableAbsoluteBoundPair::from(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                finite.time(),
                finite.inclusivity().opposite(),
            ).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        )),
    }
}

/// Returns the past continuation of the given [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_emptiable_abs_bound_pair(bounds: &EmptiableAbsoluteBoundPair) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(bounds) = bounds else {
        return EmptiableAbsoluteBoundPair::Empty;
    };

    past_continuation_abs_bound_pair(bounds)
}

/// Returns the future continuation of the given [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_emptiable_abs_bound_pair(bounds: &EmptiableAbsoluteBoundPair) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(bounds) = bounds else {
        return EmptiableAbsoluteBoundPair::Empty;
    };

    future_continuation_abs_bound_pair(bounds)
}

/// Returns the past continuation of the given [`BoundedAbsoluteInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_bounded_abs_interval(interval: &BoundedAbsoluteInterval) -> HalfBoundedAbsoluteInterval {
    HalfBoundedAbsoluteInterval::new_with_inclusivity(
        interval.start(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    )
}

/// Returns the future continuation of the given [`BoundedAbsoluteInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_bounded_abs_interval(interval: &BoundedAbsoluteInterval) -> HalfBoundedAbsoluteInterval {
    HalfBoundedAbsoluteInterval::new_with_inclusivity(
        interval.end(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    )
}

/// Returns the past continuation of the given [`RelativeBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_rel_bound_pair(bounds: &RelativeBoundPair) -> EmptiableRelativeBoundPair {
    match bounds.rel_start() {
        RelativeStartBound::InfinitePast => EmptiableRelativeBoundPair::Empty,
        RelativeStartBound::Finite(finite) => EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new_with_inclusivity(
                finite.offset(),
                finite.inclusivity().opposite(),
            ).to_end_bound(),
        )),
    }
}

/// Returns the future continuation of the given [`RelativeBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_rel_bound_pair(bounds: &RelativeBoundPair) -> EmptiableRelativeBoundPair {
    match bounds.rel_end() {
        RelativeEndBound::InfiniteFuture => EmptiableRelativeBoundPair::Empty,
        RelativeEndBound::Finite(finite) => EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(
                finite.offset(),
                finite.inclusivity().opposite(),
            ).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )),
    }
}

/// Returns the past continuation of the given [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_emptiable_rel_bound_pair(bounds: &EmptiableRelativeBoundPair) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(bounds) = bounds else {
        return EmptiableRelativeBoundPair::Empty;
    };

    past_continuation_rel_bound_pair(bounds)
}

/// Returns the future continuation of the given [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_emptiable_rel_bound_pair(bounds: &EmptiableRelativeBoundPair) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(bounds) = bounds else {
        return EmptiableRelativeBoundPair::Empty;
    };

    future_continuation_rel_bound_pair(bounds)
}

/// Returns the past continuation of the given [`BoundedRelativeInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_bounded_rel_interval(interval: &BoundedRelativeInterval) -> HalfBoundedRelativeInterval {
    HalfBoundedRelativeInterval::new_with_inclusivity(
        interval.start(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    )
}

/// Returns the future continuation of the given [`BoundedRelativeInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_bounded_rel_interval(interval: &BoundedRelativeInterval) -> HalfBoundedRelativeInterval {
    HalfBoundedRelativeInterval::new_with_inclusivity(
        interval.end(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    )
}

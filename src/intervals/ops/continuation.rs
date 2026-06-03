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
//! #     AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::continuation::Continuable;
//! let interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! assert_eq!(
//!     interval.past_continuation(),
//!     AbsBoundPair::new(
//!         AbsStartBound::InfinitePast,
//!         AbsFiniteBoundPos::new_with_incl(
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
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new_with_incl(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!             BoundInclusivity::Exclusive,
//!         )
//!         .to_start_bound(),
//!         AbsEndBound::InfiniteFuture,
//!     )
//!     .to_emptiable(),
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
use crate::intervals::meta::OpeningDirection;
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
/// #     AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::continuation::Continuable;
/// let interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 16:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.past_continuation(),
///     AbsBoundPair::new(
///         AbsStartBound::InfinitePast,
///         AbsFiniteBoundPos::new_with_incl(
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
///     AbsBoundPair::new(
///         AbsFiniteBoundPos::new_with_incl(
///             "2025-01-01 16:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///             BoundInclusivity::Exclusive,
///         )
///         .to_start_bound(),
///         AbsEndBound::InfiniteFuture,
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
    /// #     AbsBoundPair, AbsFiniteBoundPos, AbsStartBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::continuation::Continuable;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.past_continuation(),
    ///     AbsBoundPair::new(
    ///         AbsStartBound::InfinitePast,
    ///         AbsFiniteBoundPos::new_with_incl(
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
    /// #     AbsBoundPair, AbsEndBound, AbsFiniteBoundPos,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::continuation::Continuable;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.future_continuation(),
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///         AbsEndBound::InfiniteFuture,
    ///     )
    ///     .to_emptiable(),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn future_continuation(&self) -> Self::Output;
}

impl Continuable for AbsBoundPair {
    type Output = EmptiableAbsBoundPair;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_abs_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_abs_bound_pair(self)
    }
}

impl Continuable for EmptiableAbsBoundPair {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_emptiable_abs_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_emptiable_abs_bound_pair(self)
    }
}

impl Continuable for AbsInterval {
    type Output = EmptiableAbsInterval;

    fn past_continuation(&self) -> Self::Output {
        Self::Output::from(past_continuation_abs_bound_pair(&self.abs_bound_pair()))
    }

    fn future_continuation(&self) -> Self::Output {
        Self::Output::from(future_continuation_abs_bound_pair(&self.abs_bound_pair()))
    }
}

impl Continuable for EmptiableAbsInterval {
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

impl Continuable for BoundedAbsInterval {
    type Output = HalfBoundedAbsInterval;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_bounded_abs_interval(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_bounded_abs_interval(self)
    }
}

impl Continuable for HalfBoundedAbsInterval {
    type Output = EmptiableAbsInterval;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_abs_bound_pair(&self.abs_bound_pair()).to_emptiable_interval()
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_abs_bound_pair(&self.abs_bound_pair()).to_emptiable_interval()
    }
}

impl Continuable for RelBoundPair {
    type Output = EmptiableRelBoundPair;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_rel_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_rel_bound_pair(self)
    }
}

impl Continuable for EmptiableRelBoundPair {
    type Output = Self;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_emptiable_rel_bound_pair(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_emptiable_rel_bound_pair(self)
    }
}

impl Continuable for RelInterval {
    type Output = EmptiableRelInterval;

    fn past_continuation(&self) -> Self::Output {
        Self::Output::from(past_continuation_rel_bound_pair(&self.rel_bound_pair()))
    }

    fn future_continuation(&self) -> Self::Output {
        Self::Output::from(future_continuation_rel_bound_pair(&self.rel_bound_pair()))
    }
}

impl Continuable for EmptiableRelInterval {
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

impl Continuable for BoundedRelInterval {
    type Output = HalfBoundedRelInterval;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_bounded_rel_interval(self)
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_bounded_rel_interval(self)
    }
}

impl Continuable for HalfBoundedRelInterval {
    type Output = EmptiableRelInterval;

    fn past_continuation(&self) -> Self::Output {
        past_continuation_rel_bound_pair(&self.rel_bound_pair()).to_emptiable_interval()
    }

    fn future_continuation(&self) -> Self::Output {
        future_continuation_rel_bound_pair(&self.rel_bound_pair()).to_emptiable_interval()
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

/// Returns the past continuation of the given [`AbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_abs_bound_pair(bounds: &AbsBoundPair) -> EmptiableAbsBoundPair {
    match bounds.abs_start() {
        AbsStartBound::InfinitePast => EmptiableAbsBoundPair::Empty,
        AbsStartBound::Finite(finite_start) => {
            AbsBoundPair::new(AbsStartBound::InfinitePast, finite_start.opposite().to_end_bound()).to_emptiable()
        },
    }
}

/// Returns the future continuation of the given [`AbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_abs_bound_pair(bounds: &AbsBoundPair) -> EmptiableAbsBoundPair {
    match bounds.abs_end() {
        AbsEndBound::InfiniteFuture => EmptiableAbsBoundPair::Empty,
        AbsEndBound::Finite(finite_end) => {
            AbsBoundPair::new(finite_end.opposite().to_start_bound(), AbsEndBound::InfiniteFuture).to_emptiable()
        },
    }
}

/// Returns the past continuation of the given [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_emptiable_abs_bound_pair(bounds: &EmptiableAbsBoundPair) -> EmptiableAbsBoundPair {
    let EmptiableAbsBoundPair::Bound(bounds) = bounds else {
        return EmptiableAbsBoundPair::Empty;
    };

    past_continuation_abs_bound_pair(bounds)
}

/// Returns the future continuation of the given [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_emptiable_abs_bound_pair(bounds: &EmptiableAbsBoundPair) -> EmptiableAbsBoundPair {
    let EmptiableAbsBoundPair::Bound(bounds) = bounds else {
        return EmptiableAbsBoundPair::Empty;
    };

    future_continuation_abs_bound_pair(bounds)
}

/// Returns the past continuation of the given [`BoundedAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_bounded_abs_interval(interval: &BoundedAbsInterval) -> HalfBoundedAbsInterval {
    HalfBoundedAbsInterval::new_from_time_and_inclusivity(
        interval.start_time(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    )
}

/// Returns the future continuation of the given [`BoundedAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_bounded_abs_interval(interval: &BoundedAbsInterval) -> HalfBoundedAbsInterval {
    HalfBoundedAbsInterval::new_from_time_and_inclusivity(
        interval.end_time(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    )
}

/// Returns the past continuation of the given [`RelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_rel_bound_pair(bounds: &RelBoundPair) -> EmptiableRelBoundPair {
    match bounds.rel_start() {
        RelStartBound::InfinitePast => EmptiableRelBoundPair::Empty,
        RelStartBound::Finite(finite_start) => {
            RelBoundPair::new(RelStartBound::InfinitePast, finite_start.opposite().to_end_bound()).to_emptiable()
        },
    }
}

/// Returns the future continuation of the given [`RelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_rel_bound_pair(bounds: &RelBoundPair) -> EmptiableRelBoundPair {
    match bounds.rel_end() {
        RelEndBound::InfiniteFuture => EmptiableRelBoundPair::Empty,
        RelEndBound::Finite(finite_end) => {
            RelBoundPair::new(finite_end.opposite().to_start_bound(), RelEndBound::InfiniteFuture).to_emptiable()
        },
    }
}

/// Returns the past continuation of the given [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_emptiable_rel_bound_pair(bounds: &EmptiableRelBoundPair) -> EmptiableRelBoundPair {
    let EmptiableRelBoundPair::Bound(bounds) = bounds else {
        return EmptiableRelBoundPair::Empty;
    };

    past_continuation_rel_bound_pair(bounds)
}

/// Returns the future continuation of the given [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_emptiable_rel_bound_pair(bounds: &EmptiableRelBoundPair) -> EmptiableRelBoundPair {
    let EmptiableRelBoundPair::Bound(bounds) = bounds else {
        return EmptiableRelBoundPair::Empty;
    };

    future_continuation_rel_bound_pair(bounds)
}

/// Returns the past continuation of the given [`BoundedRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn past_continuation_bounded_rel_interval(interval: &BoundedRelInterval) -> HalfBoundedRelInterval {
    HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        interval.start_offset(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    )
}

/// Returns the future continuation of the given [`BoundedRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn future_continuation_bounded_rel_interval(interval: &BoundedRelInterval) -> HalfBoundedRelInterval {
    HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        interval.end_offset(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    )
}

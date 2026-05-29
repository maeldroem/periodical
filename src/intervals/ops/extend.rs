//! Interval extension up to another interval
//!
//! Extends an interval up to another. The process takes the lowest start bound
//! of the two intervals and the highest end bound of the two intervals, then
//! creates a new interval spanning those two points.
//!
//! Regarding bound inclusivity, for each point we will get the bound
//! inclusivity of the interval from which the point was taken. If they were
//! equal, we choose the most inclusive bound.
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
//! # use periodical::intervals::ops::Extensible;
//! let first_interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 12:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let second_interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! assert_eq!(
//!     first_interval.extend(&second_interval),
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Capacity to extend an interval up to another
///
/// Extends an interval up to another. The process takes the lowest start bound
/// of the two intervals and the highest end bound of the two intervals, then
/// creates a new interval spanning those two points.
///
/// Regarding bound inclusivity, for each point we will get the bound
/// inclusivity of the interval from which the point was taken. If they were
/// equal, we choose the most inclusive bound.
pub trait Extensible<Rhs = Self> {
    /// Output type
    type Output;

    /// Creates an extended interval from the current one and given one
    ///
    /// Extends an interval up to another. The process takes the lowest start
    /// bound of the two intervals and the highest end bound of the two
    /// intervals, then creates a new interval spanning those two points.
    ///
    /// Regarding bound inclusivity, for each point we will get the bound
    /// inclusivity of the interval from which the point was taken. If they
    /// were equal, we choose the most inclusive bound.
    ///
    /// If both intervals are empty, the method just returns an empty interval.
    ///
    /// If one of the intervals is empty, the method just return a clone of the
    /// other non-empty interval.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::ops::Extensible;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.extend(&second_interval),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn extend(&self, rhs: &Rhs) -> Self::Output;
}

impl<Rhs> Extensible<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Extensible<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        extend_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Extensible<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        ))
    }
}

impl<Rhs> Extensible<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn extend(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(extend_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        ))
    }
}

impl Extensible<AbsoluteBoundPair> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &AbsoluteBoundPair) -> Self::Output {
        *self
    }
}

impl Extensible<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &EmptiableAbsoluteBoundPair) -> Self::Output {
        *self
    }
}

impl Extensible<AbsoluteInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &AbsoluteInterval) -> Self::Output {
        *self
    }
}

impl Extensible<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &BoundedAbsoluteInterval) -> Self::Output {
        *self
    }
}

impl Extensible<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &HalfBoundedAbsoluteInterval) -> Self::Output {
        *self
    }
}

impl Extensible<RelativeBoundPair> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &RelativeBoundPair) -> Self::Output {
        *self
    }
}

impl Extensible<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &EmptiableRelativeBoundPair) -> Self::Output {
        *self
    }
}

impl Extensible<RelativeInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &RelativeInterval) -> Self::Output {
        *self
    }
}

impl Extensible<BoundedRelativeInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &BoundedRelativeInterval) -> Self::Output {
        *self
    }
}

impl Extensible<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &HalfBoundedRelativeInterval) -> Self::Output {
        *self
    }
}

impl Extensible<UnboundedInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &UnboundedInterval) -> Self::Output {
        *self
    }
}

impl Extensible<EmptyInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn extend(&self, _rhs: &EmptyInterval) -> Self::Output {
        *self
    }
}

impl Extensible<AbsoluteBoundPair> for EmptyInterval {
    type Output = AbsoluteBoundPair;

    fn extend(&self, rhs: &AbsoluteBoundPair) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<EmptiableAbsoluteBoundPair> for EmptyInterval {
    type Output = EmptiableAbsoluteBoundPair;

    fn extend(&self, rhs: &EmptiableAbsoluteBoundPair) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<AbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn extend(&self, rhs: &AbsoluteInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<BoundedAbsoluteInterval> for EmptyInterval {
    type Output = BoundedAbsoluteInterval;

    fn extend(&self, rhs: &BoundedAbsoluteInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<HalfBoundedAbsoluteInterval> for EmptyInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn extend(&self, rhs: &HalfBoundedAbsoluteInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<RelativeBoundPair> for EmptyInterval {
    type Output = RelativeBoundPair;

    fn extend(&self, rhs: &RelativeBoundPair) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<EmptiableRelativeBoundPair> for EmptyInterval {
    type Output = EmptiableRelativeBoundPair;

    fn extend(&self, rhs: &EmptiableRelativeBoundPair) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<RelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn extend(&self, rhs: &RelativeInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<BoundedRelativeInterval> for EmptyInterval {
    type Output = BoundedRelativeInterval;

    fn extend(&self, rhs: &BoundedRelativeInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<HalfBoundedRelativeInterval> for EmptyInterval {
    type Output = HalfBoundedRelativeInterval;

    fn extend(&self, rhs: &HalfBoundedRelativeInterval) -> Self::Output {
        rhs.clone()
    }
}

impl Extensible<UnboundedInterval> for EmptyInterval {
    type Output = UnboundedInterval;

    fn extend(&self, rhs: &UnboundedInterval) -> Self::Output {
        *rhs
    }
}

impl Extensible<EmptyInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn extend(&self, _rhs: &EmptyInterval) -> Self::Output {
        *self
    }
}

/// Extends two [`AbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::extend) for more info.
#[must_use]
pub fn extend_abs_bound_pair(og_bounds: &AbsoluteBoundPair, other_bounds: &AbsoluteBoundPair) -> AbsoluteBoundPair {
    let new_start_bound = match (og_bounds.abs_start(), other_bounds.abs_start()) {
        (bound @ AbsoluteStartBound::InfinitePast, _) | (_, bound @ AbsoluteStartBound::InfinitePast) => bound,
        (og_bound @ AbsoluteStartBound::Finite(..), other_bound @ AbsoluteStartBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    let new_end_bound = match (og_bounds.abs_end(), other_bounds.abs_end()) {
        (bound @ AbsoluteEndBound::InfiniteFuture, _) | (_, bound @ AbsoluteEndBound::InfiniteFuture) => bound,
        (og_bound @ AbsoluteEndBound::Finite(..), other_bound @ AbsoluteEndBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    AbsoluteBoundPair::new(new_start_bound, new_end_bound)
}

/// Extends an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::extend) for more info.
#[must_use]
pub fn extend_abs_bound_pair_with_emptiable_abs_bound_pair(
    og_bounds: &AbsoluteBoundPair,
    other_bounds: &EmptiableAbsoluteBoundPair,
) -> AbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    extend_abs_bound_pair(og_bounds, other_non_empty_bounds)
}

/// Extends two [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::extend) for more info.
#[must_use]
pub fn extend_emptiable_abs_bound_pair(
    og_bounds: &EmptiableAbsoluteBoundPair,
    other_bounds: &EmptiableAbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    match (og_bounds, other_bounds) {
        (EmptiableAbsoluteBoundPair::Empty, EmptiableAbsoluteBoundPair::Empty) => EmptiableAbsoluteBoundPair::Empty,
        (EmptiableAbsoluteBoundPair::Empty, bound @ EmptiableAbsoluteBoundPair::Bound(..))
        | (bound @ EmptiableAbsoluteBoundPair::Bound(..), EmptiableAbsoluteBoundPair::Empty) => bound.clone(),
        (EmptiableAbsoluteBoundPair::Bound(og_bounds), EmptiableAbsoluteBoundPair::Bound(other_bounds)) => {
            EmptiableAbsoluteBoundPair::Bound(og_bounds.extend(other_bounds))
        },
    }
}

/// Extends two [`RelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::extend) for more info.
#[must_use]
pub fn extend_rel_bound_pair(og_bounds: &RelativeBoundPair, other_bounds: &RelativeBoundPair) -> RelativeBoundPair {
    let new_start_bound = match (og_bounds.rel_start(), other_bounds.rel_start()) {
        (bound @ RelativeStartBound::InfinitePast, _) | (_, bound @ RelativeStartBound::InfinitePast) => bound,
        (og_bound @ RelativeStartBound::Finite(..), other_bound @ RelativeStartBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
        },
    };

    let new_end_bound = match (og_bounds.rel_end(), other_bounds.rel_end()) {
        (bound @ RelativeEndBound::InfiniteFuture, _) | (_, bound @ RelativeEndBound::InfiniteFuture) => bound,
        (og_bound @ RelativeEndBound::Finite(..), other_bound @ RelativeEndBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    RelativeBoundPair::new(new_start_bound, new_end_bound)
}

/// Extends an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::extend) for more info.
#[must_use]
pub fn extend_rel_bound_pair_with_emptiable_rel_bound_pair(
    og_bounds: &RelativeBoundPair,
    other_bounds: &EmptiableRelativeBoundPair,
) -> RelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(other_non_empty_bounds) = other_bounds else {
        return og_bounds.clone();
    };

    extend_rel_bound_pair(og_bounds, other_non_empty_bounds)
}

/// Extends two [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::extend) for more info.
#[must_use]
pub fn extend_emptiable_rel_bound_pair(
    og_bounds: &EmptiableRelativeBoundPair,
    other_bounds: &EmptiableRelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    match (og_bounds, other_bounds) {
        (EmptiableRelativeBoundPair::Empty, EmptiableRelativeBoundPair::Empty) => EmptiableRelativeBoundPair::Empty,
        (EmptiableRelativeBoundPair::Empty, bound @ EmptiableRelativeBoundPair::Bound(..))
        | (bound @ EmptiableRelativeBoundPair::Bound(..), EmptiableRelativeBoundPair::Empty) => bound.clone(),
        (EmptiableRelativeBoundPair::Bound(og_bounds), EmptiableRelativeBoundPair::Bound(other_bounds)) => {
            EmptiableRelativeBoundPair::Bound(og_bounds.extend(other_bounds))
        },
    }
}

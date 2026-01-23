//! Fill gaps between non-overlapping intervals
//!
//! Use [`GapFillable::fill_gap`] to fill gaps between non-overlapping intervals.
//! This operation takes the first interval, provided by `self`, and extends it so that it fills the gap
//! up to the second interval.
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::fill_gap::GapFillable;
//! let first_interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! let second_interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! assert_eq!(
//!     first_interval.fill_gap(&second_interval),
//!     Ok(AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!             BoundInclusivity::Exclusive,
//!         )),
//!     )),
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfBoundedRelativeInterval, RelativeBounds, RelativeEndBound, RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{BoundedAbsoluteInterval, BoundedRelativeInterval, RelativeInterval};

/// Errors that can be produced when using [`GapFillable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GapFillError {
    /// The two given intervals were overlapping
    Overlap,
}

/// Capacity to fill gaps between non-overlapping intervals
///
/// Filling a gap returns a copy of the first interval, given by `self`, that fills the gap up to the second interval.
pub trait GapFillable<Rhs = Self> {
    /// Output type
    type Output;

    /// Fills the gap up the other interval
    ///
    /// Returns a copy of `self` that fills the gap up to the second interval.
    ///
    /// # Errors
    ///
    /// If the two intervals are overlapping, it result in [`GapFillError::Overlap`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::fill_gap::GapFillable;
    /// let first_interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let second_interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.fill_gap(&second_interval),
    ///     Ok(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///             BoundInclusivity::Exclusive,
    ///         )),
    ///     )),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError>;
}

impl<Rhs> GapFillable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(AbsoluteInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> GapFillable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(RelativeInterval::from)
    }
}

impl GapFillable<AbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &AbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<EmptiableAbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &EmptiableAbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<AbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &AbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &BoundedAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, _rhs: &HalfBoundedAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<RelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &RelativeBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<EmptiableRelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &EmptiableRelativeBounds) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<RelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &RelativeInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &BoundedRelativeInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, _rhs: &HalfBoundedRelativeInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<UnboundedInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn fill_gap(&self, _rhs: &UnboundedInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<EmptyInterval> for UnboundedInterval {
    type Output = EmptyInterval;

    fn fill_gap(&self, _rhs: &EmptyInterval) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl GapFillable<AbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &AbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<EmptiableAbsoluteBounds> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &EmptiableAbsoluteBounds) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<AbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &AbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Ok(rhs.clone())
    }
}

impl GapFillable<BoundedAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &BoundedAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<HalfBoundedAbsoluteInterval> for EmptyInterval {
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &HalfBoundedAbsoluteInterval) -> Result<Self::Output, GapFillError> {
        Ok(AbsoluteInterval::from(rhs.clone()))
    }
}

impl GapFillable<RelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &RelativeBounds) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<EmptiableRelativeBounds> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &EmptiableRelativeBounds) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<RelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &RelativeInterval) -> Result<Self::Output, GapFillError> {
        Ok(rhs.clone())
    }
}

impl GapFillable<BoundedRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &BoundedRelativeInterval) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<HalfBoundedRelativeInterval> for EmptyInterval {
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &HalfBoundedRelativeInterval) -> Result<Self::Output, GapFillError> {
        Ok(RelativeInterval::from(rhs.clone()))
    }
}

impl GapFillable<UnboundedInterval> for EmptyInterval {
    type Output = UnboundedInterval;

    fn fill_gap(&self, rhs: &UnboundedInterval) -> Result<Self::Output, GapFillError> {
        Ok(*rhs)
    }
}

impl GapFillable<EmptyInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn fill_gap(&self, rhs: &EmptyInterval) -> Result<Self::Output, GapFillError> {
        Ok(*rhs)
    }
}

/// Extends an [`AbsoluteBounds`] to fill the gap up to the other [`AbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::fill_gap) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_abs_bounds(a: &AbsoluteBounds, b: &AbsoluteBounds) -> Result<AbsoluteBounds, GapFillError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OutsideBefore`"
                );
            };

            let new_end_bound = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            Ok(a.grow_end(new_end_bound))
        },
        Dop::OutsideAfter => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OutsideAfter`"
                );
            };

            let new_start_bound = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            Ok(a.grow_start(new_start_bound))
        },
        _ => Err(GapFillError::Overlap),
    }
}

/// Extends an [`AbsoluteBounds`] to fill the gap up to the other [`EmptiableAbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::fill_gap) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<AbsoluteBounds, GapFillError> {
    let EmptiableAbsoluteBounds::Bound(b_abs_bounds) = b else {
        return Ok(a.clone());
    };

    fill_gap_abs_bounds(a, b_abs_bounds)
}

/// Extends an [`EmptiableAbsoluteBounds`] to fill the gap up to the other [`EmptiableAbsoluteBounds`]
///
/// See [module documentation](crate::intervals::ops::fill_gap) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<EmptiableAbsoluteBounds, GapFillError> {
    let EmptiableAbsoluteBounds::Bound(a_abs_bounds) = a else {
        return Ok(b.clone());
    };

    fill_gap_abs_bounds_with_emptiable_abs_bounds(a_abs_bounds, b).map(EmptiableAbsoluteBounds::from)
}

/// Extends a [`RelativeBounds`] to fill the gap up to the other [`RelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::fill_gap) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_rel_bounds(a: &RelativeBounds, b: &RelativeBounds) -> Result<RelativeBounds, GapFillError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OutsideBefore`"
                );
            };

            let new_end_bound = RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            Ok(a.grow_end(new_end_bound))
        },
        Dop::OutsideAfter => {
            let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OutsideAfter`"
                );
            };

            let new_start_bound = RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(), // So that it fully closes the gap
            ));

            Ok(a.grow_start(new_start_bound))
        },
        _ => Err(GapFillError::Overlap),
    }
}

/// Extends a [`RelativeBounds`] to fill the gap up to the other [`EmptiableRelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::fill_gap) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_rel_bounds_with_emptiable_rel_bounds(
    a: &RelativeBounds,
    b: &EmptiableRelativeBounds,
) -> Result<RelativeBounds, GapFillError> {
    let EmptiableRelativeBounds::Bound(b_rel_bounds) = b else {
        return Ok(a.clone());
    };

    fill_gap_rel_bounds(a, b_rel_bounds)
}

/// Extends an [`EmptiableRelativeBounds`] to fill the gap up to the other [`EmptiableRelativeBounds`]
///
/// See [module documentation](crate::intervals::ops::fill_gap) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_emptiable_rel_bounds(
    a: &EmptiableRelativeBounds,
    b: &EmptiableRelativeBounds,
) -> Result<EmptiableRelativeBounds, GapFillError> {
    let EmptiableRelativeBounds::Bound(a_rel_bounds) = a else {
        return Ok(b.clone());
    };

    fill_gap_rel_bounds_with_emptiable_rel_bounds(a_rel_bounds, b).map(EmptiableRelativeBounds::from)
}

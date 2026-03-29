//! Fill gaps between non-overlapping intervals
//!
//! Use [`GapFillable::fill_gap`] to fill gaps between non-overlapping
//! intervals. This operation takes the first interval, provided by `self`, and
//! extends it so that it fills the gap up to the second interval.
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::fill_gap::GapFillable;
//! let first_interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 10:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let second_interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 12:00:00[Europe/Oslo]"
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
//!     first_interval.fill_gap(&second_interval),
//!     Ok(AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new_with_inclusivity(
//!             "2025-01-01 12:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!             BoundInclusivity::Exclusive,
//!         )
//!         .to_end_bound(),
//!     )),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
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
use crate::intervals::meta::{HasBoundInclusivity, Interval};
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

/// Errors that can be produced when using [`GapFillable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GapFillError {
    /// The two given intervals were overlapping
    Overlap,
}

/// Capacity to fill gaps between non-overlapping intervals
///
/// Filling a gap returns a copy of the first interval, given by `self`, that
/// fills the gap up to the second interval.
pub trait GapFillable<Rhs = Self> {
    /// Output type
    type Output;

    /// Fills the gap up the other interval
    ///
    /// Returns a copy of `self` that fills the gap up to the second interval.
    ///
    /// # Errors
    ///
    /// If the two intervals are overlapping, it result in
    /// [`GapFillError::Overlap`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::fill_gap::GapFillable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
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
    ///     first_interval.fill_gap(&second_interval),
    ///     Ok(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError>;
}

impl<Rhs> GapFillable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for UnboundedInterval
where
    Rhs: Interval,
{
    type Output = UnboundedInterval;

    fn fill_gap(&self, _rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        Err(GapFillError::Overlap)
    }
}

impl<Rhs> GapFillable<Rhs> for EmptyInterval
where
    Rhs: Interval + Clone,
{
    type Output = Rhs;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillError> {
        Ok(rhs.clone())
    }
}

/// Extends an [`AbsoluteBoundPair`] to fill the gap up to the other
/// [`AbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &AbsoluteBoundPair,
) -> Result<AbsoluteBoundPair, GapFillError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
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
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
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

/// Extends an [`AbsoluteBoundPair`] to fill the gap up to the other
/// [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> Result<AbsoluteBoundPair, GapFillError> {
    let EmptiableAbsoluteBoundPair::Bound(b_abs_bound_pair) = b else {
        return Ok(a.clone());
    };

    fill_gap_abs_bound_pair(a, b_abs_bound_pair)
}

/// Extends an [`EmptiableAbsoluteBoundPair`] to fill the gap up to the other
/// [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> Result<EmptiableAbsoluteBoundPair, GapFillError> {
    let EmptiableAbsoluteBoundPair::Bound(a_abs_bound_pair) = a else {
        return Ok(b.clone());
    };

    fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(a_abs_bound_pair, b).map(EmptiableAbsoluteBoundPair::from)
}

/// Extends a [`RelativeBoundPair`] to fill the gap up to the other
/// [`RelativeBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &RelativeBoundPair,
) -> Result<RelativeBoundPair, GapFillError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
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
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
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

/// Extends a [`RelativeBoundPair`] to fill the gap up to the other
/// [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> Result<RelativeBoundPair, GapFillError> {
    let EmptiableRelativeBoundPair::Bound(b_rel_bound_pair) = b else {
        return Ok(a.clone());
    };

    fill_gap_rel_bound_pair(a, b_rel_bound_pair)
}

/// Extends an [`EmptiableRelativeBoundPair`] to fill the gap up to the other
/// [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillError::Overlap`]
pub fn fill_gap_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> Result<EmptiableRelativeBoundPair, GapFillError> {
    let EmptiableRelativeBoundPair::Bound(a_rel_bound_pair) = a else {
        return Ok(b.clone());
    };

    fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(a_rel_bound_pair, b).map(EmptiableRelativeBoundPair::from)
}

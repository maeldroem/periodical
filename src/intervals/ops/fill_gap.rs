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
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::fill_gap::GapFillable;
//! let first_interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 10:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let second_interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 12:00:00[Europe/Oslo]"
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
//!     first_interval.fill_gap(&second_interval),
//!     Ok(AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new_with_incl(
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

use std::error::Error;
use std::fmt::Display;

use super::grow::{GrowableEndBound, GrowableStartBound};
use super::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, Interval};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::EmptyInterval;

/// The two given intervals were overlapping when using [`GapFillable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GapFillOverlapFoundError;

impl Display for GapFillOverlapFoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "The two given intervals were overlapping")
    }
}

impl Error for GapFillOverlapFoundError {}

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
    /// If the two intervals are overlapping, it result in [`GapFillOverlapFoundError`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::fill_gap::GapFillable;
    /// let first_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
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
    ///     first_interval.fill_gap(&second_interval),
    ///     Ok(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new_with_incl(
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
    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError>;
}

impl<Rhs> GapFillable<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = AbsInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = AbsInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> GapFillable<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for EmptiableRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = RelInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = RelInterval;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(Self::Output::from)
    }
}

impl<Rhs> GapFillable<Rhs> for EmptyInterval
where
    Rhs: Interval + Clone,
{
    type Output = Rhs;

    fn fill_gap(&self, rhs: &Rhs) -> Result<Self::Output, GapFillOverlapFoundError> {
        Ok(rhs.clone())
    }
}

/// Extends an [`AbsBoundPair`] to fill the gap up to the other
/// [`AbsBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillOverlapFoundError`]
pub fn fill_gap_abs_bound_pair(a: &AbsBoundPair, b: &AbsBoundPair) -> Result<AbsBoundPair, GapFillOverlapFoundError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let AbsStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
                );
            };

            let new_end_bound = AbsFiniteBoundPos::new_with_incl(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            Ok(a.grow_end(new_end_bound))
        },
        Dop::OutsideAfter => {
            let AbsEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
                );
            };

            let new_start_bound = AbsFiniteBoundPos::new_with_incl(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            Ok(a.grow_start(new_start_bound))
        },
        _ => Err(GapFillOverlapFoundError),
    }
}

/// Extends an [`AbsBoundPair`] to fill the gap up to the other
/// [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillOverlapFoundError`]
pub fn fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> Result<AbsBoundPair, GapFillOverlapFoundError> {
    let EmptiableAbsBoundPair::Bound(b_abs_bound_pair) = b else {
        return Ok(a.clone());
    };

    fill_gap_abs_bound_pair(a, b_abs_bound_pair)
}

/// Extends an [`EmptiableAbsBoundPair`] to fill the gap up to the other
/// [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillOverlapFoundError`]
pub fn fill_gap_emptiable_abs_bound_pair(
    a: &EmptiableAbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> Result<EmptiableAbsBoundPair, GapFillOverlapFoundError> {
    let EmptiableAbsBoundPair::Bound(a_abs_bound_pair) = a else {
        return Ok(b.clone());
    };

    fill_gap_abs_bound_pair_with_emptiable_abs_bound_pair(a_abs_bound_pair, b).map(EmptiableAbsBoundPair::from)
}

/// Extends a [`RelBoundPair`] to fill the gap up to the other
/// [`RelBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillOverlapFoundError`]
pub fn fill_gap_rel_bound_pair(a: &RelBoundPair, b: &RelBoundPair) -> Result<RelBoundPair, GapFillOverlapFoundError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::Strict);

    match overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore => {
            let RelStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OutsideBefore`"
                );
            };

            let new_end_bound = RelFiniteBoundPos::new_with_incl(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_end_bound();

            Ok(a.grow_end(new_end_bound))
        },
        Dop::OutsideAfter => {
            let RelEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OutsideAfter`"
                );
            };

            let new_start_bound = RelFiniteBoundPos::new_with_incl(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(), // So that it fully closes the gap
            )
            .to_start_bound();

            Ok(a.grow_start(new_start_bound))
        },
        _ => Err(GapFillOverlapFoundError),
    }
}

/// Extends a [`RelBoundPair`] to fill the gap up to the other
/// [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillOverlapFoundError`]
pub fn fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelBoundPair,
    b: &EmptiableRelBoundPair,
) -> Result<RelBoundPair, GapFillOverlapFoundError> {
    let EmptiableRelBoundPair::Bound(b_rel_bound_pair) = b else {
        return Ok(a.clone());
    };

    fill_gap_rel_bound_pair(a, b_rel_bound_pair)
}

/// Extends an [`EmptiableRelBoundPair`] to fill the gap up to the other
/// [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
///
/// # Errors
///
/// If the given bounds overlap, it results in [`GapFillOverlapFoundError`]
pub fn fill_gap_emptiable_rel_bound_pair(
    a: &EmptiableRelBoundPair,
    b: &EmptiableRelBoundPair,
) -> Result<EmptiableRelBoundPair, GapFillOverlapFoundError> {
    let EmptiableRelBoundPair::Bound(a_rel_bound_pair) = a else {
        return Ok(b.clone());
    };

    fill_gap_rel_bound_pair_with_emptiable_rel_bound_pair(a_rel_bound_pair, b).map(EmptiableRelBoundPair::from)
}

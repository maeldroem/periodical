//! Set operations on intervals
//!
//! The main set operations are implemented:
//!
//! - Unions, with [`Unitable`]
//! - Intersections, with [`Intersectable`]
//! - Differences, with [`Differentiable`]
//! - Symmetric differences, with [`SymmetricallyDifferentiable`]

use super::abridge::Abridgable;
use super::extend::Extensible;
use super::overlap::CanPositionOverlap;

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteInterval, BoundedAbsoluteInterval, EmptiableAbsoluteBoundPair, EmptiableAbsoluteInterval, HalfBoundedAbsoluteInterval, HasAbsoluteBoundPair, HasEmptiableAbsoluteBoundPair
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::Complementable;
use crate::intervals::ops::overlap::{OverlapRule, OverlapRuleSet};
use crate::intervals::ops::remove_overlap::{OverlapRemovable, OverlapRemovalErr, OverlapRemovalResult};
use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBoundPair, EmptiableRelativeInterval, HalfBoundedRelativeInterval, HasEmptiableRelativeBoundPair, HasRelativeBoundPair, RelativeBoundPair, RelativeInterval
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::{ComplementResult, DifferenceResult, IntersectionResult, SymmetricDifferenceResult, UnionResult};

/// Capacity to unite an interval with another
///
/// # Examples
///
/// ## Unitable intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::UnionResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::set_ops::Unitable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.unite(&second_interval),
///     UnionResult::United(AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_start_bound(),
///         AbsoluteFiniteBound::new(
///             "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_end_bound(),
///     )),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::UnionResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::set_ops::Unitable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.unite(&second_interval),
///     UnionResult::Separate,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Unitable<Rhs = Self> {
    /// Output type
    type Output;

    /// Unites two intervals using default overlap rules
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::UnionResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::set_ops::Unitable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.unite(&second_interval),
    ///     UnionResult::United(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output>;

    /// Unites two intervals using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::UnionResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::extend::Extensible;
    /// # use periodical::intervals::ops::set_ops::Unitable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let union_closure = |
    ///     a: &AbsoluteBoundPair,
    ///     b: &AbsoluteBoundPair,
    /// | -> UnionResult<AbsoluteBoundPair> {
    ///     // Always unite
    ///     UnionResult::United(a.extend(b))
    /// };
    ///
    /// assert_eq!(
    ///     first_interval.unite_with(&second_interval, union_closure),
    ///     UnionResult::United(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn unite_with<F>(&self, rhs: &Rhs, mut f: F) -> UnionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> UnionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(AbsoluteInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(AbsoluteInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(RelativeInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(RelativeInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for UnboundedInterval
where
    Rhs: Interval,
{
    type Output = UnboundedInterval;

    fn unite(&self, _rhs: &Rhs) -> UnionResult<Self::Output> {
        UnionResult::United(*self)
    }
}

impl<Rhs> Unitable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = Rhs;

    fn unite(&self, _rhs: &Rhs) -> UnionResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be united with anything
        UnionResult::Separate
    }
}

/// Unites two [`AbsoluteBoundPair`]
#[must_use]
pub fn unite_abs_bound_pair(a: &AbsoluteBoundPair, b: &AbsoluteBoundPair) -> UnionResult<AbsoluteBoundPair> {
    // We use the lenient rule set with allow adjacency rule so that "touching" intervals are united together
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> UnionResult<AbsoluteBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> UnionResult<EmptiableAbsoluteBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`RelativeBoundPair`]
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_rel_bound_pair(a: &RelativeBoundPair, b: &RelativeBoundPair) -> UnionResult<RelativeBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> UnionResult<RelativeBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> UnionResult<EmptiableRelativeBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Capacity to intersect an interval with another
///
/// # Examples
///
/// ## Intersectable intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::IntersectionResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::set_ops::Intersectable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.intersect(&second_interval),
///     IntersectionResult::Intersected(AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new(
///             "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_start_bound(),
///         AbsoluteFiniteBound::new(
///             "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_end_bound(),
///     )),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::IntersectionResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::set_ops::Intersectable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.intersect(&second_interval),
///     IntersectionResult::Separate,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Intersectable<Rhs = Self> {
    /// Output type
    type Output;

    /// Intersects two intervals using the default overlap rules
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::IntersectionResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::set_ops::Intersectable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.intersect(&second_interval),
    ///     IntersectionResult::Intersected(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output>;

    /// Intersects two intervals using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::IntersectionResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::abridge::Abridgable;
    /// # use periodical::intervals::ops::set_ops::Intersectable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let intersection_closure = |
    ///     a: &AbsoluteBoundPair,
    ///     b: &AbsoluteBoundPair,
    /// | -> IntersectionResult<AbsoluteBoundPair> {
    ///     // Always abridge intervals
    ///     if let EmptiableAbsoluteBoundPair::Bound(abridged) = a.abridge(b) {
    ///         IntersectionResult::Intersected(abridged)
    ///     } else {
    ///         IntersectionResult::Separate
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     first_interval.intersect_with(&second_interval, intersection_closure),
    ///     IntersectionResult::Intersected(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         ).to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn intersect_with<F>(&self, rhs: &Rhs, mut f: F) -> IntersectionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> IntersectionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<AbsoluteBoundPair> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &AbsoluteBoundPair) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &EmptiableAbsoluteBoundPair) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<AbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &AbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &BoundedAbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &HalfBoundedAbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<RelativeBoundPair> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &RelativeBoundPair) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &EmptiableRelativeBoundPair) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<RelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &RelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &BoundedRelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &HalfBoundedRelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<UnboundedInterval> for UnboundedInterval {
    type Output = EmptyInterval;

    fn intersect(&self, _rhs: &UnboundedInterval) -> IntersectionResult<Self::Output> {
        IntersectionResult::Intersected(EmptyInterval)
    }
}

impl Intersectable<EmptyInterval> for UnboundedInterval {
    type Output = ();

    fn intersect(&self, _rhs: &EmptyInterval) -> IntersectionResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be used in an intersection
        IntersectionResult::Separate
    }
}

impl<Rhs> Intersectable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = EmptyInterval;

    fn intersect(&self, _rhs: &Rhs) -> IntersectionResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be used in an intersection
        IntersectionResult::Separate
    }
}

/// Intersects two [`AbsoluteBoundPair`]
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableAbsoluteBoundPair::Empty`]
#[must_use]
pub fn intersect_abs_bound_pair(a: &AbsoluteBoundPair, b: &AbsoluteBoundPair) -> IntersectionResult<AbsoluteBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableAbsoluteBoundPair::Empty`]
#[must_use]
pub fn intersect_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> IntersectionResult<AbsoluteBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
#[must_use]
pub fn intersect_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> IntersectionResult<EmptiableAbsoluteBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects two [`RelativeBoundPair`]
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableRelativeBoundPair::Empty`]
#[must_use]
pub fn intersect_rel_bound_pair(a: &RelativeBoundPair, b: &RelativeBoundPair) -> IntersectionResult<RelativeBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableRelativeBoundPair::Empty`]
#[must_use]
pub fn intersect_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> IntersectionResult<RelativeBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
#[must_use]
pub fn intersect_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> IntersectionResult<EmptiableRelativeBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Capacity to differentiate an interval with another
///
/// _Differentiate_, in this context, means the finding the [set difference] of an interval with another,
/// the latter being used as the _remover_ of the former.
///
/// [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
///
/// # Examples
///
/// ## Differentiating intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::DifferenceResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::set_ops::Differentiable;
/// let interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let remover = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.differentiate(&remover),
///     DifferenceResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_start_bound(),
///         AbsoluteFiniteBound::new_with_inclusivity(
///             "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///             BoundInclusivity::Exclusive,
///         ).to_end_bound(),
///     ))),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::DifferenceResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
/// # use periodical::intervals::ops::set_ops::Differentiable;
/// let interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let remover = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 13:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.differentiate(&remover),
///     DifferenceResult::Separate,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Differentiable<Rhs = Self> {
    /// Output type
    type Output;

    /// Differentiates the interval with the given one using default overlap rules
    ///
    /// `self` is the one differentiated by the given other interval: same operand order as the mathematical
    /// expression for a set difference.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::DifferenceResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::set_ops::Differentiable;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let remover = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.differentiate(&remover),
    ///     DifferenceResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         ).to_end_bound(),
    ///     ))),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output>;

    /// Differentiates the interval with the given one using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::DifferenceResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
    /// # use periodical::intervals::ops::remove_overlap::OverlapRemovable;
    /// # use periodical::intervals::ops::set_ops::Differentiable;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let remover = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// // Only differentiate if it just crosses the other
    /// let difference_closure = |
    ///     a: &AbsoluteBoundPair,
    ///     b: &AbsoluteBoundPair,
    /// | -> DifferenceResult<EmptiableAbsoluteBoundPair> {
    ///     match a.disambiguated_overlap_position(b, OverlapRuleSet::Strict) {
    ///         Ok(DisambiguatedOverlapPosition::CrossesStart | DisambiguatedOverlapPosition::CrossesEnd) => {
    ///             DifferenceResult::Single(
    ///                 a
    ///                 .remove_overlap(b)
    ///                 .expect("They overlap already")
    ///                 .single()
    ///                 .expect("Since they only cross each other, only a single element will be produced")
    ///             )
    ///         },
    ///         _ => DifferenceResult::Separate,
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     interval.differentiate_with(&remover, difference_closure),
    ///     DifferenceResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         ).to_end_bound(),
    ///     ))),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn differentiate_with<F>(&self, rhs: &Rhs, mut f: F) -> DifferenceResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> DifferenceResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Differentiable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteBoundPair;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeBoundPair;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl Differentiable<AbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn differentiate(&self, rhs: &AbsoluteBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_difference(Self::Output::from)
    }
}

impl Differentiable<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn differentiate(&self, rhs: &EmptiableAbsoluteBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl Differentiable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn differentiate(&self, rhs: &BoundedAbsoluteInterval) -> DifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => DifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => DifferenceResult::Split(split_before, split_after),
        }
    }
}

impl Differentiable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn differentiate(&self, rhs: &HalfBoundedAbsoluteInterval) -> DifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => DifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => DifferenceResult::Split(split_before, split_after),
        }
    }
}

impl Differentiable<RelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn differentiate(&self, rhs: &RelativeBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_difference(Self::Output::from)
    }
}

impl Differentiable<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn differentiate(&self, rhs: &EmptiableRelativeBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl Differentiable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = HalfBoundedRelativeInterval;

    fn differentiate(&self, rhs: &BoundedRelativeInterval) -> DifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => DifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => DifferenceResult::Split(split_before, split_after),
        }
    }
}

impl Differentiable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = HalfBoundedRelativeInterval;

    fn differentiate(&self, rhs: &HalfBoundedRelativeInterval) -> DifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => DifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => DifferenceResult::Split(split_before, split_after),
        }
    }
}

impl Differentiable<UnboundedInterval> for UnboundedInterval {
    type Output = EmptyInterval;

    fn differentiate(&self, _rhs: &UnboundedInterval) -> DifferenceResult<Self::Output> {
        DifferenceResult::Single(EmptyInterval)
    }
}

impl Differentiable<EmptyInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn differentiate(&self, _rhs: &EmptyInterval) -> DifferenceResult<Self::Output> {
        DifferenceResult::Single(UnboundedInterval)
    }
}

impl<Rhs> Differentiable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = ();

    fn differentiate(&self, _rhs: &Rhs) -> DifferenceResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be used in a difference
        DifferenceResult::Separate
    }
}

/// Differentiates an [`AbsoluteBoundPair`] with another one
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_abs_bound_pair(
    og_bounds: &AbsoluteBoundPair,
    other_bounds: &AbsoluteBoundPair,
) -> DifferenceResult<EmptiableAbsoluteBoundPair> {
    if !og_bounds.simple_overlaps(other_bounds) {
        return DifferenceResult::Separate;
    }

    match og_bounds.remove_overlap(other_bounds) {
        Ok(overlap_removal_res) => match overlap_removal_res {
            OverlapRemovalResult::Single(single) => DifferenceResult::Single(single),
            OverlapRemovalResult::Split(s1, s2) => DifferenceResult::Split(s1, s2),
        },
        Err(OverlapRemovalErr::NoOverlap) => unreachable!("Overlap check already happened earlier"),
    }
}

/// Differentiates an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
    og_bounds: &AbsoluteBoundPair,
    other_bounds: &EmptiableAbsoluteBoundPair,
) -> DifferenceResult<EmptiableAbsoluteBoundPair> {
    let EmptiableAbsoluteBoundPair::Bound(other_bounds) = other_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_abs_bound_pair(og_bounds, other_bounds)
}

/// Differentiates an [`EmptiableAbsoluteBoundPair`] with another one
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_emptiable_abs_bound_pair(
    og_bounds: &EmptiableAbsoluteBoundPair,
    other_bounds: &EmptiableAbsoluteBoundPair,
) -> DifferenceResult<EmptiableAbsoluteBoundPair> {
    let EmptiableAbsoluteBoundPair::Bound(og_bounds) = og_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(og_bounds, other_bounds)
}

/// Differentiates an [`RelativeBoundPair`] with another one
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_rel_bound_pair(
    og_bounds: &RelativeBoundPair,
    other_bounds: &RelativeBoundPair,
) -> DifferenceResult<EmptiableRelativeBoundPair> {
    if !og_bounds.simple_overlaps(other_bounds) {
        return DifferenceResult::Separate;
    }

    match og_bounds.remove_overlap(other_bounds) {
        Ok(overlap_removal_res) => match overlap_removal_res {
            OverlapRemovalResult::Single(single) => DifferenceResult::Single(single),
            OverlapRemovalResult::Split(s1, s2) => DifferenceResult::Split(s1, s2),
        },
        Err(OverlapRemovalErr::NoOverlap) => unreachable!("Overlap check already happened earlier"),
    }
}

/// Differentiates an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
    og_bounds: &RelativeBoundPair,
    other_bounds: &EmptiableRelativeBoundPair,
) -> DifferenceResult<EmptiableRelativeBoundPair> {
    let EmptiableRelativeBoundPair::Bound(other_bounds) = other_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_rel_bound_pair(og_bounds, other_bounds)
}

/// Differentiates an [`EmptiableRelativeBoundPair`] with another one
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_emptiable_rel_bound_pair(
    og_bounds: &EmptiableRelativeBoundPair,
    other_bounds: &EmptiableRelativeBoundPair,
) -> DifferenceResult<EmptiableRelativeBoundPair> {
    let EmptiableRelativeBoundPair::Bound(og_bounds) = og_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(og_bounds, other_bounds)
}

/// Capacity to symmetrically differentiate (a.k.a. XOR) an interval with another
///
/// Creates a [symmetric difference] between the two given intervals.
///
/// [symmetric difference]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
///
/// # Examples
///
/// ## Symmetrically differentiable intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::SymmetricDifferenceResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.symmetrically_differentiate(&second_interval),
///     SymmetricDifferenceResult::Split(
///         EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
///             AbsoluteFiniteBound::new(
///                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///             ).to_start_bound(),
///             AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///                 BoundInclusivity::Exclusive,
///             ).to_end_bound(),
///         )),
///         EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
///             AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///                 BoundInclusivity::Exclusive,
///             ).to_start_bound(),
///             AbsoluteFiniteBound::new(
///                 "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///             ).to_end_bound(),
///         )),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::SymmetricDifferenceResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
/// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.symmetrically_differentiate(&second_interval),
///     SymmetricDifferenceResult::Separate,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait SymmetricallyDifferentiable<Rhs = Self> {
    /// Output type
    type Output;

    /// Symmetrically differentiates the two intervals using the default overlap rules
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.symmetrically_differentiate(&second_interval),
    ///     SymmetricDifferenceResult::Split(
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBound::new(
    ///                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             ).to_start_bound(),
    ///             AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_end_bound(),
    ///         ).to_emptiable(),
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_start_bound(),
    ///             AbsoluteFiniteBound::new(
    ///                 "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             ).to_end_bound(),
    ///         ).to_emptiable(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output>;

    /// Symmetrically differentiates the two intervals using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
    /// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// // Only symmetrical differentiate intervals that crosses
    /// let symmetric_difference_closure = |
    ///     a: &AbsoluteBoundPair,
    ///     b: &AbsoluteBoundPair,
    /// | -> SymmetricDifferenceResult<EmptiableAbsoluteBoundPair> {
    ///     match a.disambiguated_overlap_position(b, OverlapRuleSet::Strict) {
    ///         Ok(DisambiguatedOverlapPosition::CrossesStart | DisambiguatedOverlapPosition::CrossesEnd) => {
    ///             a.symmetrically_differentiate(b)
    ///         },
    ///         _ => SymmetricDifferenceResult::Separate,
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     first_interval.symmetrically_differentiate_with(&second_interval, symmetric_difference_closure),
    ///     SymmetricDifferenceResult::Split(
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBound::new(
    ///                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             ).to_start_bound(),
    ///             AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_end_bound(),
    ///         ).to_emptiable(),
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             ).to_start_bound(),
    ///             AbsoluteFiniteBound::new(
    ///                 "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             ).to_end_bound(),
    ///         ).to_emptiable(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn symmetrically_differentiate_with<F>(&self, rhs: &Rhs, mut f: F) -> SymmetricDifferenceResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> SymmetricDifferenceResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteBoundPair;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeBoundPair;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<AbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &AbsoluteBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair(&self.abs_bound_pair(), rhs).map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableAbsoluteBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<AbsoluteInterval> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &AbsoluteInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &BoundedAbsoluteInterval) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => SymmetricDifferenceResult::Split(split_before, split_after),
        }
    }
}

impl SymmetricallyDifferentiable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn symmetrically_differentiate(
        &self,
        rhs: &HalfBoundedAbsoluteInterval,
    ) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => SymmetricDifferenceResult::Split(split_before, split_after),
        }
    }
}

impl SymmetricallyDifferentiable<RelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &RelativeBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair(&self.rel_bound_pair(), rhs).map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableRelativeBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<RelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &RelativeInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableRelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableRelativeInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = HalfBoundedRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &BoundedRelativeInterval) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => SymmetricDifferenceResult::Split(split_before, split_after),
        }
    }
}

impl SymmetricallyDifferentiable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = HalfBoundedRelativeInterval;

    fn symmetrically_differentiate(
        &self,
        rhs: &HalfBoundedRelativeInterval,
    ) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => SymmetricDifferenceResult::Split(split_before, split_after),
        }
    }
}

impl SymmetricallyDifferentiable<UnboundedInterval> for UnboundedInterval {
    type Output = EmptyInterval;

    fn symmetrically_differentiate(&self, _rhs: &UnboundedInterval) -> SymmetricDifferenceResult<Self::Output> {
        SymmetricDifferenceResult::Single(EmptyInterval)
    }
}

impl SymmetricallyDifferentiable<EmptyInterval> for UnboundedInterval {
    type Output = ();

    fn symmetrically_differentiate(&self, _rhs: &EmptyInterval) -> SymmetricDifferenceResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be differentiated with anything
        SymmetricDifferenceResult::Separate
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = ();

    fn symmetrically_differentiate(&self, _rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be differentiated with anything
        SymmetricDifferenceResult::Separate
    }
}

/// Symmetrically differentiates two [`AbsoluteBoundPair`]
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &AbsoluteBoundPair,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBoundPair> {
    if !a.simple_overlaps(b) {
        return SymmetricDifferenceResult::Separate;
    }

    let diff_a_with_b = match a.remove_overlap(b) {
        Ok(a_removed_b) => a_removed_b,
        Err(OverlapRemovalErr::NoOverlap) => unreachable!("Overlap check already happened earlier"),
    };
    let diff_b_with_a = match b.remove_overlap(a) {
        Ok(b_removed_a) => b_removed_a,
        Err(OverlapRemovalErr::NoOverlap) => unreachable!("Overlap check already happened earlier"),
    };

    match (diff_a_with_b, diff_b_with_a) {
        (
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableAbsoluteBoundPair::Empty),
        (OverlapRemovalResult::Single(single_diff), OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty), OverlapRemovalResult::Single(single_diff)) => {
            SymmetricDifferenceResult::Single(single_diff)
        },
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (OverlapRemovalResult::Split(split1, split2), OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty), OverlapRemovalResult::Split(split1, split2)) => {
            SymmetricDifferenceResult::Split(split1, split2)
        },
        (OverlapRemovalResult::Split(..), _) | (_, OverlapRemovalResult::Split(..)) => {
            unreachable!(
                "No possible interval configuration exist where A \\ B (A diff B) returns a `Split` result, \
                but at the same time B \\ A (B diff A) returns anything other than an empty interval"
            );
        },
    }
}

/// Symmetrically differentiates an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBoundPair> {
    let EmptiableAbsoluteBoundPair::Bound(b) = b else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_abs_bound_pair(a, b)
}

/// Symmetrically differentiates two [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBoundPair> {
    let EmptiableAbsoluteBoundPair::Bound(a) = a else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(a, b)
}

/// Symmetrically differentiates two [`RelativeBoundPair`]
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &RelativeBoundPair,
) -> SymmetricDifferenceResult<EmptiableRelativeBoundPair> {
    if !a.simple_overlaps(b) {
        return SymmetricDifferenceResult::Separate;
    }

    let diff_a_with_b = match a.remove_overlap(b) {
        Ok(a_removed_b) => a_removed_b,
        Err(OverlapRemovalErr::NoOverlap) => unreachable!("Overlap check already happened earlier"),
    };
    let diff_b_with_a = match b.remove_overlap(a) {
        Ok(b_removed_a) => b_removed_a,
        Err(OverlapRemovalErr::NoOverlap) => unreachable!("Overlap check already happened earlier"),
    };

    match (diff_a_with_b, diff_b_with_a) {
        (
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableRelativeBoundPair::Empty),
        (OverlapRemovalResult::Single(single_diff), OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty), OverlapRemovalResult::Single(single_diff)) => {
            SymmetricDifferenceResult::Single(single_diff)
        },
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (OverlapRemovalResult::Split(split1, split2), OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty), OverlapRemovalResult::Split(split1, split2)) => {
            SymmetricDifferenceResult::Split(split1, split2)
        },
        (OverlapRemovalResult::Split(..), _) | (_, OverlapRemovalResult::Split(..)) => {
            unreachable!(
                "No possible interval configuration exist where A \\ B (A diff B) returns a `Split` result, \
                but at the same time B \\ A (B diff A) returns anything other than an empty interval"
            );
        },
    }
}

/// Symmetrically differentiates an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> SymmetricDifferenceResult<EmptiableRelativeBoundPair> {
    let EmptiableRelativeBoundPair::Bound(b) = b else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_rel_bound_pair(a, b)
}

/// Symmetrically differentiates two [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> SymmetricDifferenceResult<EmptiableRelativeBoundPair> {
    let EmptiableRelativeBoundPair::Bound(a) = a else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(a, b)
}

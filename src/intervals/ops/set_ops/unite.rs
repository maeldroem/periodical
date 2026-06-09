//! Union between two intervals

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsInterval,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::extend::Extensible;
use crate::intervals::ops::overlap::{CanPositionOverlap, OverlapRule, OverlapRuleSet};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelInterval,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::UnionResult;

/// Capacity to unite an interval with another
///
/// # Examples
///
/// ## Unitable intervals
///
/// ```ignore
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::ops::UnionResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::set_ops::Unitable;
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
///     AbsFiniteBoundPos::new("2025-01-01 14:00:00Z".parse::<Timestamp>()?).to_end_bound(),
/// );
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new("2025-01-01 12:00:00Z".parse::<Timestamp>()?).to_start_bound(),
///     AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.unite(&second_interval),
///     UnionResult::United(AbsBoundPair::new(
///         AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
///         AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
///     )),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```ignore
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::ops::UnionResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::set_ops::Unitable;
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
///     AbsFiniteBoundPos::new("2025-01-01 12:00:00Z".parse::<Timestamp>()?).to_end_bound(),
/// );
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new("2025-01-01 14:00:00Z".parse::<Timestamp>()?).to_start_bound(),
///     AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.unite(&second_interval),
///     UnionResult::Separate,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Unitable<Rhs = Self> {
    /// Type of the resulting united interval
    type Output;

    /// Unites two intervals using default overlap rules
    ///
    /// # Examples
    ///
    /// ```ignore
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::ops::UnionResult;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::set_ops::Unitable;
    /// let first_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 14:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 12:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.unite(&second_interval),
    ///     UnionResult::United(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///         AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
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
    /// ```ignore
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::ops::UnionResult;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::extend::Extensible;
    /// # use periodical::intervals::ops::set_ops::Unitable;
    /// let first_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 12:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 14:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// let union_closure = |a: &AbsBoundPair, b: &AbsBoundPair| -> UnionResult<AbsBoundPair> {
    ///     // Always unite
    ///     UnionResult::United(a.extend(b))
    /// };
    ///
    /// assert_eq!(
    ///     first_interval.unite_with(&second_interval, union_closure),
    ///     UnionResult::United(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///         AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
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

impl<Rhs> Unitable<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = AbsInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(AbsInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = AbsInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(AbsInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = RelInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(RelInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = RelInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(RelInterval::from)
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

/// Unites two [`AbsBoundPair`]
#[must_use]
pub fn unite_abs_bound_pair(a: &AbsBoundPair, b: &AbsBoundPair) -> UnionResult<AbsBoundPair> {
    // We use the lenient rule set with allow adjacency rule so that "touching"
    // intervals are united together
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    todo!("wait for extend to be fixed before uncommenting");
    // UnionResult::United(a.extend(b))
}

/// Unites an [`AbsBoundPair`] with an [`EmptiableAbsBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> UnionResult<AbsBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    todo!("wait for extend to be fixed before uncommenting");
    // UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableAbsBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_emptiable_abs_bound_pair(
    a: &EmptiableAbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> UnionResult<EmptiableAbsBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    todo!("wait for extend to be fixed before uncommenting");
    // UnionResult::United(a.extend(b))
}

/// Unites two [`RelBoundPair`]
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_rel_bound_pair(a: &RelBoundPair, b: &RelBoundPair) -> UnionResult<RelBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    todo!("wait for extend to be fixed before uncommenting");
    // UnionResult::United(a.extend(b))
}

/// Unites an [`RelBoundPair`] with an [`EmptiableRelBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelBoundPair,
    b: &EmptiableRelBoundPair,
) -> UnionResult<RelBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    todo!("wait for extend to be fixed before uncommenting");
    // UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableRelBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_emptiable_rel_bound_pair(
    a: &EmptiableRelBoundPair,
    b: &EmptiableRelBoundPair,
) -> UnionResult<EmptiableRelBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    todo!("wait for extend to be fixed before uncommenting");
    // UnionResult::United(a.extend(b))
}

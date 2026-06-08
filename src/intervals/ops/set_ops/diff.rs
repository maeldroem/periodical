//! Difference between two intervals

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
use crate::intervals::ops::complement::Complementable;
use crate::intervals::ops::overlap::CanPositionOverlap;
use crate::intervals::ops::remove_overlap::{
    OverlapRemovable,
    OverlapRemovalNoOverlapFoundError,
    OverlapRemovalResult,
};
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
use crate::ops::{ComplementResult, DifferenceResult};

/// Capacity to differentiate an interval with another
///
/// _Differentiate_, in this context, means the finding the [set difference] of
/// an interval with another, the latter being used as the _remover_ of the
/// former.
///
/// [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1355557106#Relative_complement
///
/// # Examples
///
/// ## Differentiating intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::ops::DifferenceResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::set_ops::Differentiable;
/// let interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 14:00:00Z".parse::<Timestamp>()?,
///     ).to_end_bound(),
/// );
///
/// let remover = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 10:00:00Z".parse::<Timestamp>()?,
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 18:00:00Z".parse::<Timestamp>()?,
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.differentiate(&remover),
///     DifferenceResult::Single(AbsBoundPair::new(
///         AbsFiniteBoundPos::new(
///             "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
///         ).to_start_bound(),
///         AbsFiniteBoundPos::new_with_incl(
///             "2025-01-01 10:00:00Z".parse::<Timestamp>()?,
///             BoundInclusivity::Exclusive,
///         ).to_end_bound(),
///     ).to_emptiable()),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::ops::DifferenceResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::set_ops::Differentiable;
/// let interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
///     AbsFiniteBoundPos::new("2025-01-01 12:00:00Z".parse::<Timestamp>()?).to_end_bound(),
/// );
///
/// let remover = AbsBoundPair::new(
///     AbsFiniteBoundPos::new("2025-01-01 13:00:00Z".parse::<Timestamp>()?).to_start_bound(),
///     AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
/// );
///
/// assert_eq!(interval.differentiate(&remover), DifferenceResult::Separate,);
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Differentiable<Rhs = Self> {
    /// Type of the resulting differentiated interval
    type Output;

    /// Differentiates the interval with the given one using default overlap rules
    ///
    /// `self` is the one differentiated by the given other interval: same
    /// operand order as the mathematical expression for a set difference.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::ops::DifferenceResult;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::set_ops::Differentiable;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 14:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// let remover = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 10:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.differentiate(&remover),
    ///     DifferenceResult::Single(
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///                 .to_start_bound(),
    ///             AbsFiniteBoundPos::new_with_incl(
    ///                 "2025-01-01 10:00:00Z".parse::<Timestamp>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_end_bound(),
    ///         )
    ///         .to_emptiable()
    ///     ),
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
    /// # use jiff::Timestamp;
    /// # use periodical::ops::DifferenceResult;
    /// # use periodical::intervals::absolute::{
    /// #     AbsBoundPair,
    /// #     AbsFiniteBoundPos,
    /// #     EmptiableAbsBoundPair,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::overlap::{
    /// #     CanPositionOverlap,
    /// #     DisambiguatedOverlapPosition,
    /// #     OverlapRuleSet,
    /// # };
    /// # use periodical::intervals::ops::remove_overlap::OverlapRemovable;
    /// # use periodical::intervals::ops::set_ops::Differentiable;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 14:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// let remover = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new("2025-01-01 10:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    ///     AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    /// );
    ///
    /// // Only differentiate if it just crosses the other
    /// let difference_closure = |a: &AbsBoundPair,
    ///                           b: &AbsBoundPair|
    ///  -> DifferenceResult<EmptiableAbsBoundPair> {
    ///     match a.disambiguated_overlap_position(b, OverlapRuleSet::Strict) {
    ///         Ok(
    ///             DisambiguatedOverlapPosition::CrossesStart
    ///             | DisambiguatedOverlapPosition::CrossesEnd,
    ///         ) => DifferenceResult::Single(
    ///             a.remove_overlap(b)
    ///                 .expect("They overlap already")
    ///                 .single()
    ///                 .expect(
    ///                     "Since they only cross each other, only a single element will be produced",
    ///                 ),
    ///         ),
    ///         _ => DifferenceResult::Separate,
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     interval.differentiate_with(&remover, difference_closure),
    ///     DifferenceResult::Single(
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///                 .to_start_bound(),
    ///             AbsFiniteBoundPos::new_with_incl(
    ///                 "2025-01-01 10:00:00Z".parse::<Timestamp>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_end_bound(),
    ///         )
    ///         .to_emptiable()
    ///     ),
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

impl<Rhs> Differentiable<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsBoundPair;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelBoundPair;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Differentiable<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl Differentiable<AbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn differentiate(&self, rhs: &AbsBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_difference(Self::Output::from)
    }
}

impl Differentiable<EmptiableAbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn differentiate(&self, rhs: &EmptiableAbsBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl Differentiable<BoundedAbsInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsInterval;

    fn differentiate(&self, rhs: &BoundedAbsInterval) -> DifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => DifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => DifferenceResult::Split(split_before, split_after),
        }
    }
}

impl Differentiable<HalfBoundedAbsInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsInterval;

    fn differentiate(&self, rhs: &HalfBoundedAbsInterval) -> DifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => DifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => DifferenceResult::Split(split_before, split_after),
        }
    }
}

impl Differentiable<RelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn differentiate(&self, rhs: &RelBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_difference(Self::Output::from)
    }
}

impl Differentiable<EmptiableRelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn differentiate(&self, rhs: &EmptiableRelBoundPair) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl Differentiable<BoundedRelInterval> for UnboundedInterval {
    type Output = HalfBoundedRelInterval;

    fn differentiate(&self, rhs: &BoundedRelInterval) -> DifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => DifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => DifferenceResult::Split(split_before, split_after),
        }
    }
}

impl Differentiable<HalfBoundedRelInterval> for UnboundedInterval {
    type Output = HalfBoundedRelInterval;

    fn differentiate(&self, rhs: &HalfBoundedRelInterval) -> DifferenceResult<Self::Output> {
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

/// Differentiates an [`AbsBoundPair`] with another one
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_abs_bound_pair(
    og_bounds: &AbsBoundPair,
    other_bounds: &AbsBoundPair,
) -> DifferenceResult<EmptiableAbsBoundPair> {
    if !og_bounds.simple_overlaps(other_bounds) {
        return DifferenceResult::Separate;
    }

    match og_bounds.remove_overlap(other_bounds) {
        Ok(overlap_removal_res) => match overlap_removal_res {
            OverlapRemovalResult::Single(single) => DifferenceResult::Single(single),
            OverlapRemovalResult::Split(s1, s2) => DifferenceResult::Split(s1, s2),
        },
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    }
}

/// Differentiates an [`AbsBoundPair`] with an
/// [`EmptiableAbsBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
    og_bounds: &AbsBoundPair,
    other_bounds: &EmptiableAbsBoundPair,
) -> DifferenceResult<EmptiableAbsBoundPair> {
    let EmptiableAbsBoundPair::Bound(other_bounds) = other_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_abs_bound_pair(og_bounds, other_bounds)
}

/// Differentiates an [`EmptiableAbsBoundPair`] with another one
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_emptiable_abs_bound_pair(
    og_bounds: &EmptiableAbsBoundPair,
    other_bounds: &EmptiableAbsBoundPair,
) -> DifferenceResult<EmptiableAbsBoundPair> {
    let EmptiableAbsBoundPair::Bound(og_bounds) = og_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(og_bounds, other_bounds)
}

/// Differentiates an [`RelBoundPair`] with another one
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_rel_bound_pair(
    og_bounds: &RelBoundPair,
    other_bounds: &RelBoundPair,
) -> DifferenceResult<EmptiableRelBoundPair> {
    if !og_bounds.simple_overlaps(other_bounds) {
        return DifferenceResult::Separate;
    }

    match og_bounds.remove_overlap(other_bounds) {
        Ok(overlap_removal_res) => match overlap_removal_res {
            OverlapRemovalResult::Single(single) => DifferenceResult::Single(single),
            OverlapRemovalResult::Split(s1, s2) => DifferenceResult::Split(s1, s2),
        },
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    }
}

/// Differentiates an [`RelBoundPair`] with an
/// [`EmptiableRelBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
    og_bounds: &RelBoundPair,
    other_bounds: &EmptiableRelBoundPair,
) -> DifferenceResult<EmptiableRelBoundPair> {
    let EmptiableRelBoundPair::Bound(other_bounds) = other_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_rel_bound_pair(og_bounds, other_bounds)
}

/// Differentiates an [`EmptiableRelBoundPair`] with another one
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`Differentiable`] for more information.
#[must_use]
pub fn differentiate_emptiable_rel_bound_pair(
    og_bounds: &EmptiableRelBoundPair,
    other_bounds: &EmptiableRelBoundPair,
) -> DifferenceResult<EmptiableRelBoundPair> {
    let EmptiableRelBoundPair::Bound(og_bounds) = og_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(og_bounds, other_bounds)
}

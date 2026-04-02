//! Interval difference

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteInterval,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
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
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeInterval,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::{ComplementResult, DifferenceResult};

/// Capacity to differentiate an interval with another
///
/// _Differentiate_, in this context, means the finding the [set difference] of
/// an interval with another, the latter being used as the _remover_ of the
/// former.
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

    /// Differentiates the interval with the given one using default overlap
    /// rules
    ///
    /// `self` is the one differentiated by the given other interval: same
    /// operand order as the mathematical expression for a set difference.
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
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
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
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
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
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
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
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_difference(Self::Output::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
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
        differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
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
        differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
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
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    }
}

/// Differentiates an [`AbsoluteBoundPair`] with an
/// [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    }
}

/// Differentiates an [`RelativeBoundPair`] with an
/// [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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

//! Symmetric difference between two intervals

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
use crate::ops::{ComplementResult, SymmetricDifferenceResult};

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
/// # use jiff::Timestamp;
/// # use periodical::ops::SymmetricDifferenceResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
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
///     first_interval.symmetrically_differentiate(&second_interval),
///     SymmetricDifferenceResult::Split(
///         AbsBoundPair::new(
///             AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?)
///                 .to_start_bound(),
///             AbsFiniteBoundPos::new_with_incl(
///                 "2025-01-01 12:00:00Z".parse::<Timestamp>()?,
///                 BoundInclusivity::Exclusive,
///             )
///             .to_end_bound(),
///         )
///         .to_emptiable(),
///         AbsBoundPair::new(
///             AbsFiniteBoundPos::new_with_incl(
///                 "2025-01-01 14:00:00Z".parse::<Timestamp>()?,
///                 BoundInclusivity::Exclusive,
///             )
///             .to_start_bound(),
///             AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
///         )
///         .to_emptiable(),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::ops::SymmetricDifferenceResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
/// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 12:00:00Z".parse::<Timestamp>()?,
///     ).to_end_bound(),
/// );
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 14:00:00Z".parse::<Timestamp>()?,
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 18:00:00Z".parse::<Timestamp>()?,
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
    /// Type of the resulting symmetrically differentiated interval
    type Output;

    /// Symmetrically differentiates the two intervals using the default overlap rules
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
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
    ///     first_interval.symmetrically_differentiate(&second_interval),
    ///     SymmetricDifferenceResult::Split(
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///                 .to_start_bound(),
    ///             AbsFiniteBoundPos::new_with_incl(
    ///                 "2025-01-01 12:00:00Z".parse::<Timestamp>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_end_bound(),
    ///         )
    ///         .to_emptiable(),
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new_with_incl(
    ///                 "2025-01-01 14:00:00Z".parse::<Timestamp>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_start_bound(),
    ///             AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    ///         )
    ///         .to_emptiable(),
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
    /// # use jiff::Timestamp;
    /// # use periodical::ops::SymmetricDifferenceResult;
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
    /// # use periodical::intervals::ops::set_ops::SymmetricallyDifferentiable;
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
    /// // Only symmetrical differentiate intervals that crosses
    /// let symmetric_difference_closure =
    ///     |a: &AbsBoundPair, b: &AbsBoundPair| -> SymmetricDifferenceResult<EmptiableAbsBoundPair> {
    ///         match a.disambiguated_overlap_position(b, OverlapRuleSet::Strict) {
    ///             Ok(
    ///                 DisambiguatedOverlapPosition::CrossesStart
    ///                 | DisambiguatedOverlapPosition::CrossesEnd,
    ///             ) => a.symmetrically_differentiate(b),
    ///             _ => SymmetricDifferenceResult::Separate,
    ///         }
    ///     };
    ///
    /// assert_eq!(
    ///     first_interval
    ///         .symmetrically_differentiate_with(&second_interval, symmetric_difference_closure),
    ///     SymmetricDifferenceResult::Split(
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///                 .to_start_bound(),
    ///             AbsFiniteBoundPos::new_with_incl(
    ///                 "2025-01-01 12:00:00Z".parse::<Timestamp>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_end_bound(),
    ///         )
    ///         .to_emptiable(),
    ///         AbsBoundPair::new(
    ///             AbsFiniteBoundPos::new_with_incl(
    ///                 "2025-01-01 14:00:00Z".parse::<Timestamp>()?,
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_start_bound(),
    ///             AbsFiniteBoundPos::new("2025-01-01 18:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    ///         )
    ///         .to_emptiable(),
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

impl<Rhs> SymmetricallyDifferentiable<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsBoundPair;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_abs_bound_pair(
            &self.emptiable_abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelBoundPair;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<AbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &AbsBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair(&self.abs_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableAbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableAbsBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<AbsInterval> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &AbsInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<BoundedAbsInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &BoundedAbsInterval) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                SymmetricDifferenceResult::Split(split_before, split_after)
            },
        }
    }
}

impl SymmetricallyDifferentiable<HalfBoundedAbsInterval> for UnboundedInterval {
    type Output = HalfBoundedAbsInterval;

    fn symmetrically_differentiate(&self, rhs: &HalfBoundedAbsInterval) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                SymmetricDifferenceResult::Split(split_before, split_after)
            },
        }
    }
}

impl SymmetricallyDifferentiable<RelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn symmetrically_differentiate(&self, rhs: &RelBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair(&self.rel_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableRelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableRelBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<RelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn symmetrically_differentiate(&self, rhs: &RelInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableRelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableRelInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bound_pair(
            &self.emptiable_rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl SymmetricallyDifferentiable<BoundedRelInterval> for UnboundedInterval {
    type Output = HalfBoundedRelInterval;

    fn symmetrically_differentiate(&self, rhs: &BoundedRelInterval) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                SymmetricDifferenceResult::Split(split_before, split_after)
            },
        }
    }
}

impl SymmetricallyDifferentiable<HalfBoundedRelInterval> for UnboundedInterval {
    type Output = HalfBoundedRelInterval;

    fn symmetrically_differentiate(&self, rhs: &HalfBoundedRelInterval) -> SymmetricDifferenceResult<Self::Output> {
        match rhs.complement() {
            ComplementResult::Single(single) => SymmetricDifferenceResult::Single(single),
            ComplementResult::Split(split_before, split_after) => {
                SymmetricDifferenceResult::Split(split_before, split_after)
            },
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
        // An empty interval is nowhere, and therefore cannot be differentiated with
        // anything
        SymmetricDifferenceResult::Separate
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = ();

    fn symmetrically_differentiate(&self, _rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be differentiated with
        // anything
        SymmetricDifferenceResult::Separate
    }
}

/// Symmetrically differentiates two [`AbsBoundPair`]
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_abs_bound_pair(
    a: &AbsBoundPair,
    b: &AbsBoundPair,
) -> SymmetricDifferenceResult<EmptiableAbsBoundPair> {
    if !a.simple_overlaps(b) {
        return SymmetricDifferenceResult::Separate;
    }

    let diff_a_with_b = match a.remove_overlap(b) {
        Ok(a_removed_b) => a_removed_b,
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };
    let diff_b_with_a = match b.remove_overlap(a) {
        Ok(b_removed_a) => b_removed_a,
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };

    match (diff_a_with_b, diff_b_with_a) {
        (
            OverlapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
            OverlapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableAbsBoundPair::Empty),
        (OverlapRemovalResult::Single(single_diff), OverlapRemovalResult::Single(EmptiableAbsBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableAbsBoundPair::Empty), OverlapRemovalResult::Single(single_diff)) => {
            SymmetricDifferenceResult::Single(single_diff)
        },
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (OverlapRemovalResult::Split(split1, split2), OverlapRemovalResult::Single(EmptiableAbsBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableAbsBoundPair::Empty), OverlapRemovalResult::Split(split1, split2)) => {
            SymmetricDifferenceResult::Split(split1, split2)
        },
        (OverlapRemovalResult::Split(..), _) | (_, OverlapRemovalResult::Split(..)) => {
            unreachable!(
                "No possible interval configuration exist where A \\ B (A diff B) returns a `Split` result, but at \
                 the same time B \\ A (B diff A) returns anything other than an empty interval"
            );
        },
    }
}

/// Symmetrically differentiates an [`AbsBoundPair`] with an
/// [`EmptiableAbsBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> SymmetricDifferenceResult<EmptiableAbsBoundPair> {
    let EmptiableAbsBoundPair::Bound(b) = b else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_abs_bound_pair(a, b)
}

/// Symmetrically differentiates two [`EmptiableAbsBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_emptiable_abs_bound_pair(
    a: &EmptiableAbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> SymmetricDifferenceResult<EmptiableAbsBoundPair> {
    let EmptiableAbsBoundPair::Bound(a) = a else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(a, b)
}

/// Symmetrically differentiates two [`RelBoundPair`]
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_rel_bound_pair(
    a: &RelBoundPair,
    b: &RelBoundPair,
) -> SymmetricDifferenceResult<EmptiableRelBoundPair> {
    if !a.simple_overlaps(b) {
        return SymmetricDifferenceResult::Separate;
    }

    let diff_a_with_b = match a.remove_overlap(b) {
        Ok(a_removed_b) => a_removed_b,
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };
    let diff_b_with_a = match b.remove_overlap(a) {
        Ok(b_removed_a) => b_removed_a,
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };

    match (diff_a_with_b, diff_b_with_a) {
        (
            OverlapRemovalResult::Single(EmptiableRelBoundPair::Empty),
            OverlapRemovalResult::Single(EmptiableRelBoundPair::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableRelBoundPair::Empty),
        (OverlapRemovalResult::Single(single_diff), OverlapRemovalResult::Single(EmptiableRelBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableRelBoundPair::Empty), OverlapRemovalResult::Single(single_diff)) => {
            SymmetricDifferenceResult::Single(single_diff)
        },
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (OverlapRemovalResult::Split(split1, split2), OverlapRemovalResult::Single(EmptiableRelBoundPair::Empty))
        | (OverlapRemovalResult::Single(EmptiableRelBoundPair::Empty), OverlapRemovalResult::Split(split1, split2)) => {
            SymmetricDifferenceResult::Split(split1, split2)
        },
        (OverlapRemovalResult::Split(..), _) | (_, OverlapRemovalResult::Split(..)) => {
            unreachable!(
                "No possible interval configuration exist where A \\ B (A diff B) returns a `Split` result, but at \
                 the same time B \\ A (B diff A) returns anything other than an empty interval"
            );
        },
    }
}

/// Symmetrically differentiates an [`RelBoundPair`] with an
/// [`EmptiableRelBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelBoundPair,
    b: &EmptiableRelBoundPair,
) -> SymmetricDifferenceResult<EmptiableRelBoundPair> {
    let EmptiableRelBoundPair::Bound(b) = b else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_rel_bound_pair(a, b)
}

/// Symmetrically differentiates two [`EmptiableRelBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
///
/// See [`SymmetricallyDifferentiable`] for more information.
#[must_use]
pub fn symmetrically_differentiate_emptiable_rel_bound_pair(
    a: &EmptiableRelBoundPair,
    b: &EmptiableRelBoundPair,
) -> SymmetricDifferenceResult<EmptiableRelBoundPair> {
    let EmptiableRelBoundPair::Bound(a) = a else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(a, b)
}

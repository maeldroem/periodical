//! Interval symmetric difference

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
use crate::ops::{ComplementResult, SymmetricDifferenceResult};

/// Capacity to symmetrically differentiate (a.k.a. XOR) an interval with
/// another
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

    /// Symmetrically differentiates the two intervals using the default overlap
    /// rules
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
        symmetrically_differentiate_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
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
        symmetrically_differentiate_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map_symmetric_difference(Self::Output::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
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
        symmetrically_differentiate_abs_bound_pair(&self.abs_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
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
            ComplementResult::Split(split_before, split_after) => {
                SymmetricDifferenceResult::Split(split_before, split_after)
            },
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
            ComplementResult::Split(split_before, split_after) => {
                SymmetricDifferenceResult::Split(split_before, split_after)
            },
        }
    }
}

impl SymmetricallyDifferentiable<RelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &RelativeBoundPair) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bound_pair(&self.rel_bound_pair(), rhs)
            .map_symmetric_difference(Self::Output::from)
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
            ComplementResult::Split(split_before, split_after) => {
                SymmetricDifferenceResult::Split(split_before, split_after)
            },
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
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };
    let diff_b_with_a = match b.remove_overlap(a) {
        Ok(b_removed_a) => b_removed_a,
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };

    match (diff_a_with_b, diff_b_with_a) {
        (
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableAbsoluteBoundPair::Empty),
        (
            OverlapRemovalResult::Single(single_diff),
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        )
        | (
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
            OverlapRemovalResult::Single(single_diff),
        ) => SymmetricDifferenceResult::Single(single_diff),
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (
            OverlapRemovalResult::Split(split1, split2),
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        )
        | (
            OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
            OverlapRemovalResult::Split(split1, split2),
        ) => SymmetricDifferenceResult::Split(split1, split2),
        (OverlapRemovalResult::Split(..), _) | (_, OverlapRemovalResult::Split(..)) => {
            unreachable!(
                "No possible interval configuration exist where A \\ B (A diff B) returns a `Split` result, but at \
                 the same time B \\ A (B diff A) returns anything other than an empty interval"
            );
        },
    }
}

/// Symmetrically differentiates an [`AbsoluteBoundPair`] with an
/// [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };
    let diff_b_with_a = match b.remove_overlap(a) {
        Ok(b_removed_a) => b_removed_a,
        Err(OverlapRemovalNoOverlapFoundError) => unreachable!("Overlap check already happened earlier"),
    };

    match (diff_a_with_b, diff_b_with_a) {
        (
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableRelativeBoundPair::Empty),
        (
            OverlapRemovalResult::Single(single_diff),
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
        )
        | (
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
            OverlapRemovalResult::Single(single_diff),
        ) => SymmetricDifferenceResult::Single(single_diff),
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (
            OverlapRemovalResult::Split(split1, split2),
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
        )
        | (
            OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty),
            OverlapRemovalResult::Split(split1, split2),
        ) => SymmetricDifferenceResult::Split(split1, split2),
        (OverlapRemovalResult::Split(..), _) | (_, OverlapRemovalResult::Split(..)) => {
            unreachable!(
                "No possible interval configuration exist where A \\ B (A diff B) returns a `Split` result, but at \
                 the same time B \\ A (B diff A) returns anything other than an empty interval"
            );
        },
    }
}

/// Symmetrically differentiates an [`RelativeBoundPair`] with an
/// [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be differentiated.
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

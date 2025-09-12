//! Set operations on intervals

use super::abridge::Abridgable;
use super::extend::Extensible;
use super::overlap::CanPositionOverlap;
use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteInterval, EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::overlap::{OverlapRule, OverlapRuleSet};
use crate::intervals::ops::remove_overlap::{OverlapRemovable, OverlapRemovalErr, OverlapRemovalResult};
use crate::intervals::relative::{EmptiableRelativeBounds, HalfBoundedRelativeInterval, RelativeBounds};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{BoundedAbsoluteInterval, BoundedRelativeInterval, RelativeInterval};
use crate::ops::{DifferenceResult, IntersectionResult, SymmetricDifferenceResult, UnionResult};

/// Capacity to unite an interval with another
pub trait Unitable<Rhs = Self> {
    /// Output type
    type Output;

    /// Unites two intervals using default overlap rules
    #[must_use]
    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output>;

    /// Unites two intervals using the given closure
    #[must_use]
    fn unite_with<F>(&self, rhs: &Rhs, mut f: F) -> UnionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> UnionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_united(AbsoluteInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_united(AbsoluteInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_united(AbsoluteInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Unitable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_united(RelativeInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_united(RelativeInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
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

/// Unites two [`AbsoluteBounds`]
#[must_use]
pub fn unite_abs_bounds(a: &AbsoluteBounds, b: &AbsoluteBounds) -> UnionResult<AbsoluteBounds> {
    // We use the lenient rule set with allow adjacency rule so that "touching" intervals are united together
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united
#[must_use]
pub fn unite_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> UnionResult<AbsoluteBounds> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableAbsoluteBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united
#[must_use]
pub fn unite_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> UnionResult<EmptiableAbsoluteBounds> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`RelativeBounds`]
#[must_use]
pub fn unite_rel_bounds(a: &RelativeBounds, b: &RelativeBounds) -> UnionResult<RelativeBounds> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`RelativeBounds`] with an [`EmptiableRelativeBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united
#[must_use]
pub fn unite_rel_bounds_with_emptiable_rel_bounds(
    a: &RelativeBounds,
    b: &EmptiableRelativeBounds,
) -> UnionResult<RelativeBounds> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableRelativeBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be united
#[must_use]
pub fn unite_emptiable_rel_bounds(
    a: &EmptiableRelativeBounds,
    b: &EmptiableRelativeBounds,
) -> UnionResult<EmptiableRelativeBounds> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Capacity to unite an interval with another
pub trait Intersectable<Rhs = Self> {
    /// Output type
    type Output;

    /// Intersects two intervals using the given rules
    #[must_use]
    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output>;

    /// Intersects two intervals using the given closure
    #[must_use]
    fn intersect_with<F>(&self, rhs: &Rhs, mut f: F) -> IntersectionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> IntersectionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Intersectable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_intersected(RelativeInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_intersected(RelativeInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<AbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &AbsoluteBounds) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<EmptiableAbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &EmptiableAbsoluteBounds) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<AbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &AbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &BoundedAbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &HalfBoundedAbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<RelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &RelativeBounds) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<EmptiableRelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &EmptiableRelativeBounds) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<RelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &RelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &BoundedRelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &HalfBoundedRelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map_intersected(RelativeInterval::from)
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

/// Intersects two [`AbsoluteBounds`]
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableAbsoluteBounds::Empty`]
#[must_use]
pub fn intersect_abs_bounds(a: &AbsoluteBounds, b: &AbsoluteBounds) -> IntersectionResult<AbsoluteBounds> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableAbsoluteBounds::Empty`]
#[must_use]
pub fn intersect_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> IntersectionResult<AbsoluteBounds> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableAbsoluteBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected
#[must_use]
pub fn intersect_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> IntersectionResult<EmptiableAbsoluteBounds> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects two [`RelativeBounds`]
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableRelativeBounds::Empty`]
#[must_use]
pub fn intersect_rel_bounds(a: &RelativeBounds, b: &RelativeBounds) -> IntersectionResult<RelativeBounds> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`RelativeBounds`] with an [`EmptiableRelativeBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns [`EmptiableRelativeBounds::Empty`]
#[must_use]
pub fn intersect_rel_bounds_with_emptiable_rel_bounds(
    a: &RelativeBounds,
    b: &EmptiableRelativeBounds,
) -> IntersectionResult<RelativeBounds> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableRelativeBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be intersected
#[must_use]
pub fn intersect_emptiable_rel_bounds(
    a: &EmptiableRelativeBounds,
    b: &EmptiableRelativeBounds,
) -> IntersectionResult<EmptiableRelativeBounds> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Capacity to differentiate an interval with another (as in set difference)
pub trait Differentiable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns the set difference of `self` with `other` using default overlap rules
    ///
    /// The caller, self, is the one that is differentiated by the given other: same operand order as the mathematical
    /// expression for a set difference.
    #[must_use]
    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output>;

    /// Returns the set difference of `self` with `other` using the given closure
    #[must_use]
    fn differentiate_with<F>(&self, rhs: &Rhs, mut f: F) -> DifferenceResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> DifferenceResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Differentiable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = EmptiableAbsoluteBounds;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> Differentiable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_difference(AbsoluteInterval::from)
    }
}

impl<Rhs> Differentiable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_difference(AbsoluteInterval::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_difference(AbsoluteInterval::from)
    }
}

impl<Rhs> Differentiable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = EmptiableRelativeBounds;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Differentiable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> Differentiable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_difference(RelativeInterval::from)
    }
}

impl<Rhs> Differentiable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_difference(RelativeInterval::from)
    }
}

impl<Rhs> Differentiable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        differentiate_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_difference(RelativeInterval::from)
    }
}

impl Differentiable<AbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn differentiate(&self, rhs: &AbsoluteBounds) -> DifferenceResult<Self::Output> {
        differentiate_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map_difference(AbsoluteInterval::from)
    }
}

impl Differentiable<EmptiableAbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn differentiate(&self, rhs: &EmptiableAbsoluteBounds) -> DifferenceResult<Self::Output> {
        differentiate_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_difference(AbsoluteInterval::from)
    }
}

impl Differentiable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn differentiate(&self, rhs: &BoundedAbsoluteInterval) -> DifferenceResult<Self::Output> {
        differentiate_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map_difference(AbsoluteInterval::from)
    }
}

impl Differentiable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn differentiate(&self, rhs: &HalfBoundedAbsoluteInterval) -> DifferenceResult<Self::Output> {
        differentiate_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds()).map_difference(AbsoluteInterval::from)
    }
}

impl Differentiable<RelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn differentiate(&self, rhs: &RelativeBounds) -> DifferenceResult<Self::Output> {
        differentiate_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map_difference(RelativeInterval::from)
    }
}

impl Differentiable<EmptiableRelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn differentiate(&self, rhs: &EmptiableRelativeBounds) -> DifferenceResult<Self::Output> {
        differentiate_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_difference(RelativeInterval::from)
    }
}

impl Differentiable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn differentiate(&self, rhs: &BoundedRelativeInterval) -> DifferenceResult<Self::Output> {
        differentiate_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map_difference(RelativeInterval::from)
    }
}

impl Differentiable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn differentiate(&self, rhs: &HalfBoundedRelativeInterval) -> DifferenceResult<Self::Output> {
        differentiate_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds()).map_difference(RelativeInterval::from)
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

/// Differentiates an [`AbsoluteBounds`] with another one
#[must_use]
pub fn differentiate_abs_bounds(
    og_bounds: &AbsoluteBounds,
    other_bounds: &AbsoluteBounds,
) -> DifferenceResult<EmptiableAbsoluteBounds> {
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

/// Differentiates an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn differentiate_abs_bounds_with_emptiable_abs_bounds(
    og_bounds: &AbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> DifferenceResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(other_bounds) = other_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_abs_bounds(og_bounds, other_bounds)
}

/// Differentiates an [`EmptiableAbsoluteBounds`] with another one
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn differentiate_emptiable_abs_bounds(
    og_bounds: &EmptiableAbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
) -> DifferenceResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(og_bounds) = og_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_abs_bounds_with_emptiable_abs_bounds(og_bounds, other_bounds)
}

/// Differentiates an [`RelativeBounds`] with another one
#[must_use]
pub fn differentiate_rel_bounds(
    og_bounds: &RelativeBounds,
    other_bounds: &RelativeBounds,
) -> DifferenceResult<EmptiableRelativeBounds> {
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

/// Differentiates an [`RelativeBounds`] with an [`EmptiableRelativeBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn differentiate_rel_bounds_with_emptiable_rel_bounds(
    og_bounds: &RelativeBounds,
    other_bounds: &EmptiableRelativeBounds,
) -> DifferenceResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(other_bounds) = other_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_rel_bounds(og_bounds, other_bounds)
}

/// Differentiates an [`EmptiableRelativeBounds`] with another one
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn differentiate_emptiable_rel_bounds(
    og_bounds: &EmptiableRelativeBounds,
    other_bounds: &EmptiableRelativeBounds,
) -> DifferenceResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(og_bounds) = og_bounds else {
        return DifferenceResult::Separate;
    };

    differentiate_rel_bounds_with_emptiable_rel_bounds(og_bounds, other_bounds)
}

/// Capacity to symmetrically differentiate (a.k.a. XOR) an interval with another
pub trait SymmetricallyDifferentiable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns the symmetrical difference between two sets of bounds using the given rules
    ///
    /// Simply uses the [`Differentiable`] trait on both Self with Rhs, and Rhs with Self.
    #[must_use]
    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output>;

    /// Returns the symmetrical difference between two sets of bounds using the given closure
    #[must_use]
    fn symmetrically_differentiate_with<F>(&self, rhs: &Rhs, mut f: F) -> SymmetricDifferenceResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> SymmetricDifferenceResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = EmptiableAbsoluteBounds;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds_with_emptiable_abs_bounds(
            &self.abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        )
        .map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds_with_emptiable_abs_bounds(
            &self.abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        )
        .map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = EmptiableRelativeBounds;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map_symmetric_difference(RelativeInterval::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds_with_emptiable_rel_bounds(
            &self.rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        )
        .map_symmetric_difference(RelativeInterval::from)
    }
}

impl<Rhs> SymmetricallyDifferentiable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds_with_emptiable_rel_bounds(
            &self.rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        )
        .map_symmetric_difference(RelativeInterval::from)
    }
}

impl SymmetricallyDifferentiable<AbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &AbsoluteBounds) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds(&self.abs_bounds(), rhs).map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableAbsoluteBounds> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableAbsoluteBounds) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), rhs)
            .map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl SymmetricallyDifferentiable<AbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &AbsoluteInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds_with_emptiable_abs_bounds(
            &self.abs_bounds(),
            &rhs.emptiable_abs_bounds(),
        )
        .map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl SymmetricallyDifferentiable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn symmetrically_differentiate(&self, rhs: &BoundedAbsoluteInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds())
            .map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl SymmetricallyDifferentiable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn symmetrically_differentiate(
        &self,
        rhs: &HalfBoundedAbsoluteInterval,
    ) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds())
            .map_symmetric_difference(AbsoluteInterval::from)
    }
}

impl SymmetricallyDifferentiable<RelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &RelativeBounds) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds(&self.rel_bounds(), rhs).map_symmetric_difference(RelativeInterval::from)
    }
}

impl SymmetricallyDifferentiable<EmptiableRelativeBounds> for UnboundedInterval {
    type Output = RelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &EmptiableRelativeBounds) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), rhs)
            .map_symmetric_difference(RelativeInterval::from)
    }
}

impl SymmetricallyDifferentiable<RelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &RelativeInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds_with_emptiable_rel_bounds(
            &self.rel_bounds(),
            &rhs.emptiable_rel_bounds(),
        )
        .map_symmetric_difference(RelativeInterval::from)
    }
}

impl SymmetricallyDifferentiable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn symmetrically_differentiate(&self, rhs: &BoundedRelativeInterval) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds())
            .map_symmetric_difference(RelativeInterval::from)
    }
}

impl SymmetricallyDifferentiable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn symmetrically_differentiate(
        &self,
        rhs: &HalfBoundedRelativeInterval,
    ) -> SymmetricDifferenceResult<Self::Output> {
        symmetrically_differentiate_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds())
            .map_symmetric_difference(RelativeInterval::from)
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

/// Symmetrically differentiates two [`AbsoluteBounds`]
#[must_use]
pub fn symmetrically_differentiate_abs_bounds(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBounds> {
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
            OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
            OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableAbsoluteBounds::Empty),
        (OverlapRemovalResult::Single(single_diff), OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty))
        | (OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty), OverlapRemovalResult::Single(single_diff)) => {
            SymmetricDifferenceResult::Single(single_diff)
        },
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (OverlapRemovalResult::Split(split1, split2), OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty))
        | (OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty), OverlapRemovalResult::Split(split1, split2)) => {
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

/// Symmetrically differentiates an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn symmetrically_differentiate_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(b) = b else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_abs_bounds(a, b)
}

/// Symmetrically differentiates two [`EmptiableAbsoluteBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn symmetrically_differentiate_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(a) = a else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_abs_bounds_with_emptiable_abs_bounds(a, b)
}

/// Symmetrically differentiates two [`RelativeBounds`]
#[must_use]
pub fn symmetrically_differentiate_rel_bounds(
    a: &RelativeBounds,
    b: &RelativeBounds,
) -> SymmetricDifferenceResult<EmptiableRelativeBounds> {
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
            OverlapRemovalResult::Single(EmptiableRelativeBounds::Empty),
            OverlapRemovalResult::Single(EmptiableRelativeBounds::Empty),
        ) => SymmetricDifferenceResult::Single(EmptiableRelativeBounds::Empty),
        (OverlapRemovalResult::Single(single_diff), OverlapRemovalResult::Single(EmptiableRelativeBounds::Empty))
        | (OverlapRemovalResult::Single(EmptiableRelativeBounds::Empty), OverlapRemovalResult::Single(single_diff)) => {
            SymmetricDifferenceResult::Single(single_diff)
        },
        (OverlapRemovalResult::Single(first_single_diff), OverlapRemovalResult::Single(second_single_diff)) => {
            SymmetricDifferenceResult::Split(first_single_diff, second_single_diff)
        },
        (OverlapRemovalResult::Split(split1, split2), OverlapRemovalResult::Single(EmptiableRelativeBounds::Empty))
        | (OverlapRemovalResult::Single(EmptiableRelativeBounds::Empty), OverlapRemovalResult::Split(split1, split2)) => {
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

/// Symmetrically differentiates an [`RelativeBounds`] with an [`EmptiableRelativeBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn symmetrically_differentiate_rel_bounds_with_emptiable_rel_bounds(
    a: &RelativeBounds,
    b: &EmptiableRelativeBounds,
) -> SymmetricDifferenceResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(b) = b else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_rel_bounds(a, b)
}

/// Symmetrically differentiates two [`EmptiableRelativeBounds`]
///
/// Empty intervals are not positioned in time, and are always "outside", therefore cannot be differentiated
#[must_use]
pub fn symmetrically_differentiate_emptiable_rel_bounds(
    a: &EmptiableRelativeBounds,
    b: &EmptiableRelativeBounds,
) -> SymmetricDifferenceResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(a) = a else {
        return SymmetricDifferenceResult::Separate;
    };

    symmetrically_differentiate_rel_bounds_with_emptiable_rel_bounds(a, b)
}

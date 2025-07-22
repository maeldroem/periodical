//! Set operations on intervals

use super::abridge::Abridgable;
use super::extend::Extensible;
use super::overlap_position::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRule, OverlapRuleSet};
use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteInterval, EmptiableAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::ops::{DifferenceResult, IntersectionResult, SymmetricDifferenceResult, UnionResult};

// TODO: Change interval iters so that they use the following traits

/// Capacity to unite an interval with another
pub trait Unitable<Rhs = Self> {
    /// Output type
    type Output;

    /// Unites two intervals using the given rules
    #[must_use]
    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    /// Unites two intervals using default overlap rules
    #[must_use]
    fn simple_unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        self.unite(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

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

    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        unite_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        unite_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn unite<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> UnionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        unite_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &rhs.emptiable_abs_bounds(),
            rule_set,
            rules,
        )
        .map_united(AbsoluteInterval::from)
    }
}

/// Unites two [`AbsoluteBounds`] using the given rules
pub fn unite_abs_bounds<'a, RI>(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> UnionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableAbsoluteBounds`] using the given rules
pub fn unite_emptiable_abs_bounds<'a, RI>(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> UnionResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`] using the given rules
pub fn unite_abs_bounds_with_emptiable_abs_bounds<'a, RI>(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> UnionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
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
    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    /// Intersects two intervals using default overlap rules
    #[must_use]
    fn simple_intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        self.intersect(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

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

    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        intersect_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        intersect_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds(), rule_set, rules)
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn intersect<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> IntersectionResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        intersect_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &rhs.emptiable_abs_bounds(),
            rule_set,
            rules,
        )
        .map_intersected(AbsoluteInterval::from)
    }
}

/// Intersects two [`AbsoluteBounds`] using the given rules
pub fn intersect_abs_bounds<'ri, RI>(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> IntersectionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects two [`EmptiableAbsoluteBounds`] using the given rules
pub fn intersect_emptiable_abs_bounds<'ri, RI>(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> IntersectionResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`] using the given rules
pub fn intersect_abs_bounds_with_emptiable_abs_bounds<'ri, RI>(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> IntersectionResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Capacity to differentiate an interval with another (as in set difference)
pub trait Differentiable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns the set difference of `self` with `other` using the given rules
    ///
    /// The caller, self, is the one that is differentiated by the given other: same operand order as the mathematical
    /// expression for a set difference.
    #[must_use]
    fn differentiate<'ri, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> DifferenceResult<Self::Output>
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    /// Returns the set difference of `self` with `other` using default overlap rules
    #[must_use]
    fn simple_differentiate(&self, rhs: &Rhs) -> DifferenceResult<Self::Output> {
        self.differentiate(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns the set difference of `self` with `other` using the given closure
    #[must_use]
    fn differentiate_with<F>(&self, rhs: &Rhs, mut f: F) -> DifferenceResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> DifferenceResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

/// Differentiates an [`AbsoluteBounds`] with another one
#[must_use]
pub fn differentiate_abs_bounds<'ri, RI>(
    og_bounds: &AbsoluteBounds,
    other_bounds: &AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Differentiates an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn differentiate_abs_bounds_with_emptiable_bounds<'ri, RI>(
    og_bounds: &AbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Differentiates an [`EmptiableAbsoluteBounds`] with another one
#[must_use]
pub fn differentiate_emptiable_abs_bounds<'ri, RI>(
    og_bounds: &EmptiableAbsoluteBounds,
    other_bounds: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> DifferenceResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Capacity to symmetrically differentiate (a.k.a. XOR) an interval with another
pub trait SymmetricallyDifferentiable<Rhs = Self>: Differentiable<Rhs, Output = Self::DiffSelfWithRhs> + Sized
where
    Rhs: Differentiable<Self, Output = Self::DiffRhsWithSelf>,
{
    /// Difference of Self with Rhs
    type DiffSelfWithRhs;

    /// Difference of Rhs with Self
    type DiffRhsWithSelf;

    /// Returns the symmetrical difference between two sets of bounds using the given rules
    ///
    /// Simply uses the [`Differentiable`] trait on both Self with Rhs, and Rhs with Self.
    #[must_use]
    fn symmetrically_differentiate<'ri, RI>(
        &self,
        rhs: &Rhs,
        rule_set: OverlapRuleSet,
        rules: RI,
    ) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs>
    // FIX
    where
        RI: IntoIterator<Item = &'ri OverlapRule> + Clone,
    {
        todo!()
        // let diff_self_with_rhs = self.differentiate(rhs, rule_set, rules.clone());
        // let diff_rhs_with_self = rhs.differentiate(self, rule_set, rules.clone());

        // match (diff_self_with_rhs, diff_rhs_with_self) {
        //     (DifferenceResult::Difference(diff_self_with_rhs), DifferenceResult::Difference(diff_rhs_with_self)) => {
        //         SymmetricDifferenceResult::SymmetricDifference(diff_self_with_rhs, diff_rhs_with_self)
        //     },
        //     _ => SymmetricDifferenceResult::Separate,
        // }
    }

    /// Returns the symmetrical difference between two sets of bounds using default overlap rules
    #[must_use]
    fn simple_symmetrically_differentiate(&self, rhs: &Rhs) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs> /* FIX */
    {
        self.symmetrically_differentiate(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns the symmetrical difference between two sets of bounds using the given closure
    #[must_use]
    fn symmetrically_differentiate_with<F>(
        &self,
        rhs: &Rhs,
        mut f: F,
    ) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs>
    // FIX
    where
        F: FnMut(&Self, &Rhs) -> SymmetricDifferenceResult<Self::DiffSelfWithRhs>, // FIX
    {
        (f)(self, rhs)
    }
}

/// Symmetrically differentiates two [`AbsoluteBounds`] using the given rules
pub fn symmetrically_differentiate_abs_bounds<'ri, RI>(
    a: AbsoluteBounds,
    b: AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> SymmetricDifferenceResult<AbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Symmetrically differentiates two [`EmptiableAbsoluteBounds`] using the given rules
pub fn symmetrically_differentiate_emptiable_abs_bounds<'ri, RI>(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> SymmetricDifferenceResult<EmptiableAbsoluteBounds>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

/// Symmetrically differentiates two [`AbsoluteInterval`]s using the given rules
pub fn symmetrically_differentiate_abs_intervals<'ri, RI>(
    a: &AbsoluteInterval,
    b: &AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: RI,
) -> SymmetricDifferenceResult<AbsoluteInterval>
where
    RI: IntoIterator<Item = &'ri OverlapRule>,
{
    todo!()
}

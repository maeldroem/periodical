//! Implementations of iterators for intervals and operations between sets of intervals
//!
//! In this module you will find the different structures for lazy operations as well as their implementations
//! for dealing with intervals.
//!
//! For example, set operations, like unions, intersections, etc. But also operations like using a certain precision
//! to re-precise interval times.

use std::iter::{FusedIterator, Peekable};

use chrono::{DateTime, RoundingError, Utc};

use crate::intervals::interval::{
    AbsoluteBounds, EmptiableAbsoluteBounds, EmptiableRelativeBounds, HasAbsoluteBounds, HasRelativeBounds,
    RelativeBounds, ToAbsolute, ToRelative,
};
use crate::intervals::ops::{
    CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRule, OverlapRuleSet, PreciseAbsoluteBounds, Precision,
    intersect_abs_bounds, intersect_abs_intervals, intersect_emptiable_abs_bounds, unite_abs_bounds,
    unite_abs_intervals, unite_emptiable_abs_bounds,
};
use crate::intervals::{AbsoluteInterval, RelativeInterval};
use crate::ops::{DifferenceResult, IntersectionResult, RunningResult, SymmetricDifferenceResult, UnionResult};

// TODO: This should contain overlap rules and a function etc. but those should be split into different kinds of Union
// structures. Also, since by doing that they would become specialized for intervals, the module should be renamed
// to "interval_set_ops.rs".
// Moreover, intervals::set_ops_impl should have methods like those in the comparison module to allow simpler and
// more granular methods for lazy set operations.
// List draft:
// - SimpleUnion - would use predetermined rules like the one for simple_overlaps in the comparison mod
// - Union - would use given rule set and rules to do the uniting
// - UnionWith - would use a custom function to unite the intervals
// - SimpleUnionToOne - would use predetermined rules to try and unite the intervals into a single one (if there
//   are non-overlapping intervals later on, they are ignored and the iterator ends)
// - UnionToOne - same as above but with given rule set and rules to do the uniting
// - UnionToOneWith - same principle, but with custom function
// - Inverse - returns a list of the inverse of the intervals (all the time not covered by the intervals)
// Do other iterators like those
// Since that would make them specialized, I think the set operations traits defined in set_ops.rs are not needed
// or should be rethought. Current opinion: those set operations should be implemented for intervals, schedules, etc.
// but since they are simple enough, we should just remove them for now, implement the specialized iterators,
// continue developing the lib until we can rule whether such traits are needed

// NOTE: Most of the operations in this file can be MAJORLY IMPROVED in terms of performance
// Suggestions for improvement:
// - Most operations can be done in parallel, but that would require them to be eagerly-evaluated, therefore it would
//   put into question whether we still need those methods as iterators. Or perhaps we can keep the iterators but
//   create methods that explicitly allow this eager evaluation?
// - Operations that "merges" two iterators may benefit from a point system: we merge all interval points into one list
//   and read from this list, therefore when we encounter a point that comes from the second iterator, we can apply
//   the operation and continue from there instead of checking for overlap of all elements of the first iter upon
//   each element of the second iter. This strategy is applicable to iterators but requires both sets of intervals
//   to be sorted chronologically.
// Current opinion: Such eager and constrained methods should be implemented on the IntervalIterator trait,
// that way, the caller can choose which one fits his needs: if they want to unite elements progressively of a list
// that is unsorted or sorted non-chronologically, they can choose to use the Union iterator. But if they need
// a fast way of uniting a list of intervals that is sorted chronologically, then they can call such methods.

// NOTE: Implement FusedIterator and exhaustion field in iterators

/// Ad-hoc trait for relative-bounded structures that can change their relativity to absolute
pub trait RelativeToAbsoluteOperable {
    type Item: HasAbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::Item;
}

impl<T: Sized + RelativeToAbsoluteOperable> RelativeToAbsoluteOperable for &T {
    type Item = T::Item;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::Item {
        (**self).to_absolute(reference_time)
    }
}

impl<T: Sized + RelativeToAbsoluteOperable> RelativeToAbsoluteOperable for &mut T {
    type Item = T::Item;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::Item {
        (**self).to_absolute(reference_time)
    }
}

impl RelativeToAbsoluteOperable for RelativeBounds {
    type Item = AbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::Item {
        <Self as ToAbsolute>::to_absolute(self, reference_time)
    }
}

impl RelativeToAbsoluteOperable for EmptiableRelativeBounds {
    type Item = EmptiableAbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::Item {
        <Self as ToAbsolute>::to_absolute(self, reference_time)
    }
}

impl RelativeToAbsoluteOperable for RelativeInterval {
    type Item = AbsoluteInterval;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::Item {
        <Self as ToAbsolute>::to_absolute(self, reference_time)
    }
}

/// Dispatcher trait for the [`RelativeToAbsolute`] conversion iterator
pub trait RelativeToAbsoluteIteratorDispatcher: Iterator + Sized {
    /// Converts [`RelativeInterval`]s to [`AbsoluteInterval`]s
    fn to_absolute(self, reference_time: DateTime<Utc>) -> RelativeToAbsolute<Self> {
        RelativeToAbsolute::new(self, reference_time)
    }
}

impl<I> RelativeToAbsoluteIteratorDispatcher for I
where
    I: Iterator,
    I::Item: RelativeToAbsoluteOperable<Item = I::Item>,
{
}

/// Converts relative intervals to absolute intervals
pub struct RelativeToAbsolute<I> {
    iter: I,
    reference_time: DateTime<Utc>,
}

impl<I> RelativeToAbsolute<I> {
    pub fn new(iter: I, reference_time: DateTime<Utc>) -> Self {
        RelativeToAbsolute { iter, reference_time }
    }
}

impl<I> Iterator for RelativeToAbsolute<I>
where
    I: Iterator,
    I::Item: RelativeToAbsoluteOperable<Item = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_absolute(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for RelativeToAbsolute<I>
where
    I: DoubleEndedIterator,
    I::Item: RelativeToAbsoluteOperable<Item = I::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.to_absolute(self.reference_time))
    }
}

/// Ad-hoc trait for absolute-bounded structures that can change their relativity to relative
pub trait AbsoluteToRelativeOperable {
    type Item: HasRelativeBounds;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::Item;
}

impl<T: Sized + AbsoluteToRelativeOperable> AbsoluteToRelativeOperable for &T {
    type Item = T::Item;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::Item {
        (**self).to_relative(reference_time)
    }
}

impl<T: Sized + AbsoluteToRelativeOperable> AbsoluteToRelativeOperable for &mut T {
    type Item = T::Item;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::Item {
        (**self).to_relative(reference_time)
    }
}

impl AbsoluteToRelativeOperable for AbsoluteBounds {
    type Item = RelativeBounds;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::Item {
        <Self as ToRelative>::to_relative(self, reference_time)
    }
}

impl AbsoluteToRelativeOperable for EmptiableAbsoluteBounds {
    type Item = EmptiableRelativeBounds;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::Item {
        <Self as ToRelative>::to_relative(self, reference_time)
    }
}

impl AbsoluteToRelativeOperable for AbsoluteInterval {
    type Item = RelativeInterval;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::Item {
        <Self as ToRelative>::to_relative(self, reference_time)
    }
}

/// Dispatcher trait for the [`AbsoluteToRelative`] conversion iterator
pub trait AbsoluteToRelativeIteratorDispatcher: Iterator + Sized {
    /// Converts [`AbsoluteInterval`]s to [`RelativeInterval`]s
    fn to_relative(self, reference_time: DateTime<Utc>) -> AbsoluteToRelative<Self> {
        AbsoluteToRelative::new(self, reference_time)
    }
}

impl<I> AbsoluteToRelativeIteratorDispatcher for I
where
    I: Iterator,
    I::Item: AbsoluteToRelativeOperable<Item = I::Item>,
{
}

/// Converts absolute intervals to relative intervals
pub struct AbsoluteToRelative<I> {
    iter: I,
    reference_time: DateTime<Utc>,
}

impl<I> AbsoluteToRelative<I> {
    pub fn new(iter: I, reference_time: DateTime<Utc>) -> Self {
        AbsoluteToRelative { iter, reference_time }
    }
}

impl<I> Iterator for AbsoluteToRelative<I>
where
    I: Iterator,
    I::Item: AbsoluteToRelativeOperable<Item = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_relative(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for AbsoluteToRelative<I>
where
    I: DoubleEndedIterator,
    I::Item: AbsoluteToRelativeOperable<Item = I::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.to_relative(self.reference_time))
    }
}

/// Ad-hoc trait for structures that can change their bounds' precision
pub trait PrecisionChangeOperable {
    type Item: PrecisionChangeOperable;
    type Error;

    /// Changes the start and end bounds with the given precisions (one for each bound)
    ///
    /// # Errors
    ///
    /// Precising a time usually is prone to errors, therefore this trait has the associated type
    /// [`Error`](PrecisionChangeOperable::Error) that allows for defining what kind of error will be produced by this
    /// process.
    fn change_start_end_precision(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Result<Self::Item, Self::Error>;
}

impl<T: Sized + PrecisionChangeOperable> PrecisionChangeOperable for &T {
    type Item = T::Item;
    type Error = T::Error;

    fn change_start_end_precision(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Result<Self::Item, Self::Error> {
        (**self).change_start_end_precision(start_precision, end_precision)
    }
}

impl<T: Sized + PrecisionChangeOperable> PrecisionChangeOperable for &mut T {
    type Item = T::Item;
    type Error = T::Error;

    fn change_start_end_precision(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Result<Self::Item, Self::Error> {
        (**self).change_start_end_precision(start_precision, end_precision)
    }
}

impl PrecisionChangeOperable for AbsoluteBounds {
    type Item = Self;
    type Error = RoundingError;

    fn change_start_end_precision(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Result<Self::Item, Self::Error> {
        self.precise_bounds_with_different_precisions(start_precision, end_precision)
    }
}

impl PrecisionChangeOperable for EmptiableAbsoluteBounds {
    type Item = Self;
    type Error = RoundingError;

    fn change_start_end_precision(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Result<Self::Item, Self::Error> {
        self.precise_bounds_with_different_precisions(start_precision, end_precision)
    }
}

impl PrecisionChangeOperable for AbsoluteInterval {
    type Item = Self;
    type Error = RoundingError;

    fn change_start_end_precision(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Result<Self::Item, Self::Error> {
        self.precise_bounds_with_different_precisions(start_precision, end_precision)
    }
}

/// Dispatcher trait for the [`PrecisionChange`] iterator
pub trait PrecisionChangeIteratorDispatcher: Iterator + Sized {
    /// Changes the precision of the interval with the given [`Precision`]
    fn change_precision(self, precision: Precision) -> PrecisionChange<Self> {
        PrecisionChange::new(self, precision, precision)
    }

    /// Changes the precision of start and end bounds with the given [`Precision`]s
    fn change_start_end_precision(self, start_precision: Precision, end_precision: Precision) -> PrecisionChange<Self> {
        PrecisionChange::new(self, start_precision, end_precision)
    }
}

impl<I> PrecisionChangeIteratorDispatcher for I
where
    I: Iterator,
    I::Item: PrecisionChangeOperable<Item = I::Item>,
{
}

/// Changes the precision of start end end times
pub struct PrecisionChange<I> {
    iter: I,
    start_precision: Precision,
    end_precision: Precision,
}

impl<I> PrecisionChange<I> {
    pub fn new(iter: I, start_precision: Precision, end_precision: Precision) -> Self {
        PrecisionChange {
            iter,
            start_precision,
            end_precision,
        }
    }
}

impl<I> Iterator for PrecisionChange<I>
where
    I: Iterator,
    I::Item: PrecisionChangeOperable<Item = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()?
            .change_start_end_precision(self.start_precision, self.end_precision)
            .ok()
    }
}

impl<I> DoubleEndedIterator for PrecisionChange<I>
where
    I: DoubleEndedIterator,
    I::Item: PrecisionChangeOperable<Item = I::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()?
            .change_start_end_precision(self.start_precision, self.end_precision)
            .ok()
    }
}

/// A very ad-hoc trait for structures that can do unions
pub trait UnionOperable {
    type Item: UnionOperable;

    /// Try uniting the peer with the accumulated value using the given rules
    fn peer_union<'a, RI>(
        united_so_far: &Self,
        peeked: &Self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> RunningResult<Self::Item, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>;

    /// Try uniting the peer with the accumulated value using the given closure
    fn peer_union_with<F>(united_so_far: &Self, peeked: &Self, f: F) -> RunningResult<Self::Item, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>;
}

impl UnionOperable for AbsoluteBounds {
    type Item = Self;

    fn peer_union<'a, RI>(
        united_so_far: &Self,
        peeked: &Self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> RunningResult<Self::Item, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_union_with(united_so_far, peeked, |united_so_far, peeked| {
            unite_abs_bounds(united_so_far, peeked, rule_set, rules)
        })
    }

    fn peer_union_with<F>(united_so_far: &Self, peeked: &Self, mut f: F) -> RunningResult<Self::Item, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(united_so_far, peeked) {
            UnionResult::United(united) => RunningResult::Running(united),
            UnionResult::Separate(..) => RunningResult::Done(united_so_far.clone()),
        }
    }
}

impl UnionOperable for EmptiableAbsoluteBounds {
    type Item = Self;

    fn peer_union<'a, RI>(
        united_so_far: &Self,
        peeked: &Self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> RunningResult<Self::Item, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_union_with(united_so_far, peeked, |united_so_far, peeked| {
            unite_emptiable_abs_bounds(united_so_far, peeked, rule_set, rules)
        })
    }

    fn peer_union_with<F>(united_so_far: &Self, peeked: &Self, mut f: F) -> RunningResult<Self::Item, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(united_so_far, peeked) {
            UnionResult::United(united) => RunningResult::Running(united),
            UnionResult::Separate(..) => RunningResult::Done(united_so_far.clone()),
        }
    }
}

impl UnionOperable for AbsoluteInterval {
    type Item = Self;

    fn peer_union<'a, RI>(
        united_so_far: &Self,
        peeked: &Self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> RunningResult<Self::Item, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_union_with(united_so_far, peeked, |united_so_far, peeked| {
            unite_abs_intervals(united_so_far, peeked, rule_set, rules)
        })
    }

    fn peer_union_with<F>(united_so_far: &Self, peeked: &Self, mut f: F) -> RunningResult<Self::Item, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(united_so_far, peeked) {
            UnionResult::United(united) => RunningResult::Running(united),
            UnionResult::Separate(..) => RunningResult::Done(united_so_far.clone()),
        }
    }
}

/// Dispatcher trait for union iterators
pub trait UnitableIteratorDispatcher: Iterator + Sized {
    /// Unites peer intervals of the iterator using predefined rules
    fn peer_simple_union(self) -> PeerSimpleUnion<Peekable<Self>> {
        PeerSimpleUnion::new(self)
    }

    /// Unites peer intervals of the iterator using the given [`OverlapRuleSet`] and [`OverlapRule`]s
    fn peer_union<'a, RI>(self, rule_set: OverlapRuleSet, rules: &'a RI) -> PeerUnion<'a, Peekable<Self>, RI>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        PeerUnion::new(self, rule_set, rules)
    }

    /// Unites peer intervals of the iterator using the given closure
    fn peer_union_with<F>(self, f: F) -> PeerUnionWith<Peekable<Self>, F>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>,
    {
        PeerUnionWith::new(self, f)
    }
}

impl<I> UnitableIteratorDispatcher for I
where
    I: Iterator,
    I::Item: UnionOperable<Item = I::Item>,
{
}

/// Peer union iterator for intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerSimpleUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> PeerSimpleUnion<Peekable<I>>
where
    I: Iterator,
{
    pub fn new(iter: I) -> Self {
        PeerSimpleUnion {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<I> Iterator for PeerSimpleUnion<Peekable<I>>
where
    I: Iterator,
    I::Item: UnionOperable<Item = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next() else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(peeked) = self.iter.peek() else {
                self.exhausted = true;
                return Some(united_so_far);
            };

            let running_result = UnionOperable::peer_union(
                &united_so_far,
                peeked,
                OverlapRuleSet::default(),
                &DEFAULT_OVERLAP_RULES,
            );

            match running_result {
                RunningResult::Running(runner) => united_so_far = runner,
                RunningResult::Done(result) => return Some(result),
            }
        }
    }
}

impl<I> FusedIterator for PeerSimpleUnion<Peekable<I>>
where
    I: Iterator,
    I::Item: UnionOperable<Item = I::Item>,
{
}

/// Peer union iterator for intervals using the given [`OverlapRuleSet`] and given [`OverlapRule`]s
#[derive(Debug, Clone, Hash)]
pub struct PeerUnion<'u, I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: &'u RI,
    exhausted: bool,
}

impl<'u, I, RI> PeerUnion<'u, Peekable<I>, RI>
where
    I: Iterator,
    &'u RI: IntoIterator<Item = &'u OverlapRule>,
{
    pub fn new(iter: I, rule_set: OverlapRuleSet, rules: &'u RI) -> Self {
        PeerUnion {
            iter: iter.peekable(),
            rule_set,
            rules,
            exhausted: false,
        }
    }
}

impl<'u, I, RI> Iterator for PeerUnion<'u, Peekable<I>, RI>
where
    I: Iterator,
    I::Item: UnionOperable<Item = I::Item>,
    &'u RI: IntoIterator<Item = &'u OverlapRule>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next() else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(peeked) = self.iter.peek() else {
                self.exhausted = true;
                return Some(united_so_far);
            };

            let running_result = UnionOperable::peer_union(&united_so_far, peeked, self.rule_set, self.rules);

            match running_result {
                RunningResult::Running(runner) => united_so_far = runner,
                RunningResult::Done(result) => return Some(result),
            }
        }
    }
}

impl<'u, I, RI> FusedIterator for PeerUnion<'u, Peekable<I>, RI>
where
    I: Iterator,
    I::Item: UnionOperable<Item = I::Item>,
    &'u RI: IntoIterator<Item = &'u OverlapRule>,
{
}

/// Peer union iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerUnionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<I, F> PeerUnionWith<Peekable<I>, F>
where
    I: Iterator,
{
    pub fn new(iter: I, f: F) -> Self {
        PeerUnionWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<I, F> Iterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: UnionOperable<Item = I::Item>,
    F: for<'a> FnMut(&'a I::Item, &'a I::Item) -> UnionResult<I::Item, &'a I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next() else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(peeked) = self.iter.peek() else {
                self.exhausted = true;
                return Some(united_so_far);
            };

            let running_result = UnionOperable::peer_union_with(&united_so_far, peeked, &mut self.f);

            match running_result {
                RunningResult::Running(runner) => united_so_far = runner,
                RunningResult::Done(result) => return Some(result),
            }
        }
    }
}

impl<I, F> FusedIterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: UnionOperable<Item = I::Item>,
    F: for<'a> FnMut(&'a I::Item, &'a I::Item) -> UnionResult<I::Item, &'a I::Item>,
{
}

/// A very ad-hoc trait for structures that can do intersections
pub trait IntersectionOperable {
    type Item: IntersectionOperable;

    /// Intersects the current element with the peeked one using the given rules
    fn peer_intersection<'a, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: &'a RI) -> Self::Item
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>;

    /// Intersects the current element with the peeked one using the given closure
    fn peer_intersection_with<F>(current: &Self, peeked: &Self, f: F) -> Self::Item
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> IntersectionResult<Self::Item, &'a Self::Item>;
}

impl IntersectionOperable for AbsoluteBounds {
    type Item = Self;

    fn peer_intersection<'a, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: &'a RI) -> Self::Item
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_intersection_with(current, peeked, |current, peeked| {
            intersect_abs_bounds(current, peeked, rule_set, rules)
        })
    }

    fn peer_intersection_with<F>(current: &Self, peeked: &Self, mut f: F) -> Self::Item
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> IntersectionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(current, peeked) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate(..) => current.clone(),
        }
    }
}

impl IntersectionOperable for EmptiableAbsoluteBounds {
    type Item = Self;

    fn peer_intersection<'a, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: &'a RI) -> Self::Item
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_intersection_with(current, peeked, |current, peeked| {
            intersect_emptiable_abs_bounds(current, peeked, rule_set, rules)
        })
    }

    fn peer_intersection_with<F>(current: &Self, peeked: &Self, mut f: F) -> Self::Item
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> IntersectionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(current, peeked) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate(..) => current.clone(),
        }
    }
}

impl IntersectionOperable for AbsoluteInterval {
    type Item = Self;

    fn peer_intersection<'a, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: &'a RI) -> Self::Item
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_intersection_with(current, peeked, |current, peeked| {
            intersect_abs_intervals(current, peeked, rule_set, rules)
        })
    }

    fn peer_intersection_with<F>(current: &Self, peeked: &Self, mut f: F) -> Self::Item
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> IntersectionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(current, peeked) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate(..) => current.clone(),
        }
    }
}

/// Dispatcher trait for intersection iterators
pub trait IntersectableIteratorDispatcher: Iterator + Sized {
    /// Intersects peer intervals of the iterator using predefined rules
    fn peer_simple_intersection(self) -> PeerSimpleIntersection<Peekable<Self>> {
        PeerSimpleIntersection::new(self)
    }

    /// Intersects peer intervals of the iterator using the given [`OverlapRuleSet`] and [`OverlapRule`]s
    fn peer_intersection<'a, RI>(
        self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> PeerIntersection<'a, Peekable<Self>, RI>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        PeerIntersection::new(self, rule_set, rules)
    }

    /// Intersects peer intervals of the iterator using the given closure
    fn peer_intersection_with<F>(self, f: F) -> PeerIntersectionWith<Peekable<Self>, F>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> IntersectionResult<Self::Item, &'a Self::Item>,
    {
        PeerIntersectionWith::new(self, f)
    }
}

impl<I> IntersectableIteratorDispatcher for I
where
    I: Iterator,
    I::Item: IntersectionOperable<Item = I::Item>,
{
}

/// Intersection of peer intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerSimpleIntersection<I> {
    iter: I,
    exhausted: bool,
}

impl<I> PeerSimpleIntersection<Peekable<I>>
where
    I: Iterator,
{
    /// Creates a new instance of [`PeerSimpleIntersection`]
    pub fn new(iter: I) -> Self {
        PeerSimpleIntersection {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<I> Iterator for PeerSimpleIntersection<Peekable<I>>
where
    I: Iterator,
    I::Item: IntersectionOperable<Item = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next() else {
            self.exhausted = true;
            return None;
        };

        let Some(peeked) = self.iter.peek() else {
            self.exhausted = true;
            return Some(current);
        };

        Some(IntersectionOperable::peer_intersection(
            &current,
            peeked,
            OverlapRuleSet::default(),
            &DEFAULT_OVERLAP_RULES,
        ))
    }
}

impl<I> DoubleEndedIterator for PeerSimpleIntersection<Peekable<I>>
where
    I: DoubleEndedIterator,
    I::Item: IntersectionOperable<Item = I::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back() else {
            self.exhausted = true;
            return None;
        };

        // No early exhaustion check as peek() uses next() and not next_back()
        let peeked = self.iter.peek()?;

        Some(IntersectionOperable::peer_intersection(
            &current,
            peeked,
            OverlapRuleSet::default(),
            &DEFAULT_OVERLAP_RULES,
        ))
    }
}

impl<I> FusedIterator for PeerSimpleIntersection<Peekable<I>>
where
    I: Iterator,
    I::Item: IntersectionOperable<Item = I::Item>,
{
}

/// Intersection of peer intervals using the given rule set and rules
#[derive(Debug, Clone, Hash)]
pub struct PeerIntersection<'i, I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: &'i RI,
    exhausted: bool,
}

impl<'i, I, RI> PeerIntersection<'i, Peekable<I>, RI>
where
    I: Iterator,
{
    /// Creates a new instance of [`PeerIntersection`]
    pub fn new(iter: I, rule_set: OverlapRuleSet, rules: &'i RI) -> Self {
        PeerIntersection {
            iter: iter.peekable(),
            rule_set,
            rules,
            exhausted: false,
        }
    }
}

impl<'i, I, RI> Iterator for PeerIntersection<'i, Peekable<I>, RI>
where
    I: Iterator,
    I::Item: IntersectionOperable<Item = I::Item>,
    &'i RI: IntoIterator<Item = &'i OverlapRule>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next() else {
            self.exhausted = true;
            return None;
        };

        let Some(peeked) = self.iter.peek() else {
            self.exhausted = true;
            return Some(current);
        };

        Some(IntersectionOperable::peer_intersection(
            &current,
            peeked,
            self.rule_set,
            self.rules,
        ))
    }
}

impl<'i, I, RI> DoubleEndedIterator for PeerIntersection<'i, Peekable<I>, RI>
where
    I: DoubleEndedIterator,
    I::Item: IntersectionOperable<Item = I::Item>,
    &'i RI: IntoIterator<Item = &'i OverlapRule>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back() else {
            self.exhausted = true;
            return None;
        };

        // No early exhaustion check as peek() uses next() and not next_back()
        let peeked = self.iter.peek()?;

        Some(IntersectionOperable::peer_intersection(
            &current,
            peeked,
            self.rule_set,
            self.rules,
        ))
    }
}

impl<'i, I, RI> FusedIterator for PeerIntersection<'i, Peekable<I>, RI>
where
    I: Iterator,
    I::Item: IntersectionOperable<Item = I::Item>,
    &'i RI: IntoIterator<Item = &'i OverlapRule>,
{
}

/// Intersection of peer intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerIntersectionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<I, F> PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator,
{
    /// Creates a new instance of [`PeerIntersectionWith`]
    pub fn new(iter: I, f: F) -> Self {
        PeerIntersectionWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<I, F> Iterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: IntersectionOperable<Item = I::Item>,
    F: for<'a> FnMut(&'a I::Item, &'a I::Item) -> IntersectionResult<I::Item, &'a I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next() else {
            self.exhausted = true;
            return None;
        };

        let Some(peeked) = self.iter.peek() else {
            self.exhausted = true;
            return Some(current);
        };

        Some(IntersectionOperable::peer_intersection_with(
            &current,
            peeked,
            &mut self.f,
        ))
    }
}

impl<I, F> DoubleEndedIterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: DoubleEndedIterator,
    I::Item: IntersectionOperable<Item = I::Item>,
    F: for<'a> FnMut(&'a I::Item, &'a I::Item) -> IntersectionResult<I::Item, &'a I::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back() else {
            self.exhausted = true;
            return None;
        };

        // No early exhaustion check as peek() uses next() and not next_back()
        let peeked = self.iter.peek()?;

        Some(IntersectionOperable::peer_intersection_with(
            &current,
            peeked,
            &mut self.f,
        ))
    }
}

impl<I, F> FusedIterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: IntersectionOperable<Item = I::Item>,
    F: for<'a> FnMut(&'a I::Item, &'a I::Item) -> IntersectionResult<I::Item, &'a I::Item>,
{
}

pub trait DifferentiableIteratorDispatcher: Sized {
    fn difference_with_one(self, interval: AbsoluteInterval) -> DifferenceWithOne<Self> {
        todo!()
    }

    fn difference<J>(self, other: J) -> Difference<Self, J>
    where
        J: Iterator<Item = AbsoluteInterval>,
    {
        todo!()
    }

    fn difference_next_peer(self) -> DifferenceNextPeer<Self> {
        todo!("takes the next peer as the right-hand side operand for the difference")
    }

    fn difference_prev_peer(self) -> DifferencePreviousPeer<Self> {
        todo!("takes the previous peer as the right-hand side operand for the difference")
    }
}

// impl<I> DifferentiableIntervalIterator for I
// where
//     I: Iterator,
//     I::Item: DifferenceOperable<Item = I::Item>,
// {
// }

// TODO: REWORK TO GENERIC
pub trait SymmetricallyDifferentiableIteratorDispatcher: Sized {
    fn sym_difference_with_one(self, interval: AbsoluteInterval) -> SymmetricDifferenceWithOne<Self> {
        todo!()
    }

    fn sym_difference<J>(self, other: J) -> SymmetricDifference<Self, J>
    where
        J: IntoIterator<Item = AbsoluteInterval>,
    {
        todo!()
    }

    fn sym_difference_peer(self) -> SymmetricDifferencePeer<Self> {
        todo!("symmetric difference between pairs of elements")
    }
}

// impl<I> SymmetricallyDifferentiableIntervalIterator for I
// where
//     I: Iterator,
//     I::Item: SymmetricDifferenceOperable<Item = I::Item>,
// {
// }

// TODO: MOVE THOSE AND REWORK THEM
#[derive(Debug, Clone)]
pub struct DifferenceWithOne<I> {
    iter: I,
    interval: AbsoluteInterval,
}

#[derive(Debug, Clone)]
pub struct Difference<I, J> {
    iter: I,
    other_iter: J,
}

#[derive(Debug, Clone)]
pub struct DifferenceNextPeer<I> {
    iter: I,
}

#[derive(Debug, Clone)]
pub struct DifferencePreviousPeer<I> {
    iter: I,
}

#[derive(Debug, Clone)]
pub struct SymmetricDifferenceWithOne<I> {
    iter: I,
    interval: AbsoluteInterval,
}

#[derive(Debug, Clone)]
pub struct SymmetricDifference<I, J> {
    iter: I,
    other_iter: J,
}

#[derive(Debug, Clone)]
pub struct SymmetricDifferencePeer<I> {
    iter: I,
}

/// Ad-hoc trait for structures that can use overlap positioning
pub trait OverlapOperable {
    type Item: OverlapOperable;

    fn overlap() {}
}

#[derive(Debug, Clone, Hash)]
pub struct SimpleOverlap<I> {
    iter: I,
    interval: AbsoluteInterval,
    exhausted: bool,
}

impl<I> SimpleOverlap<I> {
    pub fn new(iter: I, interval: AbsoluteInterval) -> Self {
        SimpleOverlap {
            iter,
            interval,
            exhausted: false,
        }
    }
}

impl<I> Iterator for SimpleOverlap<I>
where
    I: Iterator,
    I::Item: CanPositionOverlap,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.iter.next()?;

            if current.simple_overlaps(&self.interval) {
                return Some(current);
            }
        }
    }
}

#[derive(Debug, Clone, Hash)]
pub struct Overlap<'o, I, RI> {
    iter: I,
    interval: AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: &'o RI,
    exhausted: bool,
}

#[derive(Debug, Clone)]
pub struct OverlapWith<I, F> {
    iter: I,
    interval: AbsoluteInterval,
    f: F,
    exhausted: bool,
}

/*
If we want to implement an operation "dispatcher" for multiple types, since we can easily run in the problem that
we can't do

impl<T: Iterator<Item = A>> CustomOperatorIter for T {}
impl<T: Iterator<Item = B>> CustomOperatorIter for T {}

as both have the signature `impl CustomOperatorIter for T` (associated type "Item" doesn't count),
we get a "conflicting implementations" error.

the solution is to do something like this:

struct Foo(u8);
struct Bar(u8);

trait CustomOperable {
    type Item: CustomOperable;
    fn custom_op(&self) -> Self::Item;
}

impl<T> CustomOperable for &T
where
    T: CustomOperable
{
    type Item = T::Item;
    fn custom_op(&self) -> Self::Item {
        (**self).custom_op()
    }
}

impl CustomOperable for Foo {
    type Item = Self;
    fn custom_op(&self) -> Self::Item {
        Self(self.0.saturating_add(1))
    }
}

impl CustomOperable for Bar {
    type Item = Self;
    fn custom_op(&self) -> Self::Item {
        Self(self.0.saturating_add(2))
    }
}

struct CustomIter<I> {
    iter: I,
}

impl<I> CustomIter<I> {
    fn new(iter: I) -> Self {
        CustomIter {
            iter,
        }
    }
}

impl<I> Iterator for CustomIter<I>
where
    I: Iterator,
    I::Item: CustomOperable<Item = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.custom_op())
    }
}

trait CustomIterDispatch: Iterator + Sized {
    fn custom_iter(self) -> CustomIter<Self> {
        CustomIter::new(self)
    }
}

impl<I> CustomIterDispatch for I
where
    I: Iterator,
    I::Item: CustomOperable<Item = I::Item>,
{}

Note: `where T: Iterator, T::Item: Operable` can also be written as `where T: Iterator<Item: Operable>`

In the future, implementing Iterator on a type that has non-overlapping trait bounds on its generics
will be allowed (see https://github.com/rust-lang/rust/issues/20400, emulation: https://github.com/rust-lang/rfcs/pull/1672#issuecomment-1405377983).
When this kind of implementations become standard, this crate should adopt it.
*/

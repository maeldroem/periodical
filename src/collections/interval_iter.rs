//! Implementations of iterators for intervals and operations between sets of intervals
//!
//! In this module you will find the different structures for lazy operations as well as their implementations
//! for dealing with intervals.
//!
//! For example, set operations, like unions, intersections, etc. But also operations like using a certain precision
//! to re-precise interval times.

use std::iter::Peekable;

use chrono::{DateTime, Utc};

use crate::intervals::interval::{ToAbsolute, ToRelative};
use crate::intervals::ops::{
    CanPositionOverlap, Extensible, OverlapRule, OverlapRuleSet, Precision, SIMPLE_OVERLAP_RULES,
    TryPreciseAbsoluteBounds,
};
use crate::intervals::{AbsoluteInterval, RelativeInterval};

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

// / Iterator trait to allow composition of multiple interval operations
// /
// / This is to extend [`Iterator`] in the same way that it works: if you create a map from an iterator,
// / you are still able to call methods like `filter` or `collect` on them.
// /
// / This trait seeks to extend it to include interval operations on all interval operation structures.

pub trait AbsoluteOrRelativeInterval {}

impl AbsoluteOrRelativeInterval for AbsoluteInterval {}

impl AbsoluteOrRelativeInterval for RelativeInterval {}

pub trait RelativeToAbsoluteIntervalIterator: Iterator + Sized {
    fn to_absolute(self, reference_time: DateTime<Utc>) -> RelativeToAbsolute<Self> {
        RelativeToAbsolute::new(self, reference_time)
    }
}

impl<I> RelativeToAbsoluteIntervalIterator for I where I: Iterator<Item = RelativeInterval> {}

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
    I: Iterator<Item = RelativeInterval>,
{
    type Item = AbsoluteInterval;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_absolute(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for RelativeToAbsolute<I>
where
    I: DoubleEndedIterator<Item = RelativeInterval>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.to_absolute(self.reference_time))
    }
}

pub trait AbsoluteToRelativeIntervalIterator: Iterator + Sized {
    fn to_relative(self, reference_time: DateTime<Utc>) -> AbsoluteToRelative<Self> {
        AbsoluteToRelative::new(self, reference_time)
    }
}

impl<I> AbsoluteToRelativeIntervalIterator for I where I: Iterator<Item = AbsoluteInterval> {}

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
    I: Iterator<Item = AbsoluteInterval>,
{
    type Item = RelativeInterval;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_relative(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for AbsoluteToRelative<I>
where
    I: DoubleEndedIterator<Item = AbsoluteInterval>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.to_relative(self.reference_time))
    }
}

pub trait PrecisionChangeIntervalIterator: Iterator + Sized {
    fn change_precision(self, precision: Precision) -> PrecisionChange<Self> {
        PrecisionChange::new(self, precision, precision)
    }

    fn change_start_end_precision(self, start_precision: Precision, end_precision: Precision) -> PrecisionChange<Self> {
        PrecisionChange::new(self, start_precision, end_precision)
    }
}

impl<I> PrecisionChangeIntervalIterator for I where I: Iterator<Item = AbsoluteInterval> {}

/// Changes the precision of start end end times
pub struct PrecisionChange<I> {
    iter: I,
    precision_start: Precision,
    precision_end: Precision,
}

impl<I> PrecisionChange<I> {
    pub fn new(iter: I, precision_start: Precision, precision_end: Precision) -> Self {
        PrecisionChange {
            iter,
            precision_start,
            precision_end,
        }
    }
}

impl<I> Iterator for PrecisionChange<I>
where
    I: Iterator<Item = AbsoluteInterval>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let bounds_option = self
                .iter
                .next()?
                .try_precise_bounds_with_different_precision(self.precision_start, self.precision_end)
                .ok();

            if let Some(bounds) = bounds_option {
                return Some(AbsoluteInterval::from(bounds));
            }
        }
    }
}

impl<I> DoubleEndedIterator for PrecisionChange<I>
where
    I: DoubleEndedIterator<Item = AbsoluteInterval>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let bounds_option = self
                .iter
                .next_back()?
                .try_precise_bounds_with_different_precision(self.precision_start, self.precision_end)
                .ok();

            if let Some(bounds) = bounds_option {
                return Some(AbsoluteInterval::from(bounds));
            }
        }
    }
}

pub trait UnitableIntervalIterator: Iterator + Sized {
    fn simple_union(self) -> SimpleUnion<Peekable<Self>> {
        SimpleUnion::new(self)
    }

    fn union<'a, RI>(self, rule_set: OverlapRuleSet, rules: &'a RI) -> Union<'a, Peekable<Self>, RI>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Union::new(self, rule_set, rules)
    }

    fn union_with<'a, F, E>(self, f: F) -> UnionWith<Peekable<Self>, F>
    where
        Self::Item: 'a,
        F: FnMut(Self::Item, Self::Item) -> Result<UnionResult<Self::Item, &'a Self::Item>, E>,
    {
        UnionWith::new(self, f)
    }
}

impl<I> UnitableIntervalIterator for I
where
    I: Iterator,
    I::Item: AbsoluteOrRelativeInterval,
{
}

/// Represents the result of a union
// NOTE: Perhaps move to another place since it's a generic that could be used for other things?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnionResult<U, S> {
    /// Union was successful, the united element is contained within this variant
    United(U),
    /// Union was unsuccessful, both elements involved are contained within this variant
    Separate(S, S),
}

#[derive(Debug, Clone, Hash)]
pub struct SimpleUnion<I> {
    iter: I,
}

impl<I> SimpleUnion<Peekable<I>>
where
    I: Iterator,
{
    pub fn new(iter: I) -> Self {
        SimpleUnion {
            // Instead of using
            // iter: Union::new(iter, OverlapRuleSet::Strict, &[OverlapRule::DenyAdjacency]),
            // We use simple_unite_abs_intervals() in the Iterator impl, so that when looking at what the final iterator
            // is composed of, we just see "SimpleUnion" and not
            // SimpleUnion<Union<Peekable<I>, &[OverlapRule]>>, which could be confusing
            iter: iter.peekable(),
        }
    }
}

impl<I> Iterator for SimpleUnion<Peekable<I>>
where
    I: Iterator<Item = AbsoluteInterval>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let mut united_interval = self.iter.next()?;

        loop {
            match self.iter.peek() {
                Some(peeked) => match simple_unite_abs_intervals(&united_interval, peeked) {
                    Ok(UnionResult::United(united)) => {
                        united_interval = united;
                    },
                    Ok(UnionResult::Separate(..)) | Err(()) => {
                        return Some(united_interval);
                    },
                },
                None => {
                    return Some(united_interval);
                },
            }
        }
    }
}

#[derive(Debug, Clone, Hash)]
pub struct Union<'u, I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: &'u RI,
}

impl<'u, I, RI> Union<'u, Peekable<I>, RI>
where
    I: Iterator,
    &'u RI: IntoIterator<Item = &'u OverlapRule>,
{
    pub fn new(iter: I, rule_set: OverlapRuleSet, rules: &'u RI) -> Self {
        Union {
            iter: iter.peekable(),
            rule_set,
            rules,
        }
    }
}

impl<'u, I, RI> Iterator for Union<'u, Peekable<I>, RI>
where
    I: Iterator<Item = AbsoluteInterval>,
    &'u RI: IntoIterator<Item = &'u OverlapRule>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let mut united_interval = self.iter.next()?;

        loop {
            match self.iter.peek() {
                Some(peeked) => match unite_abs_intervals(&united_interval, peeked, self.rule_set, self.rules) {
                    Ok(UnionResult::United(united)) => {
                        united_interval = united;
                    },
                    Ok(UnionResult::Separate(..)) | Err(()) => {
                        return Some(united_interval);
                    },
                },
                None => {
                    return Some(united_interval);
                },
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct UnionWith<I, F> {
    iter: I,
    f: F,
}

impl<I, F> UnionWith<Peekable<I>, F>
where
    I: Iterator,
{
    pub fn new(iter: I, f: F) -> Self {
        UnionWith {
            iter: iter.peekable(),
            f,
        }
    }
}

impl<I, F> Iterator for UnionWith<Peekable<I>, F>
where
    I: Iterator<Item = AbsoluteInterval>,
    // https://doc.rust-lang.org/nomicon/hrtb.html
    F: for<'a> Fn(
        &'a I::Item,
        &'a I::Item,
    ) -> Result<UnionResult<I::Item, &'a I::Item>, <I::Item as Extensible>::Error>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let mut united_interval = self.iter.next()?;

        loop {
            match self.iter.peek() {
                Some(peeked) => match (self.f)(&united_interval, peeked) {
                    Ok(UnionResult::United(united)) => {
                        united_interval = united;
                    },
                    Ok(UnionResult::Separate(..)) | Err(()) => {
                        return Some(united_interval);
                    },
                },
                None => {
                    return Some(united_interval);
                },
            }
        }
    }
}

fn simple_unite_abs_intervals<'a>(
    a: &'a AbsoluteInterval,
    b: &'a AbsoluteInterval,
) -> Result<UnionResult<AbsoluteInterval, &'a AbsoluteInterval>, <AbsoluteInterval as Extensible>::Error> {
    unite_abs_intervals(a, b, OverlapRuleSet::Strict, &SIMPLE_OVERLAP_RULES)
}

fn unite_abs_intervals<'a, 'b, RI>(
    a: &'a AbsoluteInterval,
    b: &'a AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: &'b RI,
) -> Result<UnionResult<AbsoluteInterval, &'a AbsoluteInterval>, <AbsoluteInterval as Extensible>::Error>
where
    &'b RI: IntoIterator<Item = &'b OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return Ok(UnionResult::Separate(a, b));
    }

    a.extend(b).map(UnionResult::United)
}

pub trait IntersectableIntervalIterator: Sized {
    fn simple_intersection(self) -> SimpleIntersection<Self> {
        todo!("Intersections of each pair of intervals")
    }

    fn intersection<RI>(self, rule_set: OverlapRuleSet, rules: RI) -> Intersection<Self, RI>
    where
        RI: IntoIterator<Item = AbsoluteInterval>,
    {
        todo!()
    }

    fn intersection_with<F, E>(self, f: F) -> IntersectionWith<Self, F>
    where
        F: FnMut(AbsoluteInterval, AbsoluteInterval) -> Result<IntersectionResult<AbsoluteInterval>, E>,
    {
        todo!()
    }

    fn intersection_with_one(self, interval: AbsoluteInterval) -> IntersectionWithOne<Self> {
        todo!()
    }
}

impl<I> IntersectableIntervalIterator for I where I: Iterator<Item = AbsoluteInterval> {}

pub trait DifferentiableIntervalIterator: Sized {
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

impl<I> DifferentiableIntervalIterator for I
where
    I: Iterator,
    I::Item: AbsoluteOrRelativeInterval,
{
}

pub trait SymmetricallyDifferentiableIntervalIterator: Sized {
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

impl<I> SymmetricallyDifferentiableIntervalIterator for I
where
    I: Iterator,
    I::Item: AbsoluteOrRelativeInterval,
{
}

/// Represents the result of an intersection
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntersectionResult<T> {
    /// Intersection was successful, the intersected element is contained within this variant
    Intersects(T),
    /// Intersection was unsuccessful, both elements involved are contained within this variant
    Separate(T, T),
}

#[derive(Debug, Clone)]
pub struct SimpleIntersection<I> {
    iter: I,
}

impl<I> SimpleIntersection<Peekable<I>>
where
    I: Iterator,
{
    pub fn new(iter: I) -> Self {
        SimpleIntersection { iter: iter.peekable() }
    }
}

#[derive(Debug, Clone)]
pub struct Intersection<I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: RI,
}

#[derive(Debug, Clone)]
pub struct IntersectionWith<I, F> {
    iter: I,
    f: F,
}

#[derive(Debug, Clone)]
pub struct IntersectionWithOne<I> {
    iter: I,
    interval: AbsoluteInterval,
}

/// Represents the result of a difference
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DifferenceResult<T> {
    /// Difference was successful, the difference of the two elements is contained within this variant
    Difference(T),
    /// Difference was unsuccessful, both elements involved are contained within this variant
    Separate(T, T),
}

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

/// Represents the result of a symmetric difference
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymmetricDifferenceResult<T> {
    /// Symmetric difference was successful, the symmetric difference of both elements is contained within this variant
    SymmetricDifference(T, T),
    /// Symmetric difference was unsuccessful, both elements involved are contained within this variant
    Separate(T, T),
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

/*
If we want to implement an operation "dispatcher" for multiple types, since we can easily run in the problem that
we can't do

impl<T: Iterator<Item = A>> CustomOperatorIter for T {}
impl<T: Iterator<Item = B>> CustomOperatorIter for T {}

as both have the signature `impl CustomOperatorIter for T` (associated type "Item" doesn't count),
we get a "conflicting implementations" error.

the solution is to do something like this:

trait Operation {
    fn my_custom_op(&self);
}

trait AOrB {
    fn my_custom_op<T: Iterator<Item = Self>>(&self);
}

impl AOrB for A {
    fn my_custom_op<T: Iterator<Item = Self>>(&self) {...}
}

impl AOrB for B {
    fn my_custom_op<T: Iterator<Item = Self>>(&self) {...}
}

impl<T> Operation for T
where
    T: Iterator,
    T::Item: AOrB,
{
    fn my_custom_op(&self) {
        <T::Item as AOrB>::my_custom_op(self);
    }
}

Note: `where T: Iterator, T::Item: AOrB` can also be written as `where T: Iterator<Item: AOrB>`
*/

//! Implementations of iterators for intervals and operations between sets of intervals
//!
//! In this module you will find the different structures for lazy operations as well as their implementations
//! for dealing with intervals.
//!
//! For example, set operations, like unions, intersections, etc. But also operations like using a certain precision
//! to re-precise interval times.

use std::collections::VecDeque;

use crate::intervals::Interval;
use crate::intervals::ops::{IntervalExtensionError, OverlapRule, OverlapRuleSet};

/// Simple iterator type containing [`Interval`]s
pub struct Intervals(VecDeque<Interval>);

impl Iterator for Intervals {
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_back()
    }
}

impl DoubleEndedIterator for Intervals {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }
}

impl FromIterator<Interval> for Intervals {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Interval>,
    {
        Intervals(iter.into_iter().collect::<VecDeque<Interval>>())
    }
}

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

/// Iterator trait to allow composition of multiple interval operations
///
/// This is to extend [`Iterator`] in the same way that it works: if you create a map from an iterator,
/// you are still able to call methods like `filter` or `collect` on them.
///
/// This trait seeks to extend it to include interval operations on all interval operation structures.
pub trait IntervalIterator: Iterator {
    fn simple_union(self) -> SimpleUnion<Self>
    where
        Self: Sized,
    {
        SimpleUnion::new(self)
    }

    fn union<RI>(self, rule_set: OverlapRuleSet, rules: RI) -> Union<Self, RI>
    where
        Self: Sized,
        RI: IntoIterator<Item = OverlapRule> + Clone,
    {
        Union::new(self, rule_set, rules)
    }

    fn union_with<F, E>(self, f: F) -> UnionWith<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Self::Item) -> Result<UnionResult<Self::Item>, E>,
    {
        UnionWith::new(self, f)
    }

    fn simple_intersection(self) -> SimpleIntersection<Self>
    where
        Self: Sized,
    {
        todo!("Intersections of each pair of intervals")
    }

    fn intersection<RI>(self, rule_set: OverlapRuleSet, rules: RI) -> Intersection<Self, RI>
    where
        Self: Sized,
        RI: IntoIterator<Item = Self::Item>,
    {
        todo!()
    }

    fn intersection_with<F, E>(self, f: F) -> IntersectionWith<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Self::Item) -> Result<IntersectionResult<Self::Item>, E>,
    {
        todo!()
    }

    fn intersection_with_one(self, interval: Self::Item) -> IntersectionWithOne<Self>
    where
        Self: Sized,
    {
        todo!()
    }

    fn difference_with_one(self, interval: Self::Item) -> DifferenceWithOne<Self>
    where
        Self: Sized,
    {
        todo!()
    }

    fn difference<J>(self, other: J) -> Difference<Self, J>
    where
        Self: Sized,
        J: IntoIterator<Item = Self::Item>,
    {
        todo!()
    }

    fn difference_next_peer(self) -> DifferenceNextPeer<Self>
    where
        Self: Sized,
    {
        todo!("takes the next peer as the right-hand side operand for the difference")
    }

    fn difference_prev_peer(self) -> DifferencePreviousPeer<Self>
    where
        Self: Sized,
    {
        todo!("takes the previous peer as the right-hand side operand for the difference")
    }

    fn sym_difference_with_one(self, interval: Self::Item) -> SymmetricDifferenceWithOne<Self>
    where
        Self: Sized,
    {
        todo!()
    }

    fn sym_difference<J>(self, other: J) -> SymmetricDifference<Self, J>
    where
        Self: Sized,
        J: IntoIterator<Item = Self::Item>,
    {
        todo!()
    }

    fn sym_difference_peer(self) -> SymmetricDifferencePeer<Self>
    where
        Self: Sized,
    {
        todo!("symmetric difference between pairs of elements")
    }
}

/// Represents the result of a union
// NOTE: Perhaps move to another place since it's a generic that could be used for other things?
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnionResult<T> {
    /// Union was successful, the united element is contained within this variant
    United(T),
    /// Union was unsuccessful, both elements involved are contained within this variant
    Separate(T, T),
}

#[derive(Debug, Clone)]
pub struct SimpleUnion<I> {
    iter: I,
    last_separate_interval: Option<Interval>,
}

impl<I> SimpleUnion<I> {
    /// Creates an instance of [`SimpleUnion`] using the given iterator
    pub fn new(iter: I) -> Self {
        SimpleUnion {
            iter,
            last_separate_interval: None,
        }
    }
}

impl<I> Iterator for SimpleUnion<I>
where
    I: Iterator<Item = Interval>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        // Unite until separate, then finally return the first united interval and process until all intervals are exhausted
        let mut united_interval: Option<Interval> = self.last_separate_interval.take();

        loop {
            let next_interval = self.iter.next()?;

            if united_interval.is_none() {
                united_interval = Some(next_interval);
                continue;
            }

            // Safe unwrap as check for None is present above
            match simple_unite_intervals(united_interval.as_ref().unwrap(), next_interval) {
                Ok(UnionResult::United(new_united)) => {
                    united_interval = Some(new_united);
                },
                Ok(UnionResult::Separate(_, new_basis)) => {
                    self.last_separate_interval = Some(new_basis);
                    break;
                },
                Err(_) => break,
            }
        }

        united_interval
    }
}

impl<I> IntervalIterator for SimpleUnion<I> where I: Iterator<Item = Interval> {}

#[derive(Debug, Clone)]
pub struct Union<I, RI> {
    iter: I,
    last_separate_interval: Option<Interval>,
    rule_set: OverlapRuleSet,
    rules: RI,
}

impl<I, RI> Union<I, RI> {
    pub fn new(iter: I, rule_set: OverlapRuleSet, rules: RI) -> Self {
        Union {
            iter,
            last_separate_interval: None,
            rule_set,
            rules,
        }
    }
}

impl<I, RI> Iterator for Union<I, RI>
where
    I: Iterator<Item = Interval>,
    RI: IntoIterator<Item = OverlapRule> + Clone,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        let mut united_interval: Option<Interval> = self.last_separate_interval.take();

        loop {
            let next_interval = self.iter.next()?;

            if united_interval.is_none() {
                united_interval = Some(next_interval);
                continue;
            }

            // Safe unwrap of `united_intervals` as check for None is present above
            // Perhaps the cloning of self.rules is unnecessary, but how can we make it a reference without having
            // all elements of the iterator as references when the into-iterable object is created?
            // Perhaps impl IntoIterator<Item = Borrow<Interval>>? idk
            match unite_intervals(
                united_interval.as_ref().unwrap(),
                next_interval,
                self.rule_set,
                self.rules.clone(),
            ) {
                Ok(UnionResult::United(new_united)) => {
                    united_interval = Some(new_united);
                },
                Ok(UnionResult::Separate(_, new_basis)) => {
                    self.last_separate_interval = Some(new_basis);
                    break;
                },
                Err(_) => break,
            }
        }

        united_interval
    }
}

impl<I, RI> IntervalIterator for Union<I, RI>
where
    I: Iterator<Item = Interval>,
    RI: IntoIterator<Item = OverlapRule> + Clone,
{
}

#[derive(Debug, Clone)]
pub struct UnionWith<I, F> {
    iter: I,
    last_separate_interval: Option<Interval>,
    f: F,
}

impl<I, F> UnionWith<I, F> {
    pub fn new(iter: I, f: F) -> Self {
        UnionWith {
            iter,
            last_separate_interval: None,
            f,
        }
    }
}

impl<I, F, E> Iterator for UnionWith<I, F>
where
    I: Iterator<Item = Interval>,
    F: Fn(Interval, Interval) -> Result<UnionResult<Interval>, E>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        let mut united_interval: Option<Interval> = self.last_separate_interval.take();

        loop {
            let next_interval = self.iter.next()?;

            if united_interval.is_none() {
                united_interval = Some(next_interval);
                continue;
            }

            // Safe unwrap of `united_intervals` as check for None is present above
            match (self.f)(united_interval.clone().unwrap(), next_interval) {
                Ok(UnionResult::United(new_united)) => {
                    united_interval = Some(new_united);
                },
                Ok(UnionResult::Separate(_, new_basis)) => {
                    self.last_separate_interval = Some(new_basis);
                    break;
                },
                Err(_) => break,
            }
        }

        united_interval
    }
}

impl<I, F, E> IntervalIterator for UnionWith<I, F>
where
    I: Iterator<Item = Interval>,
    F: Fn(Interval, Interval) -> Result<UnionResult<Interval>, E>,
{
}

fn simple_unite_intervals(a: &Interval, b: Interval) -> Result<UnionResult<Interval>, IntervalExtensionError> {
    unite_intervals(a, b, OverlapRuleSet::Strict, [OverlapRule::DenyAdjacency])
}

fn unite_intervals(
    a: &Interval,
    b: Interval,
    rule_set: OverlapRuleSet,
    rules: impl IntoIterator<Item = OverlapRule>,
) -> Result<UnionResult<Interval>, IntervalExtensionError> {
    if !a.overlaps(&b, rule_set, rules) {
        return Ok(UnionResult::Separate(a.clone(), b));
    }

    a.try_extend(&b).map(UnionResult::United)
}

/// Represents the result of an intersection
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum IntersectionResult<T> {
    /// Intersection was successful, the intersected element is contained within this variant
    Intersects(T),
    /// Intersection was unsuccessful, both elements involved are contained within this variant
    Separate(T, T),
}

#[derive(Debug, Clone)]
pub struct SimpleIntersection<I> {
    iter: I,
    last_interval: Option<Interval>,
}

impl<I> SimpleIntersection<I> {
    pub fn new(iter: I) -> Self {
        SimpleIntersection {
            iter,
            last_interval: None,
        }
    }
}

impl<I> Iterator for SimpleIntersection<I>
where
    I: Iterator<Item = Interval>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next_interval = self.iter.next()?;

        // match self.last_interval {
        //     Some(last_interval) =>
        // }
        todo!()
    }
}

impl<I> IntervalIterator for SimpleIntersection<I> where I: Iterator<Item = Interval> {}

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
    interval: Interval,
}

/// Represents the result of a difference
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DifferenceResult<T> {
    /// Difference was successful, the difference of the two elements is contained within this variant
    Difference(T),
    /// Difference was unsuccessful, both elements involved are contained within this variant
    Separate(T, T),
}

#[derive(Debug, Clone)]
pub struct DifferenceWithOne<I> {
    iter: I,
    interval: Interval,
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
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SymmetricDifferenceResult<T> {
    /// Symmetric difference was successful, the symmetric difference of both elements is contained within this variant
    SymmetricDifference(T, T),
    /// Symmetric difference was unsuccessful, both elements involved are contained within this variant
    Separate(T, T),
}

#[derive(Debug, Clone)]
pub struct SymmetricDifferenceWithOne<I> {
    iter: I,
    interval: Interval,
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

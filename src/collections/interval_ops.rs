//! Implementations of operation structures
//! 
//! In this module you will find the different structures for lazy operations as well as their implementations
//! for dealing with intervals.
//! 
//! For example, set operations, like unions, intersections, etc. But also operations like using a certain precision
//! to re-precise interval times.

use crate::intervals::comparison::{OverlapRule, OverlapRuleSet};
use crate::intervals::Interval;

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
// Do other iterators like those
// Since that would make them specialized, I think the set operations traits defined in set_ops.rs are not needed
// or should be rethought. Current opinion: those set operations should be implemented for intervals, schedules, etc.
// but since they are simple enough, we should just remove them for now, implement the specialized iterators,
// continue developing the lib until we can rule whether such traits are needed

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
        todo!()
    }

    fn union<RI>(self, rule_set: OverlapRuleSet, rules: RI) -> Union<Self, RI>
    where
        Self: Sized,
        RI: IntoIterator<Item = OverlapRule>,
    {
        todo!()
    }

    fn union_with<F>(self, f: F) -> UnionWith<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Self::Item) -> Self::Item,
    {
        todo!()
    }

    fn simple_union_to_one(self) -> SimpleUnionToOne<Self>
    where
        Self: Sized,
    {
        todo!()
    }

    fn union_to_one<RI>(self, rule_set: OverlapRuleSet, rules: RI) -> UnionToOne<Self, RI>
    where
        Self: Sized,
        RI: IntoIterator<Item = OverlapRule>,
    {
        todo!()
    }

    fn union_to_one_with<F>(self, f: F) -> UnionToOneWith<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Self::Item) -> Option<Self::Item>,
    {
        todo!()
    }
}

pub struct SimpleUnion<I> {
    iter: I,
}

impl<I> SimpleUnion<I> {
    pub fn new(iter: I) -> Self {
        SimpleUnion {
            iter
        }
    }
}

impl<I> Iterator for SimpleUnion<I>
where
    I: IntoIterator<Item = Interval>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<I> IntervalIterator for SimpleUnion<I>
where
    I: IntoIterator<Item = Interval>,
{}

pub struct Union<I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: RI,
}

impl<I, RI> Union<I, RI> {
    pub fn new(iter: I, rule_set: OverlapRuleSet, rules: RI) -> Self {
        Union {
            iter,
            rule_set,
            rules,
        }
    }
}

impl<I, RI> Iterator for Union<I, RI>
where
    I: IntoIterator<Item = Interval>,
    RI: IntoIterator<Item = OverlapRule>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<I, RI> IntervalIterator for Union<I, RI>
where
    I: IntoIterator<Item = Interval>,
    RI: IntoIterator<Item = OverlapRule>,
{}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnionResult<T> {
    United(T),
    Separate(T),
}

pub struct UnionWith<I, F> {
    iter: I,
    f: F,
}

impl<I, F> UnionWith<I, F> {
    pub fn new(iter: I, f: F) -> Self {
        UnionWith {
            iter,
            f,
        }
    }
}

impl<I, F> Iterator for UnionWith<I, F>
where
    I: IntoIterator<Item = Interval>,
    F: Fn(Interval, Interval) -> UnionResult<Interval>,
{
    type Item = Interval;
 
    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<I, F> IntervalIterator for UnionWith<I, F>
where
    I: IntoIterator<Item = Interval>,
    F: Fn(Interval, Interval) -> UnionResult<Interval>,
{}

pub struct SimpleUnionToOne<I> {
    iter: I,
}

impl<I> SimpleUnionToOne<I> {
    pub fn new(iter: I) -> Self {
        SimpleUnionToOne {
            iter,
        }
    }
}

impl<I> Iterator for SimpleUnionToOne<I>
where
    I: IntoIterator<Item = Interval>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<I> IntervalIterator for SimpleUnionToOne<I>
where
    I: IntoIterator<Item = Interval>,
{}

pub struct UnionToOne<I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: RI,
}

impl<I, RI> UnionToOne<I, RI> {
    pub fn new(iter: I, rule_set: OverlapRuleSet, rules: RI) -> Self {
        UnionToOne {
            iter,
            rule_set,
            rules,
        }
    }
}

impl<I, RI> Iterator for UnionToOne<I, RI>
where
    I: IntoIterator<Item = Interval>,
    RI: IntoIterator<Item = OverlapRule>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<I, RI> IntervalIterator for UnionToOne<I, RI>
where
    I: IntoIterator<Item = Interval>,
    RI: IntoIterator<Item = OverlapRule>,
{}

pub struct UnionToOneWith<I, F> {
    iter: I,
    f: F,
}

impl<I, F> UnionToOneWith<I, F> {
    pub fn new(iter: I, f: F) -> Self {
        UnionToOneWith {
            iter,
            f,
        }
    }
}

impl<I, F> Iterator for UnionToOneWith<I, F>
where
    I: IntoIterator<Item = Interval>,
    F: Fn(Interval, Interval) -> Option<Interval>,
{
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<I, F> IntervalIterator for UnionToOneWith<I, F>
where
    I: IntoIterator<Item = Interval>,
    F: Fn(Interval, Interval) -> Option<Interval>,
{}

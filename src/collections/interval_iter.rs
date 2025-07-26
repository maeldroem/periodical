//! Implementations of iterators for intervals and operations between sets of intervals
//!
//! In this module you will find the different structures for lazy operations as well as their implementations
//! for dealing with intervals.
//!
//! For example, set operations, like unions, intersections, etc. But also operations like using a certain precision
//! to re-precise interval times.

use std::iter::{FusedIterator, Peekable};

use chrono::{DateTime, RoundingError, Utc};

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteInterval, EmptiableAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::ops::overlap_position::{DEFAULT_OVERLAP_RULES, OverlapRule, OverlapRuleSet};
use crate::intervals::ops::precision::PreciseAbsoluteBounds;
use crate::intervals::ops::relativity_conversion::{ToAbsolute, ToRelative};
use crate::intervals::ops::set_ops::{
    intersect_abs_bounds, intersect_emptiable_abs_bounds, unite_abs_bounds, unite_emptiable_abs_bounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HasEmptiableRelativeBounds, RelativeBounds, RelativeInterval,
};
use crate::ops::{
    DifferenceResult, IntersectionResult, Precision, RunningResult, SymmetricDifferenceResult, UnionResult,
};

/// A very ad-hoc trait for structures that can do intersections
pub trait PeerIntersectionOperable {
    type Item: PeerIntersectionOperable;

    /// Intersects the current element with the peeked one using the given rules
    fn peer_intersection<'ri, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: RI) -> Self::Item
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    /// Intersects the current element with the peeked one using the given closure
    fn peer_intersection_with<F>(current: &Self, peeked: &Self, f: F) -> Self::Item
    where
        F: FnMut(&Self::Item, &Self::Item) -> IntersectionResult<Self::Item>;
}

impl PeerIntersectionOperable for AbsoluteBounds {
    type Item = Self;

    fn peer_intersection<'ri, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: RI) -> Self::Item
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        match intersect_abs_bounds(current, peeked, rule_set, rules) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate => current.clone(),
        }
    }

    fn peer_intersection_with<F>(current: &Self, peeked: &Self, mut f: F) -> Self::Item
    where
        F: FnMut(&Self::Item, &Self::Item) -> IntersectionResult<Self::Item>,
    {
        match (f)(current, peeked) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate => current.clone(),
        }
    }
}

impl PeerIntersectionOperable for EmptiableAbsoluteBounds {
    type Item = Self;

    fn peer_intersection<'ri, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: RI) -> Self::Item
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        match intersect_emptiable_abs_bounds(current, peeked, rule_set, rules) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate => current.clone(),
        }
    }

    fn peer_intersection_with<F>(current: &Self, peeked: &Self, mut f: F) -> Self::Item
    where
        F: FnMut(&Self::Item, &Self::Item) -> IntersectionResult<Self::Item>,
    {
        match (f)(current, peeked) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate => current.clone(),
        }
    }
}

impl PeerIntersectionOperable for AbsoluteInterval {
    type Item = Self;

    fn peer_intersection<'ri, RI>(current: &Self, peeked: &Self, rule_set: OverlapRuleSet, rules: RI) -> Self::Item
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        match intersect_emptiable_abs_bounds(
            &current.emptiable_abs_bounds(),
            &peeked.emptiable_abs_bounds(),
            rule_set,
            rules,
        ) {
            IntersectionResult::Intersected(intersected) => AbsoluteInterval::from(intersected),
            IntersectionResult::Separate => current.clone(),
        }
    }

    fn peer_intersection_with<F>(current: &Self, peeked: &Self, mut f: F) -> Self::Item
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> IntersectionResult<Self::Item>,
    {
        match (f)(current, peeked) {
            IntersectionResult::Intersected(intersected) => intersected,
            IntersectionResult::Separate => current.clone(),
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
    fn peer_intersection<'ri, RI>(self, rule_set: OverlapRuleSet, rules: RI) -> PeerIntersection<Peekable<Self>, RI>
    where
        RI: IntoIterator<Item = &'ri OverlapRule> + Clone,
    {
        PeerIntersection::new(self, rule_set, rules)
    }

    /// Intersects peer intervals of the iterator using the given closure
    fn peer_intersection_with<F>(self, f: F) -> PeerIntersectionWith<Peekable<Self>, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> IntersectionResult<Self::Item>,
    {
        PeerIntersectionWith::new(self, f)
    }
}

impl<I> IntersectableIteratorDispatcher for I
where
    I: Iterator,
    I::Item: PeerIntersectionOperable<Item = I::Item>,
{
}

/// Intersection of peer intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerSimpleIntersection<I> {
    iter: I,
    exhausted: bool,
}

impl<I> PeerSimpleIntersection<I>
where
    I: Iterator,
{
    /// Creates a new instance of [`PeerSimpleIntersection`]
    pub fn new(iter: I) -> PeerSimpleIntersection<Peekable<I>> {
        PeerSimpleIntersection {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<I> Iterator for PeerSimpleIntersection<Peekable<I>>
where
    I: Iterator,
    I::Item: PeerIntersectionOperable<Item = I::Item>,
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

        Some(PeerIntersectionOperable::peer_intersection(
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
    I::Item: PeerIntersectionOperable<Item = I::Item>,
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

        Some(PeerIntersectionOperable::peer_intersection(
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
    I::Item: PeerIntersectionOperable<Item = I::Item>,
{
}

/// Intersection of peer intervals using the given rule set and rules
#[derive(Debug, Clone, Hash)]
pub struct PeerIntersection<I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: RI,
    exhausted: bool,
}

impl<I, RI> PeerIntersection<I, RI>
where
    I: Iterator,
{
    /// Creates a new instance of [`PeerIntersection`]
    pub fn new(iter: I, rule_set: OverlapRuleSet, rules: RI) -> PeerIntersection<Peekable<I>, RI> {
        PeerIntersection {
            iter: iter.peekable(),
            rule_set,
            rules,
            exhausted: false,
        }
    }
}

impl<'ri, I, RI> Iterator for PeerIntersection<Peekable<I>, RI>
where
    I: Iterator,
    I::Item: PeerIntersectionOperable<Item = I::Item>,
    RI: IntoIterator<Item = &'ri OverlapRule> + Clone,
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

        Some(PeerIntersectionOperable::peer_intersection(
            &current,
            peeked,
            self.rule_set,
            self.rules.clone(),
        ))
    }
}

impl<'ri, I, RI> DoubleEndedIterator for PeerIntersection<Peekable<I>, RI>
where
    I: DoubleEndedIterator,
    I::Item: PeerIntersectionOperable<Item = I::Item>,
    RI: IntoIterator<Item = &'ri OverlapRule> + Clone,
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

        Some(PeerIntersectionOperable::peer_intersection(
            &current,
            peeked,
            self.rule_set,
            self.rules.clone(),
        ))
    }
}

impl<'ri, I, RI> FusedIterator for PeerIntersection<Peekable<I>, RI>
where
    I: Iterator,
    I::Item: PeerIntersectionOperable<Item = I::Item>,
    RI: IntoIterator<Item = &'ri OverlapRule> + Clone,
{
}

/// Intersection of peer intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerIntersectionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<I, F> PeerIntersectionWith<I, F>
where
    I: Iterator,
{
    /// Creates a new instance of [`PeerIntersectionWith`]
    pub fn new(iter: I, f: F) -> PeerIntersectionWith<Peekable<I>, F> {
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
    I::Item: PeerIntersectionOperable<Item = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> IntersectionResult<I::Item>,
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

        Some(PeerIntersectionOperable::peer_intersection_with(
            &current,
            peeked,
            &mut self.f,
        ))
    }
}

impl<I, F> DoubleEndedIterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: DoubleEndedIterator,
    I::Item: PeerIntersectionOperable<Item = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> IntersectionResult<I::Item>,
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

        Some(PeerIntersectionOperable::peer_intersection_with(
            &current,
            peeked,
            &mut self.f,
        ))
    }
}

impl<I, F> FusedIterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: PeerIntersectionOperable<Item = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> IntersectionResult<I::Item>,
{
}

/// A very ad-hoc trait for structures that can be differentiated (_differentiated_ as set difference)
pub trait DifferenceOperable<Rhs = Self> {
    type Output: DifferenceOperable<Rhs>;

    fn difference<'ri, RI>(a: Self, b: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> Self::Output
    where
        RI: IntoIterator<Item = &'ri OverlapRule>;

    fn difference_with<F>(a: Self, b: &Rhs, f: F) -> Self::Output
    where
        F: FnMut(&Self, &Rhs) -> DifferenceResult<Self::Output>;
}

impl<Rhs> DifferenceOperable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn difference<'ri, RI>(a: Self, b: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> Self::Output
    where
        RI: IntoIterator<Item = &'ri OverlapRule>,
    {
        todo!()
    }

    fn difference_with<F>(a: Self, b: &Rhs, f: F) -> Self::Output
    where
        F: FnMut(&Self, &Rhs) -> DifferenceResult<Self::Output>,
    {
        todo!()
    }
}

/// Dispatcher trait for difference iterators
pub trait DifferentiableIteratorDispatcher: Iterator + Sized {
    fn difference_with_one<B>(self, comparator: B) -> DifferenceWithOne<Peekable<Self>, B> {
        DifferenceWithOne::new(self, comparator)
    }

    fn difference<J, O>(self, other_iter: J) -> Difference<Self, J>
    where
        J: IntoIterator + Clone,
    {
        Difference::new(self, other_iter)
    }

    fn difference_next_peer(self) -> DifferenceNextPeer<Self> {
        todo!("takes the next peer as the right-hand side operand for the difference")
    }

    fn difference_prev_peer(self) -> DifferencePreviousPeer<Self> {
        todo!("takes the previous peer as the right-hand side operand for the difference")
    }
}

impl<I> DifferentiableIteratorDispatcher for I
where
    I: Iterator,
    I::Item: DifferenceOperable<Output = I::Item>,
{
}

#[derive(Debug, Clone)]
pub struct DifferenceWithOne<I, B> {
    iter: I,
    comparator: B,
    exhausted: bool,
}

impl<I, B> DifferenceWithOne<I, B>
where
    I: Iterator,
{
    pub fn new(iter: I, comparator: B) -> DifferenceWithOne<Peekable<I>, B> {
        DifferenceWithOne {
            iter: iter.peekable(),
            comparator,
            exhausted: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Difference<I, J> {
    iter: I,
    other_iter: J,
    exhausted: bool,
}

impl<I, J> Difference<I, J> {
    pub fn new(iter: I, other_iter: J) -> Difference<I, J> {
        Difference {
            iter,
            other_iter,
            exhausted: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DifferenceNextPeer<I> {
    iter: I,
    exhausted: bool,
}

#[derive(Debug, Clone)]
pub struct DifferencePreviousPeer<I> {
    iter: I,
    exhausted: bool,
}

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

// impl<I> Iterator for SimpleOverlap<I>
// where
//     I: Iterator,
//     I::Item: CanPositionOverlap,
// {
//     type Item = I::Item;

//     fn next(&mut self) -> Option<Self::Item> {
//         loop {
//             let current = self.iter.next()?;

//             if current.simple_overlaps(&self.interval) {
//                 return Some(current);
//             }
//         }
//     }
// }

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
    type Output: CustomOperable;
    fn custom_op(&self) -> Self::Output;
}

impl<T> CustomOperable for &T
where
    T: CustomOperable
{
    type Output = T::Output;
    fn custom_op(&self) -> Self::Output {
        (**self).custom_op()
    }
}

impl CustomOperable for Foo {
    type Output = Self;
    fn custom_op(&self) -> Self::Output {
        Self(self.0.saturating_add(1))
    }
}

impl CustomOperable for Bar {
    type Output = Self;
    fn custom_op(&self) -> Self::Output {
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
    I::Item: CustomOperable<Output = I::Item>,
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
    I::Item: CustomOperable<Output = I::Item>,
{}

Note: `where T: Iterator, T::Item: Operable` can also be written as `where T: Iterator<Item: Operable>`

In the future, implementing Iterator on a type that has non-overlapping trait bounds on its generics
will be allowed (see https://github.com/rust-lang/rust/issues/20400, emulation: https://github.com/rust-lang/rfcs/pull/1672#issuecomment-1405377983).
When this kind of implementations become standard, this crate should adopt it.
*/

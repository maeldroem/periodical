//! Implementations of iterators for intervals and operations between sets of intervals
//!
//! In this module you will find the different structures for lazy operations as well as their implementations
//! for dealing with intervals.
//!
//! For example, set operations, like unions, intersections, etc. But also operations like using a certain precision
//! to re-precise interval times.

use std::iter::{FusedIterator, Peekable};
use std::ops::ControlFlow;

use chrono::{DateTime, RoundingError, Utc};

use crate::intervals::interval::{
    AbsoluteBounds, AbsoluteBoundsOrEmpty, HasAbsoluteBounds, HasRelativeBounds, RelativeBounds, RelativeBoundsOrEmpty,
    ToAbsolute, ToRelative,
};
use crate::intervals::ops::{
    CanPositionOverlap, Extensible, OverlapRule, OverlapRuleSet, PreciseAbsoluteBounds, Precision, SIMPLE_OVERLAP_RULES,
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

impl RelativeToAbsoluteOperable for RelativeBoundsOrEmpty {
    type Item = AbsoluteBoundsOrEmpty;

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
pub trait RelativeToAbsoluteIntervalIterator: Iterator + Sized {
    /// Converts [`RelativeInterval`]s to [`AbsoluteInterval`]s
    fn to_absolute(self, reference_time: DateTime<Utc>) -> RelativeToAbsolute<Self> {
        RelativeToAbsolute::new(self, reference_time)
    }
}

impl<I> RelativeToAbsoluteIntervalIterator for I
where
    I: Iterator,
    I::Item: RelativeToAbsoluteOperable,
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
    I::Item: RelativeToAbsoluteOperable,
{
    type Item = <I::Item as RelativeToAbsoluteOperable>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_absolute(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for RelativeToAbsolute<I>
where
    I: DoubleEndedIterator,
    I::Item: RelativeToAbsoluteOperable,
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

impl AbsoluteToRelativeOperable for AbsoluteBoundsOrEmpty {
    type Item = RelativeBoundsOrEmpty;

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
pub trait AbsoluteToRelativeIntervalIterator: Iterator + Sized {
    /// Converts [`AbsoluteInterval`]s to [`RelativeInterval`]s
    fn to_relative(self, reference_time: DateTime<Utc>) -> AbsoluteToRelative<Self> {
        AbsoluteToRelative::new(self, reference_time)
    }
}

impl<I> AbsoluteToRelativeIntervalIterator for I
where
    I: Iterator,
    I::Item: AbsoluteToRelativeOperable,
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
    I::Item: AbsoluteToRelativeOperable,
{
    type Item = <I::Item as AbsoluteToRelativeOperable>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_relative(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for AbsoluteToRelative<I>
where
    I: DoubleEndedIterator,
    I::Item: AbsoluteToRelativeOperable,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.to_relative(self.reference_time))
    }
}

/// Ad-hoc trait for structures that can change their bounds' precision
pub trait PrecisionChangeOperable {
    type Item: PrecisionChangeOperable;
    type Error;

    fn change_start_end_precision(&self, start_precision: Precision, end_precision: Precision) -> Result<Self::Item, Self::Error>;
}

impl<T: Sized + PrecisionChangeOperable> PrecisionChangeOperable for &T {
    type Item = T::Item;
    type Error = T::Error;

    fn change_start_end_precision(&self, start_precision: Precision, end_precision: Precision) -> Result<Self::Item, Self::Error> {
        (**self).change_start_end_precision(start_precision, end_precision)
    }
}

impl<T: Sized + PrecisionChangeOperable> PrecisionChangeOperable for &mut T {
    type Item = T::Item;
    type Error = T::Error;

    fn change_start_end_precision(&self, start_precision: Precision, end_precision: Precision) -> Result<Self::Item, Self::Error> {
        (**self).change_start_end_precision(start_precision, end_precision)
    }
}

impl PrecisionChangeOperable for AbsoluteBounds {
    type Item = Self;
    type Error = RoundingError;

    fn change_start_end_precision(&self, start_precision: Precision, end_precision: Precision) -> Result<Self::Item, Self::Error> {
        self.precise_bounds_with_different_precisions(start_precision, end_precision)
    }
}

impl PrecisionChangeOperable for AbsoluteBoundsOrEmpty {
    type Item = Self;
    type Error = RoundingError;

    fn change_start_end_precision(&self, start_precision: Precision, end_precision: Precision) -> Result<Self::Item, Self::Error> {
        self.precise_bounds_with_different_precisions(start_precision, end_precision)
    }
}

impl PrecisionChangeOperable for AbsoluteInterval {
    type Item = Self;
    type Error = RoundingError;

    fn change_start_end_precision(&self, start_precision: Precision, end_precision: Precision) -> Result<Self::Item, Self::Error> {
        self.precise_bounds_with_different_precisions(start_precision, end_precision)
    }
}

/// Dispatcher trait for the [`PrecisionChange`] iterator
pub trait PrecisionChangeIntervalIterator: Iterator + Sized {
    /// Changes the precision of the interval with the given [`Precision`]
    fn change_precision(self, precision: Precision) -> PrecisionChange<Self> {
        PrecisionChange::new(self, precision, precision)
    }

    /// Changes the precision of start and end bounds with the given [`Precision`]s
    fn change_start_end_precision(self, start_precision: Precision, end_precision: Precision) -> PrecisionChange<Self> {
        PrecisionChange::new(self, start_precision, end_precision)
    }
}

impl<I> PrecisionChangeIntervalIterator for I
where
    I: Iterator,
    I::Item: PrecisionChangeOperable,
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
    I::Item: PrecisionChangeOperable,
{
    type Item = <I::Item as PrecisionChangeOperable>::Item;

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
    I::Item: PrecisionChangeOperable,
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

    fn peer_union<'a, RI>(
        united_so_far: &Self,
        peeked: &Self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>;

    fn peer_union_with<F>(
        united_so_far: &Self,
        peeked: &Self,
        f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>;

    fn union<'a, OgIter, OtherIter, RI>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        &'a RI: IntoIterator<Item = &'a OverlapRule>;

    fn union_with<OgIter, OtherIter, F>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>;
}

impl UnionOperable for AbsoluteBounds {
    type Item = Self;

    fn peer_union<'a, RI>(
        united_so_far: &Self,
        peeked: &Self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_union_with(
            united_so_far,
            peeked,
            |united_so_far, peeked| unite_abs_bounds(united_so_far, peeked, rule_set, rules)
        )
    }

    fn peer_union_with<F>(
        united_so_far: &Self,
        peeked: &Self,
        mut f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(united_so_far, peeked) {
            UnionResult::United(united) => ControlFlow::Continue(united),
            UnionResult::Separate(..) => ControlFlow::Break(Some(united_so_far.clone())),
        }
    }

    fn union<'a, OgIter, OtherIter, RI>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        &'a RI: IntoIterator<Item = &'a OverlapRule>
    {
        Self::union_with(
            og_iter,
            other_iter,
            united_so_far,
            exhausted,
            |united_so_far, peeked| unite_abs_bounds(united_so_far, peeked, rule_set, rules),
        )
    }

    fn union_with<OgIter, OtherIter, F>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        mut f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>
    {
        let peeked_union_with_og = og_iter
            .peek()
            .map(|peeked| (f)(united_so_far, peeked));
        let peeked_union_with_other = other_iter
            .peek()
            .map(|peeked| (f)(united_so_far, peeked));

        match (peeked_union_with_og, peeked_union_with_other) {
            (Some(UnionResult::United(og_united)), Some(UnionResult::United(other_united))) => {
                // Both iterators should advance as we used peeked values
                og_iter.next();
                other_iter.next();

                ControlFlow::Continue(og_united.extend(&other_united))
            },
            (Some(UnionResult::United(og_united)), _) => {
                // Since the peeked interval of `other_iter` was separate, we only advance `og_iter`
                og_iter.next();

                ControlFlow::Continue(og_united)
            },
            (_, Some(UnionResult::United(other_united))) => {
                // Since the peeked interval of `og_iter` was separate, we only advance `other_iter`
                other_iter.next();

                ControlFlow::Continue(other_united)
            },
            (None, None) => {
                // Don't know how to return the `exhausted` info other than using a mutable pointer to the flag
                *exhausted = true;
                ControlFlow::Break(Some(united_so_far.clone()))
            },
            (peeked_union_with_og, peeked_union_with_other) => {
                // We advance any iterator that isn't exhausted for the next iteration,
                // then return the united interval
                // Note about exhaustion: peeked values are kept within Peekable, so calling peek() multiple
                // times is cheap (if the peekable iterator hasn't advanced)
                if peeked_union_with_og.is_some() {
                    og_iter.next();
                }

                if peeked_union_with_other.is_some() {
                    other_iter.next();
                }

                ControlFlow::Break(Some(united_so_far.clone()))
            },
        }
    }
}

impl UnionOperable for AbsoluteBoundsOrEmpty {
    type Item = Self;

    fn peer_union<'a, RI>(
        united_so_far: &Self,
        peeked: &Self,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_union_with(
            united_so_far,
            peeked,
            |united_so_far, peeked| unite_abs_bounds_or_empty(united_so_far, peeked, rule_set, rules)
        )
    }

    fn peer_union_with<F>(
        united_so_far: &Self,
        peeked: &Self,
        mut f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(united_so_far, peeked) {
            UnionResult::United(united) => ControlFlow::Continue(united),
            UnionResult::Separate(..) => ControlFlow::Break(Some(united_so_far.clone())),
        }
    }

    fn union<'a, OgIter, OtherIter, RI>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        &'a RI: IntoIterator<Item = &'a OverlapRule>
    {
        Self::union_with(
            og_iter,
            other_iter,
            united_so_far,
            exhausted,
            |united_so_far, peeked| unite_abs_bounds_or_empty(united_so_far, peeked, rule_set, rules),
        )
    }

    fn union_with<OgIter, OtherIter, F>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        mut f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>
    {
        let peeked_union_with_og = og_iter
            .peek()
            .map(|peeked| (f)(united_so_far, peeked));
        let peeked_union_with_other = other_iter
            .peek()
            .map(|peeked| (f)(united_so_far, peeked));

        match (peeked_union_with_og, peeked_union_with_other) {
            (Some(UnionResult::United(og_united)), Some(UnionResult::United(other_united))) => {
                // Both iterators should advance as we used peeked values
                og_iter.next();
                other_iter.next();

                ControlFlow::Continue(og_united.extend(&other_united))
            },
            (Some(UnionResult::United(og_united)), _) => {
                // Since the peeked interval of `other_iter` was separate, we only advance `og_iter`
                og_iter.next();

                ControlFlow::Continue(og_united)
            },
            (_, Some(UnionResult::United(other_united))) => {
                // Since the peeked interval of `og_iter` was separate, we only advance `other_iter`
                other_iter.next();

                ControlFlow::Continue(other_united)
            },
            (None, None) => {
                // Don't know how to return the `exhausted` info other than using a mutable pointer to the flag
                *exhausted = true;
                ControlFlow::Break(Some(united_so_far.clone()))
            },
            (peeked_union_with_og, peeked_union_with_other) => {
                // We advance any iterator that isn't exhausted for the next iteration,
                // then return the united interval
                // Note about exhaustion: peeked values are kept within Peekable, so calling peek() multiple
                // times is cheap (if the peekable iterator hasn't advanced)
                if peeked_union_with_og.is_some() {
                    og_iter.next();
                }

                if peeked_union_with_other.is_some() {
                    other_iter.next();
                }

                ControlFlow::Break(Some(united_so_far.clone()))
            },
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
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Self::peer_union_with(
            united_so_far,
            peeked,
            |united_so_far, peeked| unite_abs_intervals(
                united_so_far,
                peeked,
                rule_set,
                rules,
            ),
        )
    }

    fn peer_union_with<F>(
        united_so_far: &Self,
        peeked: &Self,
        mut f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>,
    {
        match (f)(united_so_far, peeked) {
            UnionResult::United(united) => ControlFlow::Continue(united),
            UnionResult::Separate(..) => ControlFlow::Break(Some(united_so_far.clone())),
        }
    }

    fn union<'a, OgIter, OtherIter, RI>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        &'a RI: IntoIterator<Item = &'a OverlapRule>
    {
        Self::union_with(
            og_iter,
            other_iter,
            united_so_far,
            exhausted,
            |united_so_far, peeked| unite_abs_intervals(united_so_far, peeked, rule_set, rules),
        )
    }

    fn union_with<OgIter, OtherIter, F>(
        og_iter: &mut Peekable<OgIter>,
        other_iter: &mut Peekable<OtherIter>,
        united_so_far: &Self,
        exhausted: &mut bool,
        mut f: F,
    ) -> ControlFlow<Option<Self::Item>, Self::Item>
    where
        OgIter: Iterator<Item = Self::Item>,
        OtherIter: Iterator<Item = Self::Item>,
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> UnionResult<Self::Item, &'a Self::Item>
    {
        let peeked_union_with_og = og_iter
            .peek()
            .map(|peeked| (f)(united_so_far, peeked));
        let peeked_union_with_other = other_iter
            .peek()
            .map(|peeked| (f)(united_so_far, peeked));

        match (peeked_union_with_og, peeked_union_with_other) {
            (Some(UnionResult::United(og_united)), Some(UnionResult::United(other_united))) => {
                // Both iterators should advance as we used peeked values
                og_iter.next();
                other_iter.next();

                ControlFlow::Continue(og_united.extend(&other_united))
            },
            (Some(UnionResult::United(og_united)), _) => {
                // Since the peeked interval of `other_iter` was separate, we only advance `og_iter`
                og_iter.next();

                ControlFlow::Continue(og_united)
            },
            (_, Some(UnionResult::United(other_united))) => {
                // Since the peeked interval of `og_iter` was separate, we only advance `other_iter`
                other_iter.next();

                ControlFlow::Continue(other_united)
            },
            (None, None) => {
                // Don't know how to return the `exhausted` info other than using a mutable pointer to the flag
                *exhausted = true;
                ControlFlow::Break(Some(united_so_far.clone()))
            },
            (peeked_union_with_og, peeked_union_with_other) => {
                // We advance any iterator that isn't exhausted for the next iteration,
                // then return the united interval
                // Note about exhaustion: peeked values are kept within Peekable, so calling peek() multiple
                // times is cheap (if the peekable iterator hasn't advanced)
                if peeked_union_with_og.is_some() {
                    og_iter.next();
                }

                if peeked_union_with_other.is_some() {
                    other_iter.next();
                }

                ControlFlow::Break(Some(united_so_far.clone()))
            },
        }
    }
}

fn unite_abs_bounds<'a, 'b, RI>(
    a: &'a AbsoluteBounds,
    b: &'a AbsoluteBounds,
    rule_set: OverlapRuleSet,
    rules: &'b RI,
) -> UnionResult<AbsoluteBounds, &'a AbsoluteBounds>
where
    &'b RI: IntoIterator<Item = &'b OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate(a, b);
    }

    UnionResult::United(a.extend(b))
}

fn unite_abs_bounds_or_empty<'a, 'b, RI>(
    a: &'a AbsoluteBoundsOrEmpty,
    b: &'a AbsoluteBoundsOrEmpty,
    rule_set: OverlapRuleSet,
    rules: &'b RI,
) -> UnionResult<AbsoluteBoundsOrEmpty, &'a AbsoluteBoundsOrEmpty>
where
    &'b RI: IntoIterator<Item = &'b OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate(a, b);
    }

    UnionResult::United(a.extend(b))
}

fn unite_abs_intervals<'a, 'b, RI>(
    a: &'a AbsoluteInterval,
    b: &'a AbsoluteInterval,
    rule_set: OverlapRuleSet,
    rules: &'b RI,
) -> UnionResult<AbsoluteInterval, &'a AbsoluteInterval>
where   
    &'b RI: IntoIterator<Item = &'b OverlapRule>,
{
    if !a.overlaps(b, rule_set, rules) {
        return UnionResult::Separate(a, b);
    }

    UnionResult::United(a.extend(b))
}

/// Dispatcher trait for union iterators
pub trait UnitableIntervalIterator: Iterator + Sized {
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

    /// Unites two interval iterators using predefined rule
    ///
    /// Both iterators must be chronologically ordered, otherwise this results in undefined results
    fn simple_union<I>(self, other: I) -> SimpleUnion<Peekable<Self>, Peekable<<I as IntoIterator>::IntoIter>>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        SimpleUnion::new(self, other.into_iter())
    }

    /// Unites two interval iterators using the given [`OverlapRuleSet`] and [`OverlapRule`]s
    fn union<'a, I, RI>(
        self,
        other: I,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> Union<'a, Peekable<Self>, Peekable<<I as IntoIterator>::IntoIter>, RI>
    where
        I: IntoIterator<Item = Self::Item>,
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        Union::new(self, other.into_iter(), rule_set, rules)
    }

    /// Unites two interval iterators using the given closure
    fn union_with<I, F, E>(
        self,
        other: I,
        f: F,
    ) -> UnionWith<Peekable<Self>, Peekable<<I as IntoIterator>::IntoIter>, F>
    where
        I: IntoIterator<Item = Self::Item>,
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> Result<IntersectionResult<Self::Item, &'a Self::Item>, E>,
    {
        UnionWith::new(self, other.into_iter(), f)
    }
}

impl<I> UnitableIntervalIterator for I
where
    I: Iterator,
    I::Item: UnionOperable,
{
}

/// Represents the result of a union
// NOTE: Perhaps move to another place since it's a generic that could be used for other things?
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnionResult<U, S> {
    /// Union was successful, the united element is contained within this variant
    United(U),
    /// Union was unsuccessful, both elements involved are contained within this variant
    Separate(S, S),
}

impl<U, S> UnionResult<U, S> {
    /// Maps the contents of the [`United`](UnionResult::United) variant
    pub fn map_united<F, T>(self, f: F) ->  UnionResult<T, S>
    where
        F: FnOnce(U) -> T,
    {
        match self {
            UnionResult::United(u) => UnionResult::United((f)(u)),
            UnionResult::Separate(a, b) => UnionResult::Separate(a, b),
        }
    }

    /// Maps the contents of the [`Separate`](UnionResult::Separate) variant
    pub fn map_separate<F, T>(self, f: F) ->  UnionResult<U, T>
    where
        F: FnOnce((S, S)) -> (T, T),
    {
        match self {
            UnionResult::United(u) => UnionResult::United(u),
            UnionResult::Separate(a, b) => {
                let new_separate = (f)((a, b));
                UnionResult::Separate(new_separate.0, new_separate.1)
            },
        }
    }
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
            // Instead of using PeerUnion as a proxy, we use simple_unite_abs_intervals() in the Iterator impl,
            // so that when looking at what the final iterator is composed of, we just see "PeerSimpleUnion" and not
            // PeerSimpleUnion<PeerUnion<Peekable<I>, &[OverlapRule]>>, which could be confusing
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<I> Iterator for PeerSimpleUnion<Peekable<I>>
where
    I: Iterator,
    I::Item: UnionOperable,
{
    type Item = <I::Item as UnionOperable>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next() else {
            self.exhausted = true;
            return None;
        };

        loop {
            if let Some(peeked) = self.iter.peek() {
                let tmp = UnionOperable::peer_union(
                    &united_so_far,
                    peeked,
                    OverlapRuleSet::Strict,
                    &SIMPLE_OVERLAP_RULES
                );

                match tmp {
                    ControlFlow::Continue(x) => {
                        // Error here: mismatched type
                        // united_so_far is `I::Item`
                        //             x is `<I::Item as UnionOperable>::Item`
                        // both are concretely equal to `impl UnionOperable` though
                        united_so_far = x;
                    },
                    ControlFlow::Break(y) => {
                        return y;
                    } 
                }
            }

            self.exhausted = true;
            return Some(united_so_far);
        }
    }
}

impl<I> FusedIterator for PeerSimpleUnion<Peekable<I>> where I: Iterator<Item = AbsoluteInterval> {}

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
    I::Item: UnionOperable,
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
            if let Some(peeked) = self.iter.peek() {
                united_so_far = UnionOperable::peer_union(&united_so_far, peeked, self.rule_set, self.rules)?;
            }

            self.exhausted = true;
            return Some(united_so_far);
        }
    }
}

impl<'u, I, RI> FusedIterator for PeerUnion<'u, Peekable<I>, RI>
where
    I: Iterator<Item = AbsoluteInterval>,
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
    I::Item: UnionOperable,
    // https://doc.rust-lang.org/nomicon/hrtb.html
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
            if let Some(peeked) = self.iter.peek() {
                united_so_far = UnionOperable::peer_union_with(&united_so_far, peeked, self.f)?;
            }

            self.exhausted = true;
            return Some(united_so_far);
        }
    }
}

impl<I, F> FusedIterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator<Item = AbsoluteInterval>,
    F: for<'a> FnMut(&'a I::Item, &'a I::Item) -> UnionResult<I::Item, &'a I::Item>,
{
}

/// Union of intervals of two sets using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct SimpleUnion<I, O> {
    iter: I,
    other: O,
    exhausted: bool,
}

impl<I, O> SimpleUnion<Peekable<I>, Peekable<O>>
where
    I: Iterator,
    O: Iterator,
{
    pub fn new(iter: I, other: O) -> Self {
        SimpleUnion {
            iter: iter.peekable(),
            other: other.peekable(),
            exhausted: false,
        }
    }
}

impl<I, O> Iterator for SimpleUnion<Peekable<I>, Peekable<O>>
where
    I: Iterator<Item = AbsoluteInterval>,
    O: Iterator<Item = AbsoluteInterval>,
{
    type Item = AbsoluteInterval;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().or_else(|| self.other.next()) else {
            self.exhausted = true;
            return None;
        };

        loop {
            united_so_far = UnionOperable::union(
                &mut self.iter,
                &mut self.other,
                &united_so_far,
                &mut self.exhausted,
                OverlapRuleSet::Strict,
                SIMPLE_OVERLAP_RULES
            )?;
        }
    }
}

impl<I, O> FusedIterator for SimpleUnion<Peekable<I>, Peekable<O>>
where
    I: Iterator<Item = AbsoluteInterval>,
    O: Iterator<Item = AbsoluteInterval>,
{
}

/// Union of intervals of two sets using the given [`OverlapRuleSet`] and [`OverlapRule`]s
#[derive(Debug, Clone, Hash)]
pub struct Union<'u, I, O, RI> {
    iter: I,
    other: O,
    rule_set: OverlapRuleSet,
    rules: &'u RI,
    exhausted: bool,
}

impl<'u, I, O, RI> Union<'u, Peekable<I>, Peekable<O>, RI>
where
    I: Iterator,
    O: Iterator,
{
    pub fn new(iter: I, other: O, rule_set: OverlapRuleSet, rules: &'u RI) -> Self
    where
        &'u RI: IntoIterator<Item = &'u OverlapRule>,
    {
        Union {
            iter: iter.peekable(),
            other: other.peekable(),
            rule_set,
            rules,
            exhausted: false,
        }
    }
}

impl<'u, I, O, RI> Iterator for Union<'u, Peekable<I>, Peekable<O>, &'u RI>
where
    I: Iterator<Item = AbsoluteInterval>,
    O: Iterator<Item = AbsoluteInterval>,
    &'u RI: IntoIterator<Item = &'u OverlapRule>,
{
    type Item = AbsoluteInterval;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().or_else(|| self.other.next()) else {
            self.exhausted = true;
            return None;
        };

        loop {
            united_so_far = UnionOperable::union(
                &mut self.iter,
                self.other,
                &united_so_far, 
                &mut self.exhausted,
                self.rule_set,
                self.rules
            )?;
        }
    }
}

impl<'u, I, O, RI> FusedIterator for Union<'u, Peekable<I>, Peekable<O>, &'u RI>
where
    I: Iterator<Item = AbsoluteInterval>,
    O: Iterator<Item = AbsoluteInterval>,
    &'u RI: IntoIterator<Item = &'u OverlapRule>,
{
}

/// Union of intervals of two sets using the given closure
#[derive(Debug, Clone)]
pub struct UnionWith<I, O, F> {
    iter: I,
    other: O,
    f: F,
    exhausted: bool,
}

impl<I, O, F> UnionWith<Peekable<I>, Peekable<O>, F>
where
    I: Iterator,
    O: Iterator,
{
    pub fn new(iter: I, other: O, f: F) -> Self {
        UnionWith {
            iter: iter.peekable(),
            other: other.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<I, O, F> Iterator for UnionWith<Peekable<I>, Peekable<O>, F>
where
    I: Iterator<Item = AbsoluteInterval>,
    O: Iterator<Item = AbsoluteInterval>,
    F: for<'a> FnMut(&'a AbsoluteInterval, &'a AbsoluteInterval) -> UnionResult<AbsoluteInterval, &'a AbsoluteInterval>,
{
    type Item = AbsoluteInterval;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().or_else(|| self.other.next()) else {
            self.exhausted = true;
            return None;
        };

        loop {
            united_so_far = UnionOperable::union_with(
                &mut self.iter,
                self.other,
                &united_so_far, 
                &mut self.exhausted,
                self.f,
            )?;
        }
    }
}

impl<I, O, F> FusedIterator for UnionWith<Peekable<I>, Peekable<O>, F>
where
    I: Iterator<Item = AbsoluteInterval>,
    O: Iterator<Item = AbsoluteInterval>,
    F: for<'a> FnMut(&'a AbsoluteInterval, &'a AbsoluteInterval) -> UnionResult<AbsoluteInterval, &'a AbsoluteInterval>,
{
}

/// Dispatcher trait for intersection iterators
pub trait IntersectableIntervalIterator: Iterator + Sized {
    /// Intersects peer intervals of the iterator using predefined rules
    fn peer_simple_intersection(self) -> PeerSimpleIntersection<Self> {
        todo!("Intersections of each pair of intervals")
    }

    /// Intersects peer intervals of the iterator using the given [`OverlapRuleSet`] and [`OverlapRule`]s
    fn peer_intersection<'a, RI>(self, rule_set: OverlapRuleSet, rules: &'a RI) -> PeerIntersection<'a, Self, RI>
    where
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        todo!()
    }

    /// Intersects peer intervals of the iterator using the given closure
    fn peer_intersection_with<F, E>(self, f: F) -> PeerIntersectionWith<Self, F>
    where
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> Result<IntersectionResult<Self::Item, &'a Self::Item>, E>,
    {
        todo!()
    }

    /// Intersection of intervals against another set of intervals using predefined rules
    fn simple_intersection<'a, I>(self, other: I) -> SimpleIntersection<Self, <I as IntoIterator>::IntoIter>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        todo!()
    }

    /// Intersection of intervals against another set of intervals using the given [`OverlapRuleSet`] and [`OverlapRule`]s
    fn intersection<'a, I, RI>(
        self,
        other: I,
        rule_set: OverlapRuleSet,
        rules: &'a RI,
    ) -> Intersection<'a, Self, <I as IntoIterator>::IntoIter, RI>
    where
        I: IntoIterator<Item = Self::Item>,
        &'a RI: IntoIterator<Item = &'a OverlapRule>,
    {
        todo!()
    }

    /// Intersection of intervals against another set of intervals using the given closure
    fn intersection_with<I, F, E>(self, other: I, f: F) -> IntersectionWith<Self, <I as IntoIterator>::IntoIter, F>
    where
        I: IntoIterator<Item = Self::Item>,
        F: for<'a> FnMut(&'a Self::Item, &'a Self::Item) -> Result<IntersectionResult<Self::Item, &'a Self::Item>, E>,
    {
        todo!()
    }
}

impl<I> IntersectableIntervalIterator for I where I: Iterator<Item = AbsoluteInterval> {}

/// Represents the result of an intersection
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntersectionResult<I, S> {
    /// Intersection was successful, the intersected element is contained within this variant
    Intersects(I),
    /// Intersection was unsuccessful, both elements involved are contained within this variant
    Separate(S, S),
}

/// Intersection of peer intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerSimpleIntersection<I> {
    iter: I,
}

impl<I> PeerSimpleIntersection<Peekable<I>>
where
    I: Iterator,
{
    pub fn new(iter: I) -> Self {
        PeerSimpleIntersection { iter: iter.peekable() }
    }
}

impl<I> Iterator for PeerSimpleIntersection<Peekable<I>>
where
    I: Iterator<Item = AbsoluteInterval>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.iter.next()?;

        todo!()
    }
}

/// Intersection of peer intervals using the given rule set and rules
#[derive(Debug, Clone, Hash)]
pub struct PeerIntersection<'i, I, RI> {
    iter: I,
    rule_set: OverlapRuleSet,
    rules: &'i RI,
}

/// Intersection of peer intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerIntersectionWith<I, F> {
    iter: I,
    f: F,
}

/// Intersection of intervals of two sets using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct SimpleIntersection<I, O> {
    iter: I,
    others: O,
}

/// Intersection of intervals of two sets using the given [`OverlapRuleSet`] and [`OverlapRule`]s
#[derive(Debug, Clone, Hash)]
pub struct Intersection<'i, I, O, RI> {
    iter: I,
    others: O,
    rule_set: OverlapRuleSet,
    rules: &'i RI,
}

/// Intersection of intervals of two sets using the given closure
#[derive(Debug, Clone)]
pub struct IntersectionWith<I, O, F> {
    iter: I,
    others: O,
    f: F,
}

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

// impl<I> DifferentiableIntervalIterator for I
// where
//     I: Iterator,
//     I::Item: DifferenceOperable,
// {
// }

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

// impl<I> SymmetricallyDifferentiableIntervalIterator for I
// where
//     I: Iterator,
//     I::Item: SymmetricDifferenceOperable,
// {
// }

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
    I::Item: CustomOperable,
{
    type Item = <I::Item as CustomOperable>::Item;

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
    I::Item: CustomOperable,
{}

Note: `where T: Iterator, T::Item: Operable` can also be written as `where T: Iterator<Item: Operable>`
*/

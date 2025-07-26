//! Interval iterators regarding interval union

use std::iter::{FusedIterator, Peekable};

use crate::intervals::meta::Interval;
use crate::intervals::prelude::*;
use crate::ops::UnionResult;

/// Dispatcher trait for peer union iterators
pub trait PeerUnitableIteratorDispatcher: Iterator + Sized {
    /// Unites peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the union. If the union is successful,
    /// it returns the united interval. If it is unsuccessful, it returns the current element.
    fn peer_union(self) -> PeerUnion<Peekable<Self>> {
        PeerUnion::new(self)
    }

    /// Unites peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the union. If the union is successful,
    /// it returns the united interval. If it is unsuccessful, it returns the current element.
    fn peer_union_with<F>(self, f: F) -> PeerUnionWith<Peekable<Self>, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> UnionResult<Self::Item>,
    {
        PeerUnionWith::new(self, f)
    }
}

impl<I> PeerUnitableIteratorDispatcher for I
where
    I: Iterator,
    I::Item: Unitable<Output = I::Item>,
{
}

/// Peer union iterator for intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> PeerUnion<I>
where
    I: Iterator,
{
    pub fn new(iter: I) -> PeerUnion<Peekable<I>> {
        PeerUnion {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<I> Iterator for PeerUnion<Peekable<I>>
where
    I: Iterator,
    I::Item: Unitable<Output = I::Item>,
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

        match current.unite(peeked) {
            UnionResult::United(united) => Some(united),
            UnionResult::Separate => Some(current),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerUnion

impl<I> FusedIterator for PeerUnion<Peekable<I>>
where
    I: Iterator,
    I::Item: Unitable<Output = I::Item>,
{
}

/// Peer union iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerUnionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<I, F> PeerUnionWith<I, F>
where
    I: Iterator,
{
    pub fn new(iter: I, f: F) -> PeerUnionWith<Peekable<I>, F> {
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
    I::Item: Unitable<Output = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> UnionResult<I::Item>,
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

        match (self.f)(&current, peeked) {
            UnionResult::United(united) => Some(united),
            UnionResult::Separate => Some(current),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerUnionWith

impl<I, F> FusedIterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: Unitable<Output = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> UnionResult<I::Item>,
{
}

/// Dispatcher trait for union iterators
pub trait UnitableIteratorDispatcher: Iterator + Sized {
    /// Unites each item with every overlapping element of the given other iterator using the predefined overlap rules
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn union<J>(self, other_iter: J) -> Union<Self, J>
    where
        J: IntoIterator + Clone,
    {
        Union::new(self, other_iter)
    }

    /// Unites each item with every overlapping element of the given other iterator using the given closure
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn union_with<J, F>(self, other_iter: J, f: F) -> UnionWith<Self, J, F>
    where
        J: IntoIterator + Clone,
        F: FnMut(&Self::Item, J::Item) -> UnionResult<Self::Item>,
    {
        UnionWith::new(self, other_iter, f)
    }
}

impl<I> UnitableIteratorDispatcher for I
where
    I: Iterator,
    I::Item: Interval, // Unitable<O, Output = I::Item>,
{
}

#[derive(Debug, Clone, Hash)]
pub struct Union<I, J> {
    iter: I,
    other_iter: J,
    exhausted: bool,
}

impl<I, J> Union<I, J> {
    pub fn new(iter: I, other_iter: J) -> Self {
        Union {
            iter,
            other_iter,
            exhausted: false,
        }
    }
}

impl<'o, I, J, O> Iterator for Union<I, J>
where
    I: Iterator,
    I::Item: Unitable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
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

        Some(self.other_iter.clone().into_iter().fold(
            current,
            |united_so_far, other| match united_so_far.unite(other) {
                UnionResult::United(united) => united,
                UnionResult::Separate => united_so_far,
            },
        ))
    }
}

impl<'o, I, J, O> DoubleEndedIterator for Union<I, J>
where
    I: DoubleEndedIterator,
    I::Item: Unitable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back() else {
            self.exhausted = true;
            return None;
        };

        Some(self.other_iter.clone().into_iter().fold(
            current,
            |united_so_far, other| match united_so_far.unite(other) {
                UnionResult::United(united) => united,
                UnionResult::Separate => united_so_far,
            },
        ))
    }
}

impl<'o, I, J, O> FusedIterator for Union<I, J>
where
    I: Iterator,
    I::Item: Unitable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
}

#[derive(Debug, Clone)]
pub struct UnionWith<I, J, F> {
    iter: I,
    other_iter: J,
    f: F,
    exhausted: bool,
}

impl<I, J, F> UnionWith<I, J, F> {
    pub fn new(iter: I, other_iter: J, f: F) -> Self {
        UnionWith {
            iter,
            other_iter,
            f,
            exhausted: false,
        }
    }
}

impl<'o, I, J, O, F> Iterator for UnionWith<I, J, F>
where
    I: Iterator,
    I::Item: Unitable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&I::Item, &'o O) -> UnionResult<I::Item>,
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

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .fold(current, |united_so_far, other| match (self.f)(&united_so_far, other) {
                    UnionResult::United(united) => united,
                    UnionResult::Separate => united_so_far,
                }),
        )
    }
}

impl<'o, I, J, O, F> DoubleEndedIterator for UnionWith<I, J, F>
where
    I: DoubleEndedIterator,
    I::Item: Unitable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&I::Item, &'o O) -> UnionResult<I::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .fold(current, |united_so_far, other| match (self.f)(&united_so_far, other) {
                    UnionResult::United(united) => united,
                    UnionResult::Separate => united_so_far,
                }),
        )
    }
}

impl<'o, I, J, O, F> FusedIterator for UnionWith<I, J, F>
where
    I: DoubleEndedIterator,
    I::Item: Unitable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&I::Item, &O) -> UnionResult<I::Item>,
{
}

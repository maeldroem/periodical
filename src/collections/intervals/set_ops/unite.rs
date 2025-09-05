//! Interval iterators regarding interval union

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::UnionResult;

/// Dispatcher trait for accumulative union iterators
pub trait AccumulativelyUnitableIteratorDispatcher: IntoIterator + Sized {
    /// Accumulatively unites intervals of the iterator using the default overlap rules
    fn acc_union(self) -> AccumulativeUnion<Peekable<Self::IntoIter>> {
        AccumulativeUnion::new(self.into_iter())
    }

    /// Accumulatively unites intervals of the iterator using the given closure
    fn acc_union_with<'a, T, F>(self, f: F) -> AccumulativeUnionWith<Peekable<Self::IntoIter>, F>
    where
        Self::IntoIter: Iterator<Item = &'a T>,
        T: 'a + Unitable<Output = T> + Clone,
        F: FnMut(&T, &T) -> UnionResult<T>,
    {
        AccumulativeUnionWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T> AccumulativelyUnitableIteratorDispatcher for I
where
    I: IntoIterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
{
}

/// Accumulative union iterator using the predefined rules
#[derive(Debug, Clone, Hash)]
pub struct AccumulativeUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> AccumulativeUnion<I>
where
    I: Iterator,
{
    pub fn new(iter: I) -> AccumulativeUnion<Peekable<I>> {
        AccumulativeUnion {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<'a, I, T> Iterator for AccumulativeUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().cloned() else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(peeked) = self.iter.peek() else {
                self.exhausted = true;
                return Some(united_so_far);
            };

            match united_so_far.unite(peeked) {
                UnionResult::United(united) => united_so_far = united,
                UnionResult::Separate => return Some(united_so_far),
            }

            self.iter.next();
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for AccumulativeUnion

impl<'a, I, T> FusedIterator for AccumulativeUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
{
}

/// Accumulative union iterator using the given closure
#[derive(Debug, Clone, Hash)]
pub struct AccumulativeUnionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<I, F> AccumulativeUnionWith<I, F>
where
    I: Iterator,
{
    pub fn new(iter: I, f: F) -> AccumulativeUnionWith<Peekable<I>, F> {
        AccumulativeUnionWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<'a, I, T, F> Iterator for AccumulativeUnionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().cloned() else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(peeked) = self.iter.peek() else {
                self.exhausted = true;
                return Some(united_so_far);
            };

            match (self.f)(&united_so_far, peeked) {
                UnionResult::United(united) => united_so_far = united,
                UnionResult::Separate => return Some(united_so_far),
            }

            self.iter.next();
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for AccumulativeUnionWith

impl<'a, I, T, F> FusedIterator for AccumulativeUnionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
}

/// Dispatcher trait for peer union iterators
pub trait PeerUnitableIteratorDispatcher: IntoIterator + Sized {
    /// Unites peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the union. If the union is successful,
    /// it returns the united interval. If it is unsuccessful, it returns the current element.
    fn peer_union(self) -> PeerUnion<Peekable<Self::IntoIter>> {
        PeerUnion::new(self.into_iter())
    }

    /// Unites peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the union. If the union is successful,
    /// it returns the united interval. If it is unsuccessful, it returns the current element.
    fn peer_union_with<'a, T, F>(self, f: F) -> PeerUnionWith<Peekable<Self::IntoIter>, F>
    where
        Self::IntoIter: Iterator<Item = &'a T>,
        T: 'a + Unitable<Output = T> + Clone,
        F: FnMut(&T, &T) -> UnionResult<T>,
    {
        PeerUnionWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T> PeerUnitableIteratorDispatcher for I
where
    I: IntoIterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
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

impl<'a, I, T> Iterator for PeerUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
{
    type Item = T;

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
            return Some(current.clone());
        };

        match current.unite(peeked) {
            UnionResult::United(united) => Some(united),
            UnionResult::Separate => Some(current.clone()),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerUnion

impl<'a, I, T> FusedIterator for PeerUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
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

impl<'a, I, T, F> Iterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
    type Item = T;

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
            return Some(current.clone());
        };

        match (self.f)(current, peeked) {
            UnionResult::United(united) => Some(united),
            UnionResult::Separate => Some(current.clone()),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerUnionWith

impl<'a, I, T, F> FusedIterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
}

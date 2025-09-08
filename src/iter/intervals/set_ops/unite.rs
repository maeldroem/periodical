//! Interval iterators regarding interval union

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::UnionResult;

/// Accumulative union iterator using the predefined rules
#[derive(Debug, Clone, Hash)]
pub struct AccumulativeUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<'a, I, T, A> AccumulativeUnion<I>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
    for<'x> &'x T: Into<&'x A>,
    A: Unitable<Output = A>,
{
    pub fn new(iter: I) -> AccumulativeUnion<Peekable<I>> {
        AccumulativeUnion {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<'a, I, T, A> Iterator for AccumulativeUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
    for<'x> &'x T: Into<&'x A>,
    A: Unitable<Output = A>,
{
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().cloned().map(Into::<A>::into) else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(&peeked) = self.iter.peek() else {
                self.exhausted = true;
                return Some(united_so_far);
            };

            match united_so_far.unite(peeked.into()) {
                UnionResult::United(united) => united_so_far = united,
                UnionResult::Separate => return Some(united_so_far),
            }

            self.iter.next();
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1)
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for AccumulativeUnion

impl<'a, I, T, A> FusedIterator for AccumulativeUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
    for<'x> &'x T: Into<&'x A>,
    A: Unitable<Output = A>,
{
}

/// Dispatcher trait for [`AccumulativeUnion`]
pub trait AccumulativeUnionIteratorDispatcher<'a, T, A>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
    for<'x> &'x T: Into<&'x A>,
    A: Unitable<Output = A>,
{
    /// Accumulatively unites intervals of the iterator using the default overlap rules
    #[must_use]
    fn acc_union(self) -> AccumulativeUnion<Peekable<Self::IntoIter>> {
        AccumulativeUnion::new(self.into_iter())
    }
}

impl<'a, T, A, I> AccumulativeUnionIteratorDispatcher<'a, T, A> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
    for<'x> &'x T: Into<&'x A>,
    A: Unitable<Output = A>,
{
}

/// Accumulative union iterator using the given closure
#[derive(Debug, Clone, Hash)]
pub struct AccumulativeUnionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<'a, I, T, F> AccumulativeUnionWith<I, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
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
    T: 'a + Clone,
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
            let Some(&peeked) = self.iter.peek() else {
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1)
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

/// Dispatcher trait for [`AccumulativeUnionWith`]
pub trait AccumulativeUnionWithIteratorDispatcher<'a, T, F>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
    /// Accumulatively unites intervals of the iterator using the given closure
    fn acc_union_with(self, f: F) -> AccumulativeUnionWith<Peekable<Self::IntoIter>, F> {
        AccumulativeUnionWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T, F> AccumulativeUnionWithIteratorDispatcher<'a, T, F> for I
where
    I: IntoIterator<Item = &'a T> + Sized,
    T: 'a + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
}

/// Peer union iterator for intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<'a, I, T, A> PeerUnion<I>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
{
    pub fn new(iter: I) -> PeerUnion<Peekable<I>> {
        PeerUnion {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<'a, I, T, A> Iterator for PeerUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
{
    type Item = A;

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
            return Some(current.clone().into());
        };

        match current.unite(peeked) {
            UnionResult::United(united) => Some(united),
            UnionResult::Separate => Some(current.clone().into()),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerUnion

impl<'a, I, T, A> FusedIterator for PeerUnion<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
{
}

/// Dispatcher trait for [`PeerUnion`]
pub trait PeerUnionIteratorDispatcher<'a, T, A>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
{
    /// Unites peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the union. If the union is successful,
    /// it returns the united interval. If it is unsuccessful, it returns the current element.
    fn peer_union(self) -> PeerUnion<Peekable<Self::IntoIter>> {
        PeerUnion::new(self.into_iter())
    }
}

impl<'a, I, T, A> PeerUnionIteratorDispatcher<'a, T, A> for I
where
    I: IntoIterator<Item = &'a T> + Sized,
    T: 'a + Unitable<Output = A> + Into<A> + Clone,
{
}

/// Peer union iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerUnionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<'a, I, T, A, F> PeerUnionWith<I, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<A> + Clone,
    F: FnMut(&T, &T) -> UnionResult<A>,
{
    pub fn new(iter: I, f: F) -> PeerUnionWith<Peekable<I>, F> {
        PeerUnionWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<'a, I, T, A, F> Iterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<A> + Clone,
    F: FnMut(&T, &T) -> UnionResult<A>,
{
    type Item = A;

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
            return Some(current.clone().into());
        };

        match (self.f)(current, peeked) {
            UnionResult::United(united) => Some(united),
            UnionResult::Separate => Some(current.clone().into()),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerUnionWith

impl<'a, I, T, A, F> FusedIterator for PeerUnionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<A> + Clone,
    F: FnMut(&T, &T) -> UnionResult<A>,
{
}

/// Dispatcher trait for peer union iterators
pub trait PeerUnionWithIteratorDispatcher<'a, T, A, F>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<A> + Clone,
    F: FnMut(&T, &T) -> UnionResult<A>,
{
    /// Unites peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the union. If the union is successful,
    /// it returns the united interval. If it is unsuccessful, it returns the current element.
    fn peer_union_with(self, f: F) -> PeerUnionWith<Peekable<Self::IntoIter>, F> {
        PeerUnionWith::new(self.into_iter(), f)
    }
}

impl<'a, T, A, F, I> PeerUnionWithIteratorDispatcher<'a, T, A, F> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<A> + Clone,
    F: FnMut(&T, &T) -> UnionResult<A>,
{
}

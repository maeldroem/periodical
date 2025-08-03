//! Interval iterators regarding interval union

use std::borrow::Borrow;
use std::iter::{FusedIterator, Peekable};

use crate::intervals::meta::Interval;
use crate::intervals::prelude::*;
use crate::ops::UnionResult;

/// Dispatcher trait for accumulative union iterators
pub trait AccumulativelyUnitableIteratorDispatcher: Iterator + Sized {
    /// Accumulatively unites intervals of the iterator using the default overlap rules
    fn acc_union(self) -> AccumulativeUnion<Peekable<Self>> {
        AccumulativeUnion::new(self)
    }

    /// Accumulatively unites intervals of the iterator using the given closure
    fn acc_union_with<F>(self, f: F) -> AccumulativeUnionWith<Peekable<Self>, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> UnionResult<Self::Item>,
    {
        AccumulativeUnionWith::new(self, f)
    }
}

impl<'a, I, T> AccumulativelyUnitableIteratorDispatcher for I
where
    I: Iterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().map(Borrow::<T>::borrow).cloned() else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(peeked) = self.iter.peek().map(Borrow::<T>::borrow) else {
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(mut united_so_far) = self.iter.next().map(Borrow::<T>::borrow).cloned() else {
            self.exhausted = true;
            return None;
        };

        loop {
            let Some(peeked) = self.iter.peek().map(Borrow::<T>::borrow) else {
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
}

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

impl<'a, I, T> PeerUnitableIteratorDispatcher for I
where
    I: Iterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next().map(Borrow::<T>::borrow) else {
            self.exhausted = true;
            return None;
        };

        let Some(peeked) = self.iter.peek().map(Borrow::<T>::borrow) else {
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next().map(Borrow::<T>::borrow) else {
            self.exhausted = true;
            return None;
        };

        let Some(peeked) = self.iter.peek().map(Borrow::<T>::borrow) else {
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
    T: 'a + Borrow<T> + Unitable<Output = T> + Clone,
    F: FnMut(&T, &T) -> UnionResult<T>,
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

/// Union iterator for intervals using the predefined rules
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

impl<'a, 'o, I, T, J, O> Iterator for Union<I, J>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o + Borrow<O>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next().map(Borrow::<T>::borrow).cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .map(Borrow::<O>::borrow)
                .fold(current, |united_so_far, other| match united_so_far.unite(other) {
                    UnionResult::United(united) => united,
                    UnionResult::Separate => united_so_far,
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O> DoubleEndedIterator for Union<I, J>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o + Borrow<O>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back().map(Borrow::<T>::borrow).cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .map(Borrow::<O>::borrow)
                .fold(current, |united_so_far, other| match united_so_far.unite(other) {
                    UnionResult::United(united) => united,
                    UnionResult::Separate => united_so_far,
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O> FusedIterator for Union<I, J>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o + Borrow<O>,
{
}

/// Union iterator for intervals using the given closure
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

impl<'a, 'o, I, T, J, O, F> Iterator for UnionWith<I, J, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o + Borrow<O>,
    F: FnMut(&T, &O) -> UnionResult<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next().map(Borrow::<T>::borrow).cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .map(Borrow::<O>::borrow)
                .fold(current, |united_so_far, other| match (self.f)(&united_so_far, other) {
                    UnionResult::United(united) => united,
                    UnionResult::Separate => united_so_far,
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O, F> DoubleEndedIterator for UnionWith<I, J, F>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o + Borrow<O>,
    F: FnMut(&T, &O) -> UnionResult<T>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back().map(Borrow::<T>::borrow).cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .map(Borrow::<O>::borrow)
                .fold(current, |united_so_far, other| match (self.f)(&united_so_far, other) {
                    UnionResult::United(united) => united,
                    UnionResult::Separate => united_so_far,
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O, F> FusedIterator for UnionWith<I, J, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Borrow<T> + Unitable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o + Borrow<O>,
    F: FnMut(&T, &O) -> UnionResult<T>,
{
}

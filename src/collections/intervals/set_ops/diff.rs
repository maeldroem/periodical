//! Interval iterators regarding interval difference (as in set difference)

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::DifferenceResult;

/// Dispatcher trait for peer difference iterators
pub trait PeerDifferenceIteratorDispatcher: IntoIterator + Sized {
    /// Differentiates peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the difference. If the difference is successful,
    /// it returns the differentiated interval. If it is unsuccessful, it returns the current element.
    fn peer_difference(self) -> PeerDifference<Peekable<Self::IntoIter>> {
        PeerDifference::new(self.into_iter())
    }

    /// Differentiates peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the difference. If the difference is successful,
    /// it returns the differentiated interval. If it is unsuccessful, it returns the current element.
    fn peer_difference_with<'a, T, U, F>(self, f: F) -> PeerDifferenceWith<Peekable<Self::IntoIter>, F>
    where
        Self::IntoIter: Iterator<Item = &'a T>,
        T: 'a + Clone,
        F: FnMut(&T, &T) -> DifferenceResult<U>,
    {
        PeerDifferenceWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T, U> PeerDifferenceIteratorDispatcher for I
where
    I: IntoIterator<Item = &'a T>,
    T: 'a + Differentiable<Output = U> + Clone,
{
}

/// Peer difference iterator for intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> PeerDifference<I>
where
    I: Iterator,
{
    pub fn new(iter: I) -> PeerDifference<Peekable<I>> {
        PeerDifference {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<'a, I, T, U> Iterator for PeerDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Differentiable<Output = U> + Into<U> + Clone,
{
    type Item = (U, Option<U>);

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
            return Some((current.clone().into(), None));
        };

        match current.differentiate(peeked) {
            DifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            DifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            DifferenceResult::Separate => Some((current.clone().into(), None)),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerDifference

impl<'a, I, T, U> FusedIterator for PeerDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Differentiable<Output = U> + Into<U> + Clone,
{
}

/// Peer difference iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerDifferenceWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<I, F> PeerDifferenceWith<I, F>
where
    I: Iterator,
{
    pub fn new(iter: I, f: F) -> PeerDifferenceWith<Peekable<I>, F> {
        PeerDifferenceWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<'a, I, T, U, F> Iterator for PeerDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> DifferenceResult<U>,
{
    type Item = (U, Option<U>);

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
            return Some((current.clone().into(), None));
        };

        match (self.f)(current, peeked) {
            DifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            DifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            DifferenceResult::Separate => Some((current.clone().into(), None)),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerDifferenceWith

impl<'a, I, T, U, F> FusedIterator for PeerDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> DifferenceResult<U>,
{
}

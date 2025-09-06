//! Interval iterators regarding interval symmetrical difference (a.k.a. XOR)

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::SymmetricDifferenceResult;

/// Dispatcher trait for peer symmetrical difference iterators
pub trait PeerSymmetricDifferenceIteratorDispatcher: IntoIterator + Sized {
    /// Symmetrically differentiates peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the symmetric difference.
    /// If the symmetric difference is successful, it returns all the parts of the differentiated intervals.
    /// If it is unsuccessful, it returns the pair of inspected elements.
    fn peer_symmetric_difference(self) -> PeerSymmetricDifference<Peekable<Self::IntoIter>> {
        PeerSymmetricDifference::new(self.into_iter())
    }

    /// Symmetrically differentiates peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the symmetric difference.
    /// If the symmetric difference is successful, it returns all the parts of the differentiated intervals.
    /// If it is unsuccessful, it returns the pair of inspected elements.
    fn peer_symmetric_difference_with<'a, T, U, F>(
        self,
        f: F,
    ) -> PeerSymmetricDifferenceWith<Peekable<Self::IntoIter>, F>
    where
        Self::IntoIter: Iterator<Item = &'a T>,
        T: 'a + Into<U> + Clone,
        F: FnMut(&T, &T) -> SymmetricDifferenceResult<U>,
    {
        PeerSymmetricDifferenceWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T, U> PeerSymmetricDifferenceIteratorDispatcher for I
where
    I: IntoIterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = U> + Clone,
{
}

/// Peer symmetric difference iterator for intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerSymmetricDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> PeerSymmetricDifference<I>
where
    I: Iterator,
{
    pub fn new(iter: I) -> PeerSymmetricDifference<Peekable<I>> {
        PeerSymmetricDifference {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<'a, I, T, U> Iterator for PeerSymmetricDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = U> + Into<U> + Clone,
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

        match current.symmetrically_differentiate(peeked) {
            SymmetricDifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            SymmetricDifferenceResult::Separate => Some((current.clone().into(), Some((*peeked).clone().into()))),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerSymmetricDifference

impl<'a, I, T, U> FusedIterator for PeerSymmetricDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = U> + Into<U> + Clone,
{
}

/// Peer symmetric difference iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerSymmetricDifferenceWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<I, F> PeerSymmetricDifferenceWith<I, F>
where
    I: Iterator,
{
    pub fn new(iter: I, f: F) -> PeerSymmetricDifferenceWith<Peekable<I>, F> {
        PeerSymmetricDifferenceWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<'a, I, T, U, F> Iterator for PeerSymmetricDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<U>,
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
            SymmetricDifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            SymmetricDifferenceResult::Separate => Some((current.clone().into(), Some((*peeked).clone().into()))),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerSymmetricDifferenceWith

impl<'a, I, T, U, F> FusedIterator for PeerSymmetricDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<U>,
{
}

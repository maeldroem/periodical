//! Interval iterators regarding interval symmetrical difference (a.k.a. XOR)

use std::iter::{FusedIterator, Peekable};

use crate::intervals::meta::Interval;
use crate::intervals::prelude::*;
use crate::ops::SymmetricDifferenceResult;

/// Dispatcher trait for peer symmetrical difference iterators
pub trait PeerSymmetricDifferenceIteratorDispatcher: Iterator + Sized {
    /// Symmetrically differentiates peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the symmetric difference.
    /// If the symmetric difference is successful, it returns all the parts of the differentiated intervals.
    /// If it is unsuccessful, it returns the pair of inspected elements.
    fn peer_symmetric_difference(self) -> PeerSymmetricDifference<Peekable<Self>> {
        PeerSymmetricDifference::new(self)
    }

    /// Symmetrically differentiates peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the symmetric difference.
    /// If the symmetric difference is successful, it returns all the parts of the differentiated intervals.
    /// If it is unsuccessful, it returns the pair of inspected elements.
    fn peer_symmetric_difference_with<F>(self, f: F) -> PeerSymmetricDifferenceWith<Peekable<Self>, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> SymmetricDifferenceResult<Self::Item>,
    {
        PeerSymmetricDifferenceWith::new(self, f)
    }
}

impl<'a, I, T> PeerSymmetricDifferenceIteratorDispatcher for I
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = T> + Clone,
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

impl<'a, I, T> Iterator for PeerSymmetricDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = T> + Clone,
{
    type Item = (T, Option<T>);

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
            return Some((current.clone(), None));
        };

        match current.symmetrically_differentiate(peeked) {
            SymmetricDifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            SymmetricDifferenceResult::Separate => Some((current.clone(), Some((*peeked).clone()))),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerSymmetricDifference

impl<'a, I, T> FusedIterator for PeerSymmetricDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = T> + Clone,
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

impl<'a, I, T, F> Iterator for PeerSymmetricDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = T> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<T>,
{
    type Item = (T, Option<T>);

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
            return Some((current.clone(), None));
        };

        match (self.f)(current, peeked) {
            SymmetricDifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            SymmetricDifferenceResult::Separate => Some((current.clone(), Some((*peeked).clone()))),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerSymmetricDifferenceWith

impl<'a, I, T, F> FusedIterator for PeerSymmetricDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = T> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<T>,
{
}

/// Dispatcher trait for difference iterators
pub trait SymmetricallyDifferentiableIteratorDispatcher: Iterator + Sized {
    /// Symmetrically differentiates each item with every overlapping element of the given other iterator
    /// using the predefined overlap rules
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn symmetric_difference<J>(self, other_iter: J) -> SymmetricDifference<Self, J>
    where
        J: IntoIterator + Clone,
    {
        SymmetricDifference::new(self, other_iter)
    }

    /// Symmetrically differentiates each item with every overlapping element of the given other iterator
    /// using the given closure
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn symmetric_difference_with<J, F>(self, other_iter: J, f: F) -> SymmetricDifferenceWith<Self, J, F>
    where
        J: IntoIterator + Clone,
        F: FnMut(&Self::Item, J::Item) -> SymmetricDifferenceResult<Self::Item>,
    {
        SymmetricDifferenceWith::new(self, other_iter, f)
    }
}

impl<'a, I, T> SymmetricallyDifferentiableIteratorDispatcher for I
where
    I: Iterator<Item = &'a T>,
    T: 'a + Interval + Clone, // SymmetricallyDifferentiable<O, Output = I::Item>,
{
}

/// Symmetric difference iterator for intervals using the predefined rules
#[derive(Debug, Clone, Hash)]
pub struct SymmetricDifference<I, J> {
    iter: I,
    other_iter: J,
    exhausted: bool,
}

impl<I, J> SymmetricDifference<I, J> {
    pub fn new(iter: I, other_iter: J) -> Self {
        SymmetricDifference {
            iter,
            other_iter,
            exhausted: false,
        }
    }
}

impl<'a, 'o, I, T, J, O> Iterator for SymmetricDifference<I, J>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next().cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .fold(vec![current], |differentiated_so_far, other| {
                    differentiated_so_far
                        .iter()
                        .flat_map(|diff| {
                            // It will be flattened anyways, so we want it to take the least possible space
                            let mut res = Vec::with_capacity(2);

                            match diff.symmetrically_differentiate(other) {
                                SymmetricDifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                SymmetricDifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O> DoubleEndedIterator for SymmetricDifference<I, J>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back().cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .fold(vec![current], |differentiated_so_far, other| {
                    differentiated_so_far
                        .iter()
                        .flat_map(|diff| {
                            // It will be flattened anyways, so we want it to take the least possible space
                            let mut res = Vec::with_capacity(2);

                            match diff.symmetrically_differentiate(other) {
                                SymmetricDifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                SymmetricDifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O> FusedIterator for SymmetricDifference<I, J>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
}

/// Symmetric difference iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct SymmetricDifferenceWith<I, J, F> {
    iter: I,
    other_iter: J,
    f: F,
    exhausted: bool,
}

impl<I, J, F> SymmetricDifferenceWith<I, J, F> {
    pub fn new(iter: I, other_iter: J, f: F) -> Self {
        SymmetricDifferenceWith {
            iter,
            other_iter,
            f,
            exhausted: false,
        }
    }
}

impl<'a, 'o, I, T, J, O, F> Iterator for SymmetricDifferenceWith<I, J, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&T, &O) -> SymmetricDifferenceResult<T>,
{
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next().cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .fold(vec![current], |differentiated_so_far, other| {
                    differentiated_so_far
                        .iter()
                        .flat_map(|diff| {
                            // It will be flattened anyways, so we want it to take the least possible space
                            let mut res = Vec::with_capacity(2);

                            match (self.f)(diff, other) {
                                SymmetricDifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                SymmetricDifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O, F> DoubleEndedIterator for SymmetricDifferenceWith<I, J, F>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&T, &O) -> SymmetricDifferenceResult<T>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        let Some(current) = self.iter.next_back().cloned() else {
            self.exhausted = true;
            return None;
        };

        Some(
            self.other_iter
                .clone()
                .into_iter()
                .fold(vec![current], |differentiated_so_far, other| {
                    differentiated_so_far
                        .iter()
                        .flat_map(|diff| {
                            // It will be flattened anyways, so we want it to take the least possible space
                            let mut res = Vec::with_capacity(2);

                            match (self.f)(diff, other) {
                                SymmetricDifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                SymmetricDifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O, F> FusedIterator for SymmetricDifferenceWith<I, J, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&T, &O) -> SymmetricDifferenceResult<T>,
{
}

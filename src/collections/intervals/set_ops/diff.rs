//! Interval iterators regarding interval difference (as in set difference)

use std::iter::{FusedIterator, Peekable};

use crate::intervals::meta::Interval;
use crate::intervals::prelude::*;
use crate::ops::DifferenceResult;

/// Dispatcher trait for peer difference iterators
pub trait PeerDifferenceIteratorDispatcher: Iterator + Sized {
    /// Differentiates peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the difference. If the difference is successful,
    /// it returns the differentiated interval. If it is unsuccessful, it returns the current element.
    fn peer_difference(self) -> PeerDifference<Peekable<Self>> {
        PeerDifference::new(self)
    }

    /// Differentiates peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the difference. If the difference is successful,
    /// it returns the differentiated interval. If it is unsuccessful, it returns the current element.
    fn peer_difference_with<F>(self, f: F) -> PeerDifferenceWith<Peekable<Self>, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> DifferenceResult<Self::Item>,
    {
        PeerDifferenceWith::new(self, f)
    }
}

impl<I> PeerDifferenceIteratorDispatcher for I
where
    I: Iterator,
    I::Item: Differentiable<Output = I::Item>,
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

impl<I> Iterator for PeerDifference<Peekable<I>>
where
    I: Iterator,
    I::Item: Differentiable<Output = I::Item>,
{
    type Item = (I::Item, Option<I::Item>);

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
            return Some((current, None));
        };

        match current.differentiate(peeked) {
            DifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            DifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            DifferenceResult::Separate => Some((current, None)),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerDifference

impl<I> FusedIterator for PeerDifference<Peekable<I>>
where
    I: Iterator,
    I::Item: Differentiable<Output = I::Item>,
{
}

/// Peer union iterator for intervals using the given closure
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

impl<I, F> Iterator for PeerDifferenceWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: Differentiable<Output = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> DifferenceResult<I::Item>,
{
    type Item = (I::Item, Option<I::Item>);

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
            return Some((current, None));
        };

        match (self.f)(&current, peeked) {
            DifferenceResult::Shrunk(shrunk) => Some((shrunk, None)),
            DifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            DifferenceResult::Separate => Some((current, None)),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerDifferenceWith

impl<I, F> FusedIterator for PeerDifferenceWith<Peekable<I>, F>
where
    I: Iterator,
    I::Item: Differentiable<Output = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> DifferenceResult<I::Item>,
{
}

/// Dispatcher trait for difference iterators
pub trait DifferentiableIteratorDispatcher: Iterator + Sized {
    /// Differentiates each item with every overlapping element of the given other iterator
    /// using the predefined overlap rules
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn difference<J>(self, other_iter: J) -> Difference<Self, J>
    where
        J: IntoIterator + Clone,
    {
        Difference::new(self, other_iter)
    }

    /// Differentiates each item with every overlapping element of the given other iterator using the given closure
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn difference_with<J, F>(self, other_iter: J, f: F) -> DifferenceWith<Self, J, F>
    where
        J: IntoIterator + Clone,
        F: FnMut(&Self::Item, J::Item) -> DifferenceResult<Self::Item>,
    {
        DifferenceWith::new(self, other_iter, f)
    }
}

impl<I> DifferentiableIteratorDispatcher for I
where
    I: Iterator,
    I::Item: Interval, // Differentiable<O, Output = I::Item>,
{
}

#[derive(Debug, Clone, Hash)]
pub struct Difference<I, J> {
    iter: I,
    other_iter: J,
    exhausted: bool,
}

impl<I, J> Difference<I, J> {
    pub fn new(iter: I, other_iter: J) -> Self {
        Difference {
            iter,
            other_iter,
            exhausted: false,
        }
    }
}

impl<'o, I, J, O> Iterator for Difference<I, J>
where
    I: Iterator,
    I::Item: Differentiable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
    type Item = Vec<I::Item>;

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
                .fold(vec![current], |differentiated_so_far, other| {
                    differentiated_so_far
                        .iter()
                        .flat_map(|diff| {
                            // It will be flattened anyways, so we want it to take the least possible space
                            let mut res = Vec::with_capacity(2);

                            match diff.differentiate(other) {
                                DifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                DifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                DifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'o, I, J, O> DoubleEndedIterator for Difference<I, J>
where
    I: DoubleEndedIterator,
    I::Item: Differentiable<O, Output = I::Item>,
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

                            match diff.differentiate(other) {
                                DifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                DifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                DifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'o, I, J, O> FusedIterator for Difference<I, J>
where
    I: Iterator,
    I::Item: Differentiable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
}

#[derive(Debug, Clone)]
pub struct DifferenceWith<I, J, F> {
    iter: I,
    other_iter: J,
    f: F,
    exhausted: bool,
}

impl<I, J, F> DifferenceWith<I, J, F> {
    pub fn new(iter: I, other_iter: J, f: F) -> Self {
        DifferenceWith {
            iter,
            other_iter,
            f,
            exhausted: false,
        }
    }
}

impl<'o, I, J, O, F> Iterator for DifferenceWith<I, J, F>
where
    I: Iterator,
    I::Item: Differentiable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&I::Item, &'o O) -> DifferenceResult<I::Item>,
{
    type Item = Vec<I::Item>;

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
                .fold(vec![current], |differentiated_so_far: Vec<I::Item>, other| {
                    differentiated_so_far
                        .iter()
                        .flat_map(|diff| {
                            // It will be flattened anyways, so we want it to take the least possible space
                            let mut res = Vec::with_capacity(2);

                            match (self.f)(diff, other) {
                                DifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                DifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                DifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'o, I, J, O, F> DoubleEndedIterator for DifferenceWith<I, J, F>
where
    I: DoubleEndedIterator,
    I::Item: Differentiable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&I::Item, &'o O) -> DifferenceResult<I::Item>,
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
                .fold(vec![current], |differentiated_so_far: Vec<I::Item>, other| {
                    differentiated_so_far
                        .iter()
                        .flat_map(|diff| {
                            // It will be flattened anyways, so we want it to take the least possible space
                            let mut res = Vec::with_capacity(2);

                            match (self.f)(diff, other) {
                                DifferenceResult::Shrunk(shrunk) => res.push(shrunk),
                                DifferenceResult::Split(split_first_part, split_second_part) => {
                                    res.push(split_first_part);
                                    res.push(split_second_part);
                                },
                                DifferenceResult::Separate => {},
                            }

                            res
                        })
                        .collect()
                }),
        )
    }
}

impl<'o, I, J, O, F> FusedIterator for DifferenceWith<I, J, F>
where
    I: DoubleEndedIterator,
    I::Item: Differentiable<O, Output = I::Item>,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&I::Item, &O) -> DifferenceResult<I::Item>,
{
}

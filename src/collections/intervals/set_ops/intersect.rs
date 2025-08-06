//! Interval iterators regarding interval intersection

use std::iter::{FusedIterator, Peekable};

use crate::intervals::meta::Interval;
use crate::intervals::prelude::*;
use crate::ops::IntersectionResult;

/// Dispatcher trait for peer intersection iterators
pub trait PeerIntersectableIteratorDispatcher: Iterator + Sized {
    /// Intersects peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the intersection. If the intersection is successful,
    /// it returns the intersected interval. If it is unsuccessful, it returns the current element.
    fn peer_intersection(self) -> PeerIntersection<Peekable<Self>> {
        PeerIntersection::new(self)
    }

    /// Intersects peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the intersection. If the intersection is successful,
    /// it returns the intersected interval. If it is unsuccessful, it returns the current element.
    fn peer_intersection_with<F>(self, f: F) -> PeerIntersectionWith<Peekable<Self>, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> IntersectionResult<Self::Item>,
    {
        PeerIntersectionWith::new(self, f)
    }
}

impl<'a, I, T> PeerIntersectableIteratorDispatcher for I
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = T> + Clone,
{
}

/// Peer intersection iterator for intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerIntersection<I> {
    iter: I,
    exhausted: bool,
}

impl<I> PeerIntersection<I>
where
    I: Iterator,
{
    pub fn new(iter: I) -> PeerIntersection<Peekable<I>> {
        PeerIntersection {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<'a, I, T> Iterator for PeerIntersection<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = T> + Clone,
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

        match current.intersect(peeked) {
            IntersectionResult::Intersected(intersected) => Some(intersected),
            IntersectionResult::Separate => Some(current.clone()),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerIntersection

impl<'a, I, T> FusedIterator for PeerIntersection<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = T> + Clone,
{
}

/// Peer intersection iterator for intervals using the given closure
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
    pub fn new(iter: I, f: F) -> PeerIntersectionWith<Peekable<I>, F> {
        PeerIntersectionWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<'a, I, T, F> Iterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = T> + Clone,
    F: FnMut(&T, &T) -> IntersectionResult<T>,
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
            IntersectionResult::Intersected(intersected) => Some(intersected),
            IntersectionResult::Separate => Some(current.clone()),
        }
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerIntersectionWith

impl<'a, I, T, F> FusedIterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = T> + Clone,
    F: FnMut(&T, &T) -> IntersectionResult<T>,
{
}

/// Dispatcher trait for intersection iterators
pub trait IntersectableIteratorDispatcher: Iterator + Sized {
    /// Intersects each item with every overlapping element of the given other iterator
    /// using the predefined overlap rules
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn intersection<J>(self, other_iter: J) -> Intersection<Self, J>
    where
        J: IntoIterator + Clone,
    {
        Intersection::new(self, other_iter)
    }

    /// Intersects each item with every overlapping element of the given other iterator using the given closure
    ///
    /// ⚠️⏱️ This is suboptimal. It checks every element of the given other iterator against each element of the current
    /// iterator. It is only useful in _some_ cases. Use [`TODO TODO TODO`] instead.
    fn intersection_with<J, F>(self, other_iter: J, f: F) -> IntersectionWith<Self, J, F>
    where
        J: IntoIterator + Clone,
        F: FnMut(&Self::Item, J::Item) -> IntersectionResult<Self::Item>,
    {
        IntersectionWith::new(self, other_iter, f)
    }
}

impl<'a, I, T> IntersectableIteratorDispatcher for I
where
    I: Iterator<Item = &'a T>,
    T: 'a + Interval + Clone, // Intersectable<O, Output = I::Item>,
{
}

/// Intersection iterator for intervals using the predefined rules
#[derive(Debug, Clone, Hash)]
pub struct Intersection<I, J> {
    iter: I,
    other_iter: J,
    exhausted: bool,
}

impl<I, J> Intersection<I, J> {
    pub fn new(iter: I, other_iter: J) -> Self {
        Intersection {
            iter,
            other_iter,
            exhausted: false,
        }
    }
}

impl<'a, 'o, I, T, J, O> Iterator for Intersection<I, J>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
    type Item = T;

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
                .fold(current, |intersected_so_far, other| {
                    match intersected_so_far.intersect(other) {
                        IntersectionResult::Intersected(intersected) => intersected,
                        IntersectionResult::Separate => intersected_so_far,
                    }
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O> DoubleEndedIterator for Intersection<I, J>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: 'a + Intersectable<O, Output = T> + Clone,
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
                .fold(current, |intersected_so_far, other| {
                    match intersected_so_far.intersect(other) {
                        IntersectionResult::Intersected(intersected) => intersected,
                        IntersectionResult::Separate => intersected_so_far,
                    }
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O> FusedIterator for Intersection<I, J>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
{
}

/// Intersection iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct IntersectionWith<I, J, F> {
    iter: I,
    other_iter: J,
    f: F,
    exhausted: bool,
}

impl<I, J, F> IntersectionWith<I, J, F> {
    pub fn new(iter: I, other_iter: J, f: F) -> Self {
        IntersectionWith {
            iter,
            other_iter,
            f,
            exhausted: false,
        }
    }
}

impl<'a, 'o, I, T, J, O, F> Iterator for IntersectionWith<I, J, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&T, &O) -> IntersectionResult<T>,
{
    type Item = T;

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
                .fold(current, |intersected_so_far, other| {
                    match (self.f)(&intersected_so_far, other) {
                        IntersectionResult::Intersected(intersected) => intersected,
                        IntersectionResult::Separate => intersected_so_far,
                    }
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O, F> DoubleEndedIterator for IntersectionWith<I, J, F>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: 'a + Intersectable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&T, &O) -> IntersectionResult<T>,
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
                .fold(current, |intersected_so_far, other| {
                    match (self.f)(&intersected_so_far, other) {
                        IntersectionResult::Intersected(intersected) => intersected,
                        IntersectionResult::Separate => intersected_so_far,
                    }
                }),
        )
    }
}

impl<'a, 'o, I, T, J, O, F> FusedIterator for IntersectionWith<I, J, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<O, Output = T> + Clone,
    J: IntoIterator<Item = &'o O> + Clone,
    O: 'o,
    F: FnMut(&T, &O) -> IntersectionResult<T>,
{
}

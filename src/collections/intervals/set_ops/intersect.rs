//! Interval iterators regarding interval intersection

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::IntersectionResult;

/// Dispatcher trait for peer intersection iterators
pub trait PeerIntersectableIteratorDispatcher: IntoIterator + Sized {
    /// Intersects peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the intersection. If the intersection is successful,
    /// it returns the intersected interval. If it is unsuccessful, it returns the current element.
    fn peer_intersection(self) -> PeerIntersection<Peekable<Self::IntoIter>> {
        PeerIntersection::new(self.into_iter())
    }

    /// Intersects peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the intersection. If the intersection is successful,
    /// it returns the intersected interval. If it is unsuccessful, it returns the current element.
    fn peer_intersection_with<'a, T, F>(self, f: F) -> PeerIntersectionWith<Peekable<Self::IntoIter>, F>
    where
        Self::IntoIter: Iterator<Item = &'a T>,
        T: 'a + Intersectable<Output = T> + Clone,
        F: FnMut(&T, &T) -> IntersectionResult<T>,
    {
        PeerIntersectionWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T> PeerIntersectableIteratorDispatcher for I
where
    I: IntoIterator<Item = &'a T>,
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

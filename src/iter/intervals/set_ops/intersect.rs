//! Interval iterators regarding interval intersection

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::IntersectionResult;

/// Peer intersection iterator for intervals using predefined rules
#[derive(Debug, Clone, Hash)]
pub struct PeerIntersection<I> {
    iter: I,
    exhausted: bool,
}

impl<'a, I, T, U> PeerIntersection<I>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = U> + Into<U> + Clone,
{
    pub fn new(iter: I) -> PeerIntersection<Peekable<I>> {
        PeerIntersection {
            iter: iter.peekable(),
            exhausted: false,
        }
    }
}

impl<'a, I, T, U> Iterator for PeerIntersection<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = U> + Into<U> + Clone,
{
    type Item = U;

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

        match current.intersect(peeked) {
            IntersectionResult::Intersected(intersected) => Some(intersected),
            IntersectionResult::Separate => Some(current.clone().into()),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerIntersection

impl<'a, I, T, U> FusedIterator for PeerIntersection<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = U> + Into<U> + Clone,
{
}

/// Iterator dispatcher for [`PeerIntersection`]
pub trait PeerIntersectionIteratorDispatcher<'a, T, U>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = U> + Into<U> + Clone,
{
    /// Intersects peer intervals of the iterator using the default overlap rules
    ///
    /// Processes elements pair by pair and returns the result of the intersection. If the intersection is successful,
    /// it returns the intersected interval. If it is unsuccessful, it returns the current element.
    fn peer_intersection(self) -> PeerIntersection<Peekable<Self::IntoIter>> {
        PeerIntersection::new(self.into_iter())
    }
}

impl<'a, I, T, U> PeerIntersectionIteratorDispatcher<'a, T, U> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Intersectable<Output = U> + Into<U> + Clone,
{
}

/// Peer intersection iterator for intervals using the given closure
#[derive(Debug, Clone)]
pub struct PeerIntersectionWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<'a, I, T, U, F> PeerIntersectionWith<I, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> IntersectionResult<U>,
{
    pub fn new(iter: I, f: F) -> PeerIntersectionWith<Peekable<I>, F> {
        PeerIntersectionWith {
            iter: iter.peekable(),
            f,
            exhausted: false,
        }
    }
}

impl<'a, I, T, U, F> Iterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> IntersectionResult<U>,
{
    type Item = U;

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
            IntersectionResult::Intersected(intersected) => Some(intersected),
            IntersectionResult::Separate => Some(current.clone().into()),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

// TODO: If a reverse Peekable becomes standard or when we'll import a crate that does that,
// implement DoubleEndedIterator for PeerIntersectionWith

impl<'a, I, T, U, F> FusedIterator for PeerIntersectionWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> IntersectionResult<U>,
{
}

/// Iterator dispatcher trait for [`PeerIntersectionWith`]
pub trait PeerIntersectionWithIteratorDispatcher<'a, T, U, F>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> IntersectionResult<U>,
{
    /// Intersects peer intervals of the iterator using the given closure
    ///
    /// Processes elements pair by pair and returns the result of the intersection. If the intersection is successful,
    /// it returns the intersected interval. If it is unsuccessful, it returns the current element.
    fn peer_intersection_with(self, f: F) -> PeerIntersectionWith<Peekable<Self::IntoIter>, F> {
        PeerIntersectionWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T, U, F> PeerIntersectionWithIteratorDispatcher<'a, T, U, F> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> IntersectionResult<U>,
{
}

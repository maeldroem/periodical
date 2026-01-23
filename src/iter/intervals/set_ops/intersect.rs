//! Interval iterators to operate intersections on intervals
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::set_ops::intersect::PeerIntersectionIteratorDispatcher;
//! let intervals = [
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::InfiniteFuture,
//!     ),
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::InfiniteFuture,
//!     ),
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     ),
//! ];
//!
//! assert_eq!(
//!     intervals.peer_intersection().collect::<Vec<_>>(),
//!     vec![
//!         AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::InfiniteFuture,
//!         ),
//!         AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         ),
//!     ],
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::IntersectionResult;

/// Peer intersection iterator for intervals using predefined rules
///
/// Operates an [intersection] on peers, that is to say, we operate the intersection on every pair of intervals.
///
/// Uses [`Intersectable`] under the hood.
///
/// [intersection]: https://en.wikipedia.org/w/index.php?title=Intersection_(set_theory)&oldid=1191979994
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
    /// Creates a new [`PeerIntersection`]
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
            return None;
        };

        match current.intersect(peeked) {
            IntersectionResult::Intersected(intersected) => Some(intersected),
            IntersectionResult::Separate => Some(current.clone().into()),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();
        (
            inner_size_hint.0.saturating_sub(1),
            inner_size_hint.1.map(|x| x.saturating_sub(1)),
        )
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
    /// Operates an [intersection] on peers, that is to say, we operate the intersection on every pair of intervals.
    ///
    /// Uses [`Intersectable`] under the hood.
    ///
    /// [intersection]: https://en.wikipedia.org/w/index.php?title=Intersection_(set_theory)&oldid=1191979994
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
///
/// Operates an [intersection] on peers, that is to say, we operate the intersection on every pair of intervals.
///
/// Uses [`Intersectable`] under the hood.
///
/// [intersection]: https://en.wikipedia.org/w/index.php?title=Intersection_(set_theory)&oldid=1191979994
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
    /// Creates a new [`PeerIntersectionWith`]
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
            return None;
        };

        match (self.f)(current, peeked) {
            IntersectionResult::Intersected(intersected) => Some(intersected),
            IntersectionResult::Separate => Some(current.clone().into()),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();
        (
            inner_size_hint.0.saturating_sub(1),
            inner_size_hint.1.map(|x| x.saturating_sub(1)),
        )
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
    /// Operates an [intersection] on peers, that is to say, we operate the intersection on every pair of intervals.
    ///
    /// Uses [`Intersectable`] under the hood.
    ///
    /// [intersection]: https://en.wikipedia.org/w/index.php?title=Intersection_(set_theory)&oldid=1191979994
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

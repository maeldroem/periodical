//! Interval iterators to operate symmetric differences on intervals
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::set_ops::sym_diff::PeerSymmetricDifferenceIteratorDispatcher;
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
//!     intervals.peer_symmetric_difference().collect::<Vec<_>>(),
//!     vec![
//!         (
//!             EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!                 AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!                 )),
//!                 AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!                     BoundInclusivity::Exclusive,
//!                 )),
//!             )),
//!             None,
//!         ),
//!         (
//!             EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!                 AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                     "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
//!                 )),
//!                 AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!                     BoundInclusivity::Exclusive,
//!                 )),
//!             )),
//!             Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!                 AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!                     BoundInclusivity::Exclusive,
//!                 )),
//!                 AbsoluteEndBound::InfiniteFuture,
//!             ))),
//!         ),
//!     ],
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::iter::{FusedIterator, Peekable};

use crate::intervals::prelude::*;
use crate::ops::SymmetricDifferenceResult;

/// Peer symmetric difference iterator for intervals using predefined rules
///
/// Operates a [symmetric difference] on peers, that is to say, we operate the intersection on every pair of intervals.
///
/// Uses [`SymmetricallyDifferentiable`] under the hood.
///
/// [symmetric difference]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
#[derive(Debug, Clone, Hash)]
pub struct PeerSymmetricDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<'a, I, T, U> PeerSymmetricDifference<I>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = U> + Into<U> + Clone,
{
    /// Creates a new [`PeerSymmetricDifference`]
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
            return None;
        };

        match current.symmetrically_differentiate(peeked) {
            SymmetricDifferenceResult::Single(shrunk) => Some((shrunk, None)),
            SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            SymmetricDifferenceResult::Separate => Some((current.clone().into(), Some((*peeked).clone().into()))),
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
// implement DoubleEndedIterator for PeerSymmetricDifference

impl<'a, I, T, U> FusedIterator for PeerSymmetricDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = U> + Into<U> + Clone,
{
}

/// Iterator dispatcher trait for [`PeerSymmetricDifference`]
pub trait PeerSymmetricDifferenceIteratorDispatcher<'a, T, U>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = U> + Into<U> + Clone,
{
    /// Symmetrically differentiates peer intervals of the iterator using the default overlap rules
    ///
    /// Operates a [symmetric difference] on peers, that is to say, we operate the intersection on every pair
    /// of intervals.
    ///
    /// Uses [`SymmetricallyDifferentiable`] under the hood.
    ///
    /// [symmetric difference]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
    fn peer_symmetric_difference(self) -> PeerSymmetricDifference<Peekable<Self::IntoIter>> {
        PeerSymmetricDifference::new(self.into_iter())
    }
}

impl<'a, I, T, U> PeerSymmetricDifferenceIteratorDispatcher<'a, T, U> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + SymmetricallyDifferentiable<Output = U> + Into<U> + Clone,
{
}

/// Peer symmetric difference iterator for intervals using the given closure
///
/// Operates a [symmetric difference] on peers, that is to say, we operate the intersection on every pair of intervals.
///
/// Uses [`SymmetricallyDifferentiable`] under the hood.
///
/// [symmetric difference]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
#[derive(Debug, Clone)]
pub struct PeerSymmetricDifferenceWith<I, F> {
    iter: I,
    f: F,
    exhausted: bool,
}

impl<'a, I, T, U, F> PeerSymmetricDifferenceWith<I, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<U>,
{
    /// Creates a new [`PeerSymmetricDifferenceWith`]
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
            return None;
        };

        match (self.f)(current, peeked) {
            SymmetricDifferenceResult::Single(shrunk) => Some((shrunk, None)),
            SymmetricDifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            SymmetricDifferenceResult::Separate => Some((current.clone().into(), Some((*peeked).clone().into()))),
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
// implement DoubleEndedIterator for PeerSymmetricDifferenceWith

impl<'a, I, T, U, F> FusedIterator for PeerSymmetricDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<U>,
{
}

/// Iterator dispatcher trait for [`PeerSymmetricDifferenceWith`]
pub trait PeerSymmetricDifferenceWithIteratorDispatcher<'a, T, U, F>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<U>,
{
    /// Symmetrically differentiates peer intervals of the iterator using the given closure
    ///
    /// Operates a [symmetric difference] on peers, that is to say, we operate the intersection on every pair
    /// of intervals.
    ///
    /// Uses [`SymmetricallyDifferentiable`] under the hood.
    ///
    /// [symmetric difference]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
    fn peer_symmetric_difference_with(self, f: F) -> PeerSymmetricDifferenceWith<Peekable<Self::IntoIter>, F> {
        PeerSymmetricDifferenceWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T, U, F> PeerSymmetricDifferenceWithIteratorDispatcher<'a, T, U, F> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> SymmetricDifferenceResult<U>,
{
}

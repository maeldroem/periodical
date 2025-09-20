//! Interval iterators to operate differences on intervals
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::set_ops::diff::PeerDifferenceIteratorDispatcher;
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
//!     intervals.peer_difference().collect::<Vec<_>>(),
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
use crate::ops::DifferenceResult;

/// Peer difference iterator for intervals using predefined rules
///
/// Operates a [difference] on peers, that is to say, we operate the difference on every pair of intervals,
/// using the intervals in the same order of as difference's operands: the first element of the pair is the _removed_,
/// the second element of the pair is the _remover_.
///
/// Uses [`Differentiable`] under the hood.
///
/// [difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
#[derive(Debug, Clone, Hash)]
pub struct PeerDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<'a, I, T, U> PeerDifference<I>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Differentiable<Output = U> + Into<U> + Clone,
{
    /// Creates a new [`PeerDifference`]
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
            return None;
        };

        match current.differentiate(peeked) {
            DifferenceResult::Single(shrunk) => Some((shrunk, None)),
            DifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            DifferenceResult::Separate => Some((current.clone().into(), None)),
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
// implement DoubleEndedIterator for PeerDifference

impl<'a, I, T, U> FusedIterator for PeerDifference<Peekable<I>>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Differentiable<Output = U> + Into<U> + Clone,
{
}

/// Iterator dispatcher trait for [`PeerDifference`]
pub trait PeerDifferenceIteratorDispatcher<'a, T, U>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Differentiable<Output = U> + Into<U> + Clone,
{
    /// Differentiates peer intervals of the iterator using the default overlap rules
    ///
    /// Operates a [difference] on peers, that is to say, we operate the difference on every pair of intervals,
    /// using the intervals in the same order of as difference's operands: the first element of the pair is
    /// the _removed_, the second element of the pair is the _remover_.
    ///
    /// Uses [`Differentiable`] under the hood.
    ///
    /// [difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
    fn peer_difference(self) -> PeerDifference<Peekable<Self::IntoIter>> {
        PeerDifference::new(self.into_iter())
    }
}

impl<'a, I, T, U> PeerDifferenceIteratorDispatcher<'a, T, U> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Differentiable<Output = U> + Into<U> + Clone,
{
}

/// Peer difference iterator for intervals using the given closure
///
/// Operates a [difference] on peers, that is to say, we operate the difference on every pair of intervals,
/// using the intervals in the same order of as difference's operands: the first element of the pair is the _removed_,
/// the second element of the pair is the _remover_.
///
/// Uses [`Differentiable`] under the hood.
///
/// [difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
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
    /// Creates a new [`PeerDifferenceWith`]
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
            return None;
        };

        match (self.f)(current, peeked) {
            DifferenceResult::Single(shrunk) => Some((shrunk, None)),
            DifferenceResult::Split(split_first_part, split_second_part) => {
                Some((split_first_part, Some(split_second_part)))
            },
            DifferenceResult::Separate => Some((current.clone().into(), None)),
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
// implement DoubleEndedIterator for PeerDifferenceWith

impl<'a, I, T, U, F> FusedIterator for PeerDifferenceWith<Peekable<I>, F>
where
    I: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> DifferenceResult<U>,
{
}

/// Iterator dispatcher trait for [`PeerDifferenceWith`]
pub trait PeerDifferenceWithIteratorDispatcher<'a, T, U, F>
where
    Self: IntoIterator + Sized,
    Self::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> DifferenceResult<U>,
{
    /// Differentiates peer intervals of the iterator using the given closure
    ///
    /// Operates a [difference] on peers, that is to say, we operate the difference on every pair of intervals,
    /// using the intervals in the same order of as difference's operands: the first element of the pair is
    /// the _removed_, the second element of the pair is the _remover_.
    ///
    /// Uses [`Differentiable`] under the hood.
    ///
    /// [difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
    fn peer_difference_with(self, f: F) -> PeerDifferenceWith<Peekable<Self::IntoIter>, F> {
        PeerDifferenceWith::new(self.into_iter(), f)
    }
}

impl<'a, I, T, U, F> PeerDifferenceWithIteratorDispatcher<'a, T, U, F> for I
where
    I: IntoIterator + Sized,
    I::IntoIter: Iterator<Item = &'a T>,
    T: 'a + Into<U> + Clone,
    F: FnMut(&T, &T) -> DifferenceResult<U>,
{
}

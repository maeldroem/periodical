//! Complement iterator
//!
//! Iterator that returns the [`ComplementResult`] of every interval from the interval.
//!
//! The iterator uses [`Complementable`] to get the complements of the intervals.
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::ops::ComplementResult;
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::complement::ComplementIteratorDispatcher;
//! let intervals = [
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     ),
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     ),
//! ];
//!
//! assert_eq!(
//!     intervals.complement().collect::<Vec<_>>(),
//!     vec![
//!         ComplementResult::Split(
//!             EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!                 AbsoluteStartBound::InfinitePast,
//!                 AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!                     BoundInclusivity::Exclusive,
//!                 )),
//!             )),
//!             EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!                 AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
//!                     BoundInclusivity::Exclusive,
//!                 )),
//!                 AbsoluteEndBound::InfiniteFuture,
//!             )),
//!         ),
//!         ComplementResult::Split(
//!             EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!                 AbsoluteStartBound::InfinitePast,
//!                 AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!                     BoundInclusivity::Exclusive,
//!                 )),
//!             )),
//!             EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!                 AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!                     BoundInclusivity::Exclusive,
//!                 )),
//!                 AbsoluteEndBound::InfiniteFuture,
//!             )),
//!         ),
//!     ],
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use crate::intervals::prelude::*;
use crate::ops::ComplementResult;

/// Dispatcher trait for the [`ComplementIter`] iterator
pub trait ComplementIteratorDispatcher
where
    Self: IntoIterator + Sized,
    Self::Item: Complementable,
{
    /// Creates a [`ComplementIter`] from the collection
    fn complement(self) -> ComplementIter<Self::IntoIter> {
        ComplementIter::new(self.into_iter())
    }
}

impl<I> ComplementIteratorDispatcher for I
where
    I: IntoIterator + Sized,
    I::Item: Complementable,
{
}

/// Returns the interval complement of each element
#[derive(Debug, Clone, Hash)]
pub struct ComplementIter<I> {
    iter: I,
}

impl<I> ComplementIter<I>
where
    I: Iterator,
    I::Item: Complementable,
{
    pub fn new(iter: I) -> Self {
        ComplementIter { iter }
    }
}

impl<I> Iterator for ComplementIter<I>
where
    I: Iterator,
    I::Item: Complementable,
{
    type Item = ComplementResult<<I::Item as Complementable>::Output>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.complement())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I> DoubleEndedIterator for ComplementIter<I>
where
    I: DoubleEndedIterator,
    I::Item: Complementable,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.complement())
    }
}

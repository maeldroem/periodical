//! Iterator to remove empty intervals
//!
//! This iterator uses the [`Emptiable`] trait to determine what is considered an empty interval.
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
//! # };
//! # use periodical::iter::intervals::remove_empty::RemoveEmptyIntervalsIteratorDispatcher;
//! let intervals = [
//!     EmptiableAbsoluteBounds::Empty,
//!     EmptiableAbsoluteBounds::Empty,
//!     EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     )),
//!     EmptiableAbsoluteBounds::Empty,
//!     EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     )),
//!     EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 15:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     )),
//!     EmptiableAbsoluteBounds::Empty,
//!     EmptiableAbsoluteBounds::Empty,
//!     EmptiableAbsoluteBounds::Empty,
//! ];
//!
//! assert_eq!(
//!     intervals.remove_empty_intervals().collect::<Vec<_>>(),
//!     vec![
//!         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         )),
//!         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         )),
//!         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 15:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         )),
//!     ],
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use crate::intervals::Emptiable;

/// Dispatcher trait for empty interval removal iterator
pub trait RemoveEmptyIntervalsIteratorDispatcher
where
    Self: IntoIterator + Sized,
    Self::Item: Emptiable,
{
    /// Filters out empty intervals from the collection
    ///
    /// Uses the trait [`Emptiable`] under the hood.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    /// # };
    /// # use periodical::iter::intervals::remove_empty::RemoveEmptyIntervalsIteratorDispatcher;
    /// let intervals = [
    ///     EmptiableAbsoluteBounds::Empty,
    ///     EmptiableAbsoluteBounds::Empty,
    ///     EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     )),
    ///     EmptiableAbsoluteBounds::Empty,
    ///     EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     )),
    ///     EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 15:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     )),
    ///     EmptiableAbsoluteBounds::Empty,
    ///     EmptiableAbsoluteBounds::Empty,
    ///     EmptiableAbsoluteBounds::Empty,
    /// ];
    ///
    /// assert_eq!(
    ///     intervals.remove_empty_intervals().collect::<Vec<_>>(),
    ///     vec![
    ///         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///         )),
    ///         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///         )),
    ///         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
    ///             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 15:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///                 "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
    ///             )),
    ///         )),
    ///     ],
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    fn remove_empty_intervals(self) -> RemoveEmptyIntervals<Self::IntoIter> {
        RemoveEmptyIntervals::new(self.into_iter())
    }
}

impl<I> RemoveEmptyIntervalsIteratorDispatcher for I
where
    I: IntoIterator + Sized,
    I::Item: Emptiable,
{
}

/// Empty interval removal iterator
///
/// Uses the trait [`Emptiable`] in order to determine what is an empty interval.
#[derive(Debug, Clone, Hash)]
pub struct RemoveEmptyIntervals<I> {
    iter: I,
}

impl<I> RemoveEmptyIntervals<I>
where
    I: Iterator,
    I::Item: Emptiable,
{
    /// Creates a new [`RemoveEmptyIntervals`]
    #[must_use]
    pub fn new(iter: I) -> Self {
        RemoveEmptyIntervals { iter }
    }
}

impl<I> Iterator for RemoveEmptyIntervals<I>
where
    I: Iterator,
    I::Item: Emptiable,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.iter.next()?;
            if !current.is_empty() {
                return Some(current);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // All items could be empty, so reset lower bound at 0
        (0, self.iter.size_hint().1)
    }
}

impl<I> DoubleEndedIterator for RemoveEmptyIntervals<I>
where
    I: DoubleEndedIterator,
    I::Item: Emptiable,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.iter.next_back()?;
            if !current.is_empty() {
                return Some(current);
            }
        }
    }
}

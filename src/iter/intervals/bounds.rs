//! Bounds iterator
//!
//! Iterator that runs over the bounds of a set of intervals.
//!
//! Remember, this iterator **does not** sort the intervals' bound. This means that the bounds output by the iterator
//! are in the same order than the intervals.
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
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
//!     intervals.abs_bounds_iter().collect::<Vec<_>>(),
//!     vec![
//!         AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         ))),
//!         AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
//!         ))),
//!         AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!         ))),
//!         AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!         ))),
//!     ],
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::iter::{FusedIterator, Peekable};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteBounds};
use crate::intervals::bound_position::BoundPosition;
use crate::intervals::relative::{RelativeBound, RelativeBounds};
use crate::iter::intervals::layered_bounds::{LayeredAbsoluteBounds, LayeredRelativeBounds};
use crate::iter::intervals::united_bounds::{AbsoluteUnitedBoundsIter, RelativeUnitedBoundsIter};

/// Iterator of [`AbsoluteBound`] from absolute intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBoundsIter {
    bounds: Vec<AbsoluteBounds>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl AbsoluteBoundsIter {
    /// Creates a new [`AbsoluteBoundsIter`]
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = AbsoluteBounds>,
    {
        AbsoluteBoundsIter {
            bounds: iter.collect::<Vec<_>>(),
            position: BoundPosition::default(),
            initd: true,
            exhausted: false,
        }
    }

    /// Unites the bounds
    ///
    /// Collects the bounds, sorts them and creates an [`AbsoluteUnitedBoundsIter`] from them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
    /// let intervals = [
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    /// ];
    ///
    /// assert_eq!(
    ///     intervals.abs_bounds_iter().united().collect::<Vec<_>>(),
    ///     vec![
    ///         AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         ))),
    ///         AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///         ))),
    ///     ],
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn united(self) -> AbsoluteUnitedBoundsIter<Peekable<impl Iterator<Item = AbsoluteBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort();

        AbsoluteUnitedBoundsIter::new(bounds.into_iter())
    }

    /// Creates a [`LayeredAbsoluteBounds`] without checking if it violates invariants
    ///
    /// Combines the current iterator and the given other iterator into a [`LayeredAbsoluteBounds`] without
    /// checking if any of them violate invariants.
    ///
    /// It is possible to use this method safely, for example in order to avoid going
    /// through an [`AbsoluteUnitedBoundsIter`] between each use
    /// of [set operations on layered bounds iterators](crate::iter::intervals::layered_bounds_set_ops),
    /// especially if the operation guarantees that there are no overlapping intervals left.
    ///
    /// To make sure you use this method in a safe manner, double-check that this iterator,
    /// acting as the first layer, and the given iterator, acting as the second layer, don't violate
    /// the input requirements laid out by [`LayeredAbsoluteBounds`], see [`LayeredAbsoluteBounds::new`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    /// ];
    ///
    /// let layered_bounds = first_layer_intervals
    ///     .abs_bounds_iter()
    ///     .unchecked_layer(second_layer_intervals.abs_bounds_iter());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn unchecked_layer(
        self,
        second_layer: AbsoluteBoundsIter,
    ) -> LayeredAbsoluteBounds<Peekable<Self>, Peekable<AbsoluteBoundsIter>> {
        LayeredAbsoluteBounds::new(self, second_layer)
    }
}

impl Iterator for AbsoluteBoundsIter {
    type Item = AbsoluteBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        if !self.initd && self.position.next_bound() {
            self.exhausted = true;
            return None;
        }

        if self.initd {
            self.initd = false;
        }

        self.position.get_abs_bound(&self.bounds)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let bounds_amount = self.bounds.len().checked_mul(2);

        (bounds_amount.unwrap_or(usize::MAX), bounds_amount)
    }
}

impl FusedIterator for AbsoluteBoundsIter {}

impl ExactSizeIterator for AbsoluteBoundsIter {}

impl FromIterator<AbsoluteBounds> for AbsoluteBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = AbsoluteBounds>,
    {
        AbsoluteBoundsIter::new(iter.into_iter())
    }
}

impl Extend<AbsoluteBounds> for AbsoluteBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = AbsoluteBounds>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`AbsoluteBoundsIter`]
pub trait AbsoluteBoundsIteratorDispatcher: IntoIterator<Item = AbsoluteBounds> + Sized {
    /// Creates an [`AbsoluteBoundsIter`] from the collection
    fn abs_bounds_iter(self) -> AbsoluteBoundsIter {
        AbsoluteBoundsIter::new(self.into_iter())
    }
}

impl<I> AbsoluteBoundsIteratorDispatcher for I where I: IntoIterator<Item = AbsoluteBounds> + Sized {}

/// Iterator of [`RelativeBound`] from relative intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativeBoundsIter {
    bounds: Vec<RelativeBounds>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl RelativeBoundsIter {
    /// Creates a new [`RelativeBoundsIter`]
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = RelativeBounds>,
    {
        RelativeBoundsIter {
            bounds: iter.collect::<Vec<_>>(),
            position: BoundPosition::default(),
            initd: true,
            exhausted: false,
        }
    }

    /// Unites the bounds
    ///
    /// Collects the bounds, sorts them and creates an [`RelativeUnitedBoundsIter`] from them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBound, RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// # use periodical::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
    /// let intervals = [
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(8),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(14),
    ///         )),
    ///     ),
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(12),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(16),
    ///         )),
    ///     ),
    /// ];
    ///
    /// assert_eq!(
    ///     intervals.rel_bounds_iter().united().collect::<Vec<_>>(),
    ///     vec![
    ///         RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(8),
    ///         ))),
    ///         RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(16),
    ///         ))),
    ///     ],
    /// );
    /// ```
    #[must_use]
    pub fn united(self) -> RelativeUnitedBoundsIter<Peekable<impl Iterator<Item = RelativeBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort();

        RelativeUnitedBoundsIter::new(bounds.into_iter())
    }

    /// Creates a [`LayeredRelativeBounds`] without checking if it violates invariants
    ///
    /// Combines the current iterator and the given other iterator into a [`LayeredRelativeBounds`] without
    /// checking if any of them violate invariants.
    ///
    /// It is possible to use this method safely, for example in order to avoid going
    /// through an [`RelativeUnitedBoundsIter`] between each use
    /// of [set operations on layered bounds iterators](crate::iter::intervals::layered_bounds_set_ops),
    /// especially if the operation guarantees that there are no overlapping intervals left.
    ///
    /// To make sure you use this method in a safe manner, double-check that this iterator,
    /// acting as the first layer, and the given iterator, acting as the second layer, don't violate
    /// the input requirements laid out by [`LayeredRelativeBounds`], see [`LayeredRelativeBounds::new`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// # use periodical::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(8),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(12),
    ///         )),
    ///     ),
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(13),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(16),
    ///         )),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(7),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(11),
    ///         )),
    ///     ),
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(14),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(18),
    ///         )),
    ///     ),
    /// ];
    ///
    /// let layered_bounds = first_layer_intervals
    ///     .rel_bounds_iter()
    ///     .unchecked_layer(second_layer_intervals.rel_bounds_iter());
    /// ```
    #[must_use]
    pub fn unchecked_layer(
        self,
        second_layer: RelativeBoundsIter,
    ) -> LayeredRelativeBounds<Peekable<Self>, Peekable<RelativeBoundsIter>> {
        LayeredRelativeBounds::new(self, second_layer)
    }
}

impl Iterator for RelativeBoundsIter {
    type Item = RelativeBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        if !self.initd && self.position.next_bound() {
            self.exhausted = true;
            return None;
        }

        if self.initd {
            self.initd = false;
        }

        self.position.get_rel_bound(&self.bounds)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let bounds_amount = self.bounds.len().checked_mul(2);

        (bounds_amount.unwrap_or(usize::MAX), bounds_amount)
    }
}

impl FusedIterator for RelativeBoundsIter {}

impl ExactSizeIterator for RelativeBoundsIter {}

impl FromIterator<RelativeBounds> for RelativeBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = RelativeBounds>,
    {
        RelativeBoundsIter::new(iter.into_iter())
    }
}

impl Extend<RelativeBounds> for RelativeBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = RelativeBounds>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`RelativeBoundsIter`]
pub trait RelativeBoundsIteratorDispatcher: IntoIterator<Item = RelativeBounds> + Sized {
    /// Creates an [`RelativeBoundsIter`] from the collection
    fn rel_bounds_iter(self) -> RelativeBoundsIter {
        RelativeBoundsIter::new(self.into_iter())
    }
}

impl<I> RelativeBoundsIteratorDispatcher for I where I: IntoIterator<Item = RelativeBounds> + Sized {}

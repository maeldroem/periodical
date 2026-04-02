//! Bounds iterator
//!
//! Iterator that runs over the bounds of a set of intervals.
//!
//! Remember, this iterator **does not** sort the intervals' bound. This means
//! that the bounds output by the iterator are in the same order than the
//! intervals.
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
//! let intervals = [
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 11:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//! ];
//!
//! assert_eq!(
//!     intervals.abs_bounds_iter().collect::<Vec<_>>(),
//!     vec![
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound()
//!         .to_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 11:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound()
//!         .to_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound()
//!         .to_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound()
//!         .to_bound(),
//!     ],
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use std::iter::{FusedIterator, Peekable};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteBoundPair};
use crate::intervals::bound_position::BoundPosition;
use crate::intervals::relative::{RelativeBound, RelativeBoundPair};
use crate::iter::intervals::layered_bounds::{LayeredAbsoluteBounds, LayeredRelativeBounds};
use crate::iter::intervals::united_bounds::{AbsoluteUnitedBoundsIter, RelativeUnitedBoundsIter};

/// Iterator of [`AbsoluteBound`] from absolute intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteBoundsIter {
    bounds: Vec<AbsoluteBoundPair>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl AbsoluteBoundsIter {
    /// Creates a new [`AbsoluteBoundsIter`]
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = AbsoluteBoundPair>,
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
    /// Collects the bounds, sorts them and creates an
    /// [`AbsoluteUnitedBoundsIter`] from them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
    /// let intervals = [
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    /// ];
    ///
    /// assert_eq!(
    ///     intervals
    ///         .abs_bounds_iter()
    ///         .unite_bounds()
    ///         .collect::<Vec<_>>(),
    ///     vec![
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound()
    ///         .to_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound()
    ///         .to_bound(),
    ///     ],
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn unite_bounds(self) -> AbsoluteUnitedBoundsIter<Peekable<impl Iterator<Item = AbsoluteBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort();

        AbsoluteUnitedBoundsIter::new(bounds.into_iter())
    }

    /// Creates a [`LayeredAbsoluteBounds`] without checking if it violates
    /// invariants
    ///
    /// Combines the current iterator and the given other iterator into a
    /// [`LayeredAbsoluteBounds`] without checking if any of them violate
    /// invariants.
    ///
    /// It is possible to use this method safely, for example in order to avoid
    /// going through an [`AbsoluteUnitedBoundsIter`] between each use
    /// of [set operations on layered bounds iterators](crate::iter::intervals::layered_bounds_set_ops),
    /// especially if the operation guarantees that there are no overlapping
    /// intervals left.
    ///
    /// To make sure you use this method in a safe manner, double-check that
    /// this iterator, acting as the first layer, and the given iterator,
    /// acting as the second layer, don't violate the input requirements
    /// laid out by [`LayeredAbsoluteBounds`], see
    /// [`LayeredAbsoluteBounds::new`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 13:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 07:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 11:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 18:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let layered_bounds = first_layer_intervals
    ///     .abs_bounds_iter()
    ///     .unchecked_layer(second_layer_intervals.abs_bounds_iter());
    /// # Ok::<(), Box<dyn Error>>(())
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

impl FromIterator<AbsoluteBoundPair> for AbsoluteBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = AbsoluteBoundPair>,
    {
        AbsoluteBoundsIter::new(iter.into_iter())
    }
}

impl Extend<AbsoluteBoundPair> for AbsoluteBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = AbsoluteBoundPair>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`AbsoluteBoundsIter`]
pub trait AbsoluteBoundsIteratorDispatcher: IntoIterator<Item = AbsoluteBoundPair> + Sized {
    /// Creates an [`AbsoluteBoundsIter`] from the collection
    fn abs_bounds_iter(self) -> AbsoluteBoundsIter {
        AbsoluteBoundsIter::new(self.into_iter())
    }
}

impl<I> AbsoluteBoundsIteratorDispatcher for I where I: IntoIterator<Item = AbsoluteBoundPair> + Sized {}

/// Iterator of [`RelativeBound`] from relative intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeBoundsIter {
    bounds: Vec<RelativeBoundPair>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl RelativeBoundsIter {
    /// Creates a new [`RelativeBoundsIter`]
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = RelativeBoundPair>,
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
    /// Collects the bounds, sorts them and creates an
    /// [`RelativeUnitedBoundsIter`] from them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBound};
    /// # use periodical::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
    /// let intervals = [
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(14)).to_end_bound(),
    ///     ),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(12)).to_start_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// assert_eq!(
    ///     intervals
    ///         .rel_bounds_iter()
    ///         .unite_bounds()
    ///         .collect::<Vec<_>>(),
    ///     vec![
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(8),)
    ///             .to_start_bound()
    ///             .to_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(16),)
    ///             .to_end_bound()
    ///             .to_bound(),
    ///     ],
    /// );
    /// ```
    #[must_use]
    pub fn unite_bounds(self) -> RelativeUnitedBoundsIter<Peekable<impl Iterator<Item = RelativeBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort();

        RelativeUnitedBoundsIter::new(bounds.into_iter())
    }

    /// Creates a [`LayeredRelativeBounds`] without checking if it violates
    /// invariants
    ///
    /// Combines the current iterator and the given other iterator into a
    /// [`LayeredRelativeBounds`] without checking if any of them violate
    /// invariants.
    ///
    /// It is possible to use this method safely, for example in order to avoid
    /// going through an [`RelativeUnitedBoundsIter`] between each use
    /// of [set operations on layered bounds iterators](crate::iter::intervals::layered_bounds_set_ops),
    /// especially if the operation guarantees that there are no overlapping
    /// intervals left.
    ///
    /// To make sure you use this method in a safe manner, double-check that
    /// this iterator, acting as the first layer, and the given iterator,
    /// acting as the second layer, don't violate the input requirements
    /// laid out by [`LayeredRelativeBounds`], see
    /// [`LayeredRelativeBounds::new`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBound};
    /// # use periodical::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(12)).to_end_bound(),
    ///     ),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(13)).to_start_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(7)).to_start_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(11)).to_end_bound(),
    ///     ),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(14)).to_start_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(18)).to_end_bound(),
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

impl FromIterator<RelativeBoundPair> for RelativeBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = RelativeBoundPair>,
    {
        RelativeBoundsIter::new(iter.into_iter())
    }
}

impl Extend<RelativeBoundPair> for RelativeBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = RelativeBoundPair>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`RelativeBoundsIter`]
pub trait RelativeBoundsIteratorDispatcher: IntoIterator<Item = RelativeBoundPair> + Sized {
    /// Creates an [`RelativeBoundsIter`] from the collection
    fn rel_bounds_iter(self) -> RelativeBoundsIter {
        RelativeBoundsIter::new(self.into_iter())
    }
}

impl<I> RelativeBoundsIteratorDispatcher for I where I: IntoIterator<Item = RelativeBoundPair> + Sized {}

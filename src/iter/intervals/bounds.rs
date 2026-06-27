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
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
//! let intervals = [
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 11:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
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
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound()
//!         .to_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 11:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound()
//!         .to_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound()
//!         .to_bound(),
//!         AbsFiniteBoundPos::new(
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

use crate::intervals::absolute::{AbsBound, AbsBoundPair};
use crate::intervals::bound_position::BoundPosition;
use crate::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{RelBound, RelBoundPair};
use crate::iter::intervals::layered_bounds::{LayeredAbsBounds, LayeredRelBounds};
use crate::iter::intervals::united_bounds::{AbsUnitedBoundsIter, RelUnitedBoundsIter};

/// Iterator of [`AbsBound`] from absolute intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsBoundsIter {
    bounds: Vec<AbsBoundPair>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl AbsBoundsIter {
    /// Creates a new [`AbsBoundsIter`]
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = AbsBoundPair>,
    {
        AbsBoundsIter {
            bounds: iter.collect::<Vec<_>>(),
            position: BoundPosition::default(),
            initd: true,
            exhausted: false,
        }
    }

    /// Unites the bounds
    ///
    /// Collects the bounds, sorts them and creates an
    /// [`AbsUnitedBoundsIter`] from them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
    /// let intervals = [
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
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
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound()
    ///         .to_bound(),
    ///         AbsFiniteBoundPos::new(
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
    pub fn unite_bounds(self) -> AbsUnitedBoundsIter<Peekable<impl Iterator<Item = AbsBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));

        AbsUnitedBoundsIter::new(bounds.into_iter())
    }

    /// Creates a [`LayeredAbsBounds`] without checking if it violates
    /// invariants
    ///
    /// Combines the current iterator and the given other iterator into a
    /// [`LayeredAbsBounds`] without checking if any of them violate
    /// invariants.
    ///
    /// It is possible to use this method safely, for example in order to avoid
    /// going through an [`AbsUnitedBoundsIter`] between each use
    /// of [set operations on layered bounds iterators](crate::iter::intervals::layered_bounds_set_ops),
    /// especially if the operation guarantees that there are no overlapping
    /// intervals left.
    ///
    /// To make sure you use this method in a safe manner, double-check that
    /// this iterator, acting as the first layer, and the given iterator,
    /// acting as the second layer, don't violate the input requirements
    /// laid out by [`LayeredAbsBounds`], see
    /// [`LayeredAbsBounds::new`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 13:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 07:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 11:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
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
        second_layer: AbsBoundsIter,
    ) -> LayeredAbsBounds<Peekable<Self>, Peekable<AbsBoundsIter>> {
        LayeredAbsBounds::new(self, second_layer)
    }
}

impl Iterator for AbsBoundsIter {
    type Item = AbsBound;

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

impl FusedIterator for AbsBoundsIter {}

impl ExactSizeIterator for AbsBoundsIter {}

impl FromIterator<AbsBoundPair> for AbsBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = AbsBoundPair>,
    {
        AbsBoundsIter::new(iter.into_iter())
    }
}

impl Extend<AbsBoundPair> for AbsBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = AbsBoundPair>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`AbsBoundsIter`]
pub trait AbsBoundsIteratorDispatcher: IntoIterator<Item = AbsBoundPair> + Sized {
    /// Creates an [`AbsBoundsIter`] from the collection
    fn abs_bounds_iter(self) -> AbsBoundsIter {
        AbsBoundsIter::new(self.into_iter())
    }
}

impl<I> AbsBoundsIteratorDispatcher for I where I: IntoIterator<Item = AbsBoundPair> + Sized {}

/// Iterator of [`RelBound`] from relative intervals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelBoundsIter {
    bounds: Vec<RelBoundPair>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl RelBoundsIter {
    /// Creates a new [`RelBoundsIter`]
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = RelBoundPair>,
    {
        RelBoundsIter {
            bounds: iter.collect::<Vec<_>>(),
            position: BoundPosition::default(),
            initd: true,
            exhausted: false,
        }
    }

    /// Unites the bounds
    ///
    /// Collects the bounds, sorts them and creates an
    /// [`RelUnitedBoundsIter`] from them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// # use periodical::iter::intervals::bounds::RelBoundsIteratorDispatcher;
    /// let intervals = [
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(14)).to_end_bound(),
    ///     ),
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(12)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// assert_eq!(
    ///     intervals
    ///         .rel_bounds_iter()
    ///         .unite_bounds()
    ///         .collect::<Vec<_>>(),
    ///     vec![
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(8),)
    ///             .to_start_bound()
    ///             .to_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(16),)
    ///             .to_end_bound()
    ///             .to_bound(),
    ///     ],
    /// );
    /// ```
    #[must_use]
    pub fn unite_bounds(self) -> RelUnitedBoundsIter<Peekable<impl Iterator<Item = RelBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));

        RelUnitedBoundsIter::new(bounds.into_iter())
    }

    /// Creates a [`LayeredRelBounds`] without checking if it violates
    /// invariants
    ///
    /// Combines the current iterator and the given other iterator into a
    /// [`LayeredRelBounds`] without checking if any of them violate
    /// invariants.
    ///
    /// It is possible to use this method safely, for example in order to avoid
    /// going through an [`RelUnitedBoundsIter`] between each use
    /// of [set operations on layered bounds iterators](crate::iter::intervals::layered_bounds_set_ops),
    /// especially if the operation guarantees that there are no overlapping
    /// intervals left.
    ///
    /// To make sure you use this method in a safe manner, double-check that
    /// this iterator, acting as the first layer, and the given iterator,
    /// acting as the second layer, don't violate the input requirements
    /// laid out by [`LayeredRelBounds`], see
    /// [`LayeredRelBounds::new`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// # use periodical::iter::intervals::bounds::RelBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(12)).to_end_bound(),
    ///     ),
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(13)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(7)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(11)).to_end_bound(),
    ///     ),
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(14)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(18)).to_end_bound(),
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
        second_layer: RelBoundsIter,
    ) -> LayeredRelBounds<Peekable<Self>, Peekable<RelBoundsIter>> {
        LayeredRelBounds::new(self, second_layer)
    }
}

impl Iterator for RelBoundsIter {
    type Item = RelBound;

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

impl FusedIterator for RelBoundsIter {}

impl ExactSizeIterator for RelBoundsIter {}

impl FromIterator<RelBoundPair> for RelBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = RelBoundPair>,
    {
        RelBoundsIter::new(iter.into_iter())
    }
}

impl Extend<RelBoundPair> for RelBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = RelBoundPair>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`RelBoundsIter`]
pub trait RelBoundsIteratorDispatcher: IntoIterator<Item = RelBoundPair> + Sized {
    /// Creates an [`RelBoundsIter`] from the collection
    fn rel_bounds_iter(self) -> RelBoundsIter {
        RelBoundsIter::new(self.into_iter())
    }
}

impl<I> RelBoundsIteratorDispatcher for I where I: IntoIterator<Item = RelBoundPair> + Sized {}

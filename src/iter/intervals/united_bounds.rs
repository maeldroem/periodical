//! United bounds iterators
//!
//! Iterators to unite a collection of bounds, assuring that the bounds are no
//! longer overlapping.
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsBound, AbsBoundPair, AbsFiniteBoundPos};
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
//!             "2025-01-01 14:00:00[Europe/Oslo]"
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
//!     intervals
//!         .abs_bounds_iter()
//!         .unite_bounds()
//!         .collect::<Vec<_>>(),
//!     vec![
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
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

use std::cmp::Ordering;
use std::iter::{FusedIterator, Peekable};

use crate::intervals::absolute::{AbsBound, AbsEndBound};
use crate::intervals::ops::BoundOrd;
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
use crate::intervals::relative::{RelBound, RelEndBound};
use crate::iter::intervals::layered_bounds::{LayeredAbsBounds, LayeredRelBounds};

/// Iterator for uniting absolute bounds
///
/// # Panics
///
/// Panics if the number of active layers overflows [`u64`].
pub struct AbsUnitedBoundsIter<I> {
    iter: I,
    layer: u64,
    is_next_start_adjacent: bool,
    exhausted: bool,
}

impl<I> AbsUnitedBoundsIter<I>
where
    I: Iterator<Item = AbsBound>,
{
    /// Creates a new [`AbsUnitedBoundsIter`]
    ///
    /// # Input requirements
    ///
    /// 1. The bounds **must be sorted chronologically**
    /// 2. The bounds **must be paired**, that means there should be an equal amount of [`Start`](AbsBound::Start)s and
    ///    [`End`](AbsBound::End)s.
    ///
    /// The responsibility of verifying those requirements are left to the
    /// caller in order to prevent double-processing.
    ///
    /// Requirement 1 is automatically guaranteed if the iterator is created
    /// from [`AbsBoundsIter::unite_bounds`](crate::iter::intervals::bounds::AbsBoundsIter::unite_bounds).
    ///
    /// Requirement 2 is automatically guaranteed if the bounds are obtained
    /// from
    /// a set of [intervals](crate::intervals::absolute::AbsInterval)
    /// or from [bound pairs](crate::intervals::absolute::AbsBoundPair) and
    /// then processed through
    /// [`AbsBoundsIter`](crate::iter::intervals::bounds::AbsBoundsIter).
    #[must_use]
    pub fn new(iter: I) -> AbsUnitedBoundsIter<Peekable<I>> {
        AbsUnitedBoundsIter {
            iter: iter.peekable(),
            layer: 0,
            is_next_start_adjacent: false,
            exhausted: false,
        }
    }
}

impl<I> AbsUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = AbsBound>,
{
    /// Layers this iterator with the given other [`AbsUnitedBoundsIter`]
    ///
    /// The given other [`AbsUnitedBoundsIter`] acts at the second layer in
    /// the resulting [`LayeredAbsBounds`].
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
    ///     .unite_bounds()
    ///     .layer(second_layer_intervals.abs_bounds_iter().unite_bounds());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn layer<J>(
        self,
        second_layer: AbsUnitedBoundsIter<Peekable<J>>,
    ) -> LayeredAbsBounds<Peekable<Self>, Peekable<AbsUnitedBoundsIter<Peekable<J>>>>
    where
        J: Iterator<Item = AbsBound>,
    {
        LayeredAbsBounds::new(self, second_layer)
    }
}

impl<I> Iterator for AbsUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = AbsBound>,
{
    type Item = AbsBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        loop {
            let Some(next) = self.iter.next() else {
                self.exhausted = true;
                return None;
            };

            match next {
                AbsBound::Start(_) => {
                    self.layer = self
                        .layer
                        .checked_add(1)
                        .expect("The number of active layers overflowed when using `AbsUniteBoundsIter`");

                    if self.is_next_start_adjacent {
                        self.is_next_start_adjacent = false;
                        continue;
                    }

                    // Since we already incremented the layer, the first counted start bound must be
                    // on layer 1 i.e. we were on the bottom layer (0) and it
                    // just was incremented to 1. This technically also guards
                    // against start bounds that, after incrementing, remain
                    // on layer 0, but this impossible as it would required going in the negatives
                    // (and since we are using an unsigned number, you see where this is going)
                    if self.layer > 1 {
                        continue;
                    }
                },
                AbsBound::End(next_end) => {
                    self.layer = self.layer.checked_sub(1).expect(
                        "An error occurred with `AbsUniteBoundsIter`: The number of active layers underflowed, which \
                         is unexpected",
                    );

                    // Since we already decremented the layer, the last counted end bound must be on
                    // layer 0 i.e. we were on the first layer (1) and it just
                    // was decremented to 0.
                    if self.layer > 0 {
                        continue;
                    }

                    // If the peeked value is a start bound that is adjacent to the current bound,
                    // we don't return this end bound. Since the layer decrement already happened
                    // and we know it's gonna be incremented again, we know that
                    // the layer will end up at 1, which is problematic
                    // as it would be a layer number that makes the start bound considered as the
                    // first start bound of a new interval.
                    // In order to solve this, we set a variable that will tell the iterator to skip
                    // the next start bound, like this end (and the following
                    // start) never happened.
                    if self
                        .iter
                        .peek()
                        .is_some_and(|peeked| is_abs_end_bound_adjacent_to_abs_peeked(&next_end, peeked))
                    {
                        self.is_next_start_adjacent = true;
                        continue;
                    }
                },
            }

            return Some(next);
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();
        (
            inner_size_hint.0.saturating_mul(2),
            inner_size_hint.1.and_then(|x| x.checked_mul(2)),
        )
    }
}

impl<I> FusedIterator for AbsUnitedBoundsIter<Peekable<I>> where I: Iterator<Item = AbsBound> {}

fn is_abs_end_bound_adjacent_to_abs_peeked(end: &AbsEndBound, peeked: &AbsBound) -> bool {
    let AbsBound::Start(peeked_start) = peeked else {
        return false;
    };

    matches!(
        end.bound_cmp(peeked_start)
            .disambiguate(BoundOverlapDisambiguationRuleSet::Lenient),
        Ordering::Equal,
    )
}

/// Iterator for uniting relative bounds
///
/// # Panics
///
/// Panics if the number of active layers overflows [`u64`].
pub struct RelUnitedBoundsIter<I> {
    iter: I,
    layer: u64,
    is_next_start_adjacent: bool,
    exhausted: bool,
}

impl<I> RelUnitedBoundsIter<I>
where
    I: Iterator<Item = RelBound>,
{
    /// Creates a new [`RelUnitedBoundsIter`]
    ///
    /// # Input requirements
    ///
    /// 1. The bounds **must be sorted chronologically**
    /// 2. The bounds **must be paired**, that means there should be an equal amount of [`Start`](RelBound::Start)s and
    ///    [`End`](RelBound::End)s.
    ///
    /// The responsibility of verifying those requirements are left to the
    /// caller in order to prevent double-processing.
    ///
    /// Requirement 1 is automatically guaranteed if the iterator is created
    /// from [`RelBoundsIter::unite_bounds`](crate::iter::intervals::bounds::RelBoundsIter::unite_bounds).
    ///
    /// Requirement 2 is automatically guaranteed if the bounds are obtained
    /// from
    /// a set of [intervals](crate::intervals::relative::RelInterval)
    /// or from [bound pairs](crate::intervals::relative::RelBoundPair) and
    /// then processed through
    /// [`RelBoundsIter`](crate::iter::intervals::bounds::RelBoundsIter).
    #[must_use]
    pub fn new(iter: I) -> RelUnitedBoundsIter<Peekable<I>> {
        // Add debug assertion on iter being sorted
        RelUnitedBoundsIter {
            iter: iter.peekable(),
            layer: 0,
            is_next_start_adjacent: false,
            exhausted: false,
        }
    }
}

impl<I> RelUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = RelBound>,
{
    /// Layers this iterator with the given other [`RelUnitedBoundsIter`]
    ///
    /// The given other [`RelUnitedBoundsIter`] acts at the second layer in
    /// the resulting [`LayeredRelBounds`].
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
    ///     .unite_bounds()
    ///     .layer(second_layer_intervals.rel_bounds_iter().unite_bounds());
    /// ```
    pub fn layer<J>(
        self,
        second_layer: RelUnitedBoundsIter<Peekable<J>>,
    ) -> LayeredRelBounds<Peekable<Self>, Peekable<RelUnitedBoundsIter<Peekable<J>>>>
    where
        J: Iterator<Item = RelBound>,
    {
        LayeredRelBounds::new(self, second_layer)
    }
}

impl<I> Iterator for RelUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = RelBound>,
{
    type Item = RelBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        loop {
            let Some(next) = self.iter.next() else {
                self.exhausted = true;
                return None;
            };

            match next {
                RelBound::Start(_) => {
                    self.layer = self
                        .layer
                        .checked_add(1)
                        .expect("The number of active layers overflowed when using `RelUniteBoundsIter`");

                    if self.is_next_start_adjacent {
                        self.is_next_start_adjacent = false;
                        continue;
                    }

                    // Since we already incremented the layer, the first counted start bound must be
                    // on layer 1 i.e. we were on the bottom layer (0) and it
                    // just was incremented to 1. This technically also guards
                    // against start bounds that, after incrementing, remain
                    // on layer 0, but this impossible as it would required going in the negatives
                    // (and since we are using an unsigned number, you see where this is going)
                    if self.layer > 1 {
                        continue;
                    }
                },
                RelBound::End(next_end) => {
                    self.layer = self.layer.checked_sub(1).expect(
                        "An error occurred with `RelUniteBoundsIter`: The number of active layers underflowed, which \
                         is unexpected",
                    );

                    // Since we already decremented the layer, the last counted end bound must be on
                    // layer 0 i.e. we were on the first layer (1) and it just
                    // was decremented to 0.
                    if self.layer > 0 {
                        continue;
                    }

                    // If the peeked value is a start bound that is adjacent to the current bound,
                    // we don't return this end bound. Since the layer decrement already happened
                    // and we know it's gonna be incremented again, we know that
                    // the layer will end up at 1, which is problematic
                    // as it would be a layer number that makes the start bound considered as the
                    // first start bound of a new interval.
                    // In order to solve this, we set a variable that will tell the iterator to skip
                    // the next start bound, like this end (and the following
                    // start) never happened.
                    if self
                        .iter
                        .peek()
                        .is_some_and(|peeked| is_rel_end_bound_adjacent_to_rel_peeked(&next_end, peeked))
                    {
                        self.is_next_start_adjacent = true;
                        continue;
                    }
                },
            }

            return Some(next);
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();
        (
            inner_size_hint.0.saturating_mul(2),
            inner_size_hint.1.and_then(|x| x.checked_mul(2)),
        )
    }
}

impl<I> FusedIterator for RelUnitedBoundsIter<Peekable<I>> where I: Iterator<Item = RelBound> {}

fn is_rel_end_bound_adjacent_to_rel_peeked(end: &RelEndBound, peeked: &RelBound) -> bool {
    let RelBound::Start(peeked_start) = peeked else {
        return false;
    };

    matches!(
        end.bound_cmp(peeked_start)
            .disambiguate(BoundOverlapDisambiguationRuleSet::Lenient),
        Ordering::Equal,
    )
}

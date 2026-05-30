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
//! # use periodical::intervals::absolute::{AbsoluteBound, AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
//! # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
//! let intervals = [
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_start_bound(),
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_end_bound(),
//!     ),
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_start_bound(),
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_end_bound(),
//!     ),
//! ];
//!
//! assert_eq!(
//!     intervals.abs_bounds_iter().unite_bounds().collect::<Vec<_>>(),
//!     vec![
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_start_bound().to_bound(),
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_end_bound().to_bound(),
//!     ],
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use std::cmp::Ordering;
use std::iter::{FusedIterator, Peekable};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound};
use crate::intervals::ops::bound_ord::BoundPartialOrd;
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
use crate::intervals::relative::{RelativeBound, RelativeEndBound};
use crate::iter::intervals::layered_bounds::{LayeredAbsoluteBounds, LayeredRelativeBounds};

/// Iterator for uniting absolute bounds
///
/// # Panics
///
/// Panics if the number of active layers overflows [`u64`].
pub struct AbsoluteUnitedBoundsIter<I> {
    iter: I,
    layer: u64,
    is_next_start_adjacent: bool,
    exhausted: bool,
}

impl<I> AbsoluteUnitedBoundsIter<I>
where
    I: Iterator<Item = AbsoluteBound>,
{
    /// Creates a new [`AbsoluteUnitedBoundsIter`]
    ///
    /// # Input requirements
    ///
    /// 1. The bounds **must be sorted chronologically**
    /// 2. The bounds **must be paired**, that means there should be an equal amount of [`Start`](AbsoluteBound::Start)s
    ///    and [`End`](AbsoluteBound::End)s.
    ///
    /// The responsibility of verifying those requirements are left to the
    /// caller in order to prevent double-processing.
    ///
    /// Requirement 1 is automatically guaranteed if the iterator is created
    /// from [`AbsoluteBoundsIter::unite_bounds`](crate::iter::intervals::bounds::AbsoluteBoundsIter::unite_bounds).
    ///
    /// Requirement 2 is automatically guaranteed if the bounds are obtained
    /// from
    /// a set of [intervals](crate::intervals::absolute::AbsoluteInterval)
    /// or from [bound pairs](crate::intervals::absolute::AbsoluteBoundPair) and
    /// then processed through
    /// [`AbsoluteBoundsIter`](crate::iter::intervals::bounds::AbsoluteBoundsIter).
    #[must_use]
    pub fn new(iter: I) -> AbsoluteUnitedBoundsIter<Peekable<I>> {
        AbsoluteUnitedBoundsIter {
            iter: iter.peekable(),
            layer: 0,
            is_next_start_adjacent: false,
            exhausted: false,
        }
    }
}

impl<I> AbsoluteUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = AbsoluteBound>,
{
    /// Layers this iterator with the given other [`AbsoluteUnitedBoundsIter`]
    ///
    /// The given other [`AbsoluteUnitedBoundsIter`] acts at the second layer in
    /// the resulting [`LayeredAbsoluteBounds`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 13:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
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
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 07:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 11:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
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
        second_layer: AbsoluteUnitedBoundsIter<Peekable<J>>,
    ) -> LayeredAbsoluteBounds<Peekable<Self>, Peekable<AbsoluteUnitedBoundsIter<Peekable<J>>>>
    where
        J: Iterator<Item = AbsoluteBound>,
    {
        LayeredAbsoluteBounds::new(self, second_layer)
    }
}

impl<I> Iterator for AbsoluteUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = AbsoluteBound>,
{
    type Item = AbsoluteBound;

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
                AbsoluteBound::Start(_) => {
                    self.layer = self
                        .layer
                        .checked_add(1)
                        .expect("The number of active layers overflowed when using `AbsoluteUniteBoundsIter`");

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
                AbsoluteBound::End(next_end) => {
                    self.layer = self.layer.checked_sub(1).expect(
                        "An error occurred with `AbsoluteUniteBoundsIter`: The number of active layers underflowed, \
                         which is unexpected",
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

impl<I> FusedIterator for AbsoluteUnitedBoundsIter<Peekable<I>> where I: Iterator<Item = AbsoluteBound> {}

fn is_abs_end_bound_adjacent_to_abs_peeked(end: &AbsoluteEndBound, peeked: &AbsoluteBound) -> bool {
    let AbsoluteBound::Start(peeked_start) = peeked else {
        return false;
    };

    matches!(
        end.bound_partial_cmp(peeked_start)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        Ordering::Equal,
    )
}

/// Iterator for uniting relative bounds
///
/// # Panics
///
/// Panics if the number of active layers overflows [`u64`].
pub struct RelativeUnitedBoundsIter<I> {
    iter: I,
    layer: u64,
    is_next_start_adjacent: bool,
    exhausted: bool,
}

impl<I> RelativeUnitedBoundsIter<I>
where
    I: Iterator<Item = RelativeBound>,
{
    /// Creates a new [`RelativeUnitedBoundsIter`]
    ///
    /// # Input requirements
    ///
    /// 1. The bounds **must be sorted chronologically**
    /// 2. The bounds **must be paired**, that means there should be an equal amount of [`Start`](RelativeBound::Start)s
    ///    and [`End`](RelativeBound::End)s.
    ///
    /// The responsibility of verifying those requirements are left to the
    /// caller in order to prevent double-processing.
    ///
    /// Requirement 1 is automatically guaranteed if the iterator is created
    /// from [`RelativeBoundsIter::unite_bounds`](crate::iter::intervals::bounds::RelativeBoundsIter::unite_bounds).
    ///
    /// Requirement 2 is automatically guaranteed if the bounds are obtained
    /// from
    /// a set of [intervals](crate::intervals::relative::RelativeInterval)
    /// or from [bound pairs](crate::intervals::relative::RelativeBoundPair) and
    /// then processed through
    /// [`RelativeBoundsIter`](crate::iter::intervals::bounds::RelativeBoundsIter).
    #[must_use]
    pub fn new(iter: I) -> RelativeUnitedBoundsIter<Peekable<I>> {
        // Add debug assertion on iter being sorted
        RelativeUnitedBoundsIter {
            iter: iter.peekable(),
            layer: 0,
            is_next_start_adjacent: false,
            exhausted: false,
        }
    }
}

impl<I> RelativeUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = RelativeBound>,
{
    /// Layers this iterator with the given other [`RelativeUnitedBoundsIter`]
    ///
    /// The given other [`RelativeUnitedBoundsIter`] acts at the second layer in
    /// the resulting [`LayeredRelativeBounds`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// # use periodical::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
    /// let first_layer_intervals = [
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(12)).to_end_bound(),
    ///     ),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(13)).to_start_bound(),
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16)).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(7)).to_start_bound(),
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(11)).to_end_bound(),
    ///     ),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(14)).to_start_bound(),
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(18)).to_end_bound(),
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
        second_layer: RelativeUnitedBoundsIter<Peekable<J>>,
    ) -> LayeredRelativeBounds<Peekable<Self>, Peekable<RelativeUnitedBoundsIter<Peekable<J>>>>
    where
        J: Iterator<Item = RelativeBound>,
    {
        LayeredRelativeBounds::new(self, second_layer)
    }
}

impl<I> Iterator for RelativeUnitedBoundsIter<Peekable<I>>
where
    I: Iterator<Item = RelativeBound>,
{
    type Item = RelativeBound;

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
                RelativeBound::Start(_) => {
                    self.layer = self
                        .layer
                        .checked_add(1)
                        .expect("The number of active layers overflowed when using `RelativeUniteBoundsIter`");

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
                RelativeBound::End(next_end) => {
                    self.layer = self.layer.checked_sub(1).expect(
                        "An error occurred with `RelativeUniteBoundsIter`: The number of active layers underflowed, \
                         which is unexpected",
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

impl<I> FusedIterator for RelativeUnitedBoundsIter<Peekable<I>> where I: Iterator<Item = RelativeBound> {}

fn is_rel_end_bound_adjacent_to_rel_peeked(end: &RelativeEndBound, peeked: &RelativeBound) -> bool {
    let RelativeBound::Start(peeked_start) = peeked else {
        return false;
    };

    matches!(
        end.bound_partial_cmp(peeked_start)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        Ordering::Equal,
    )
}

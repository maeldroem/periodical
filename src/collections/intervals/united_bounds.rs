//! United bounds iterators

use std::cmp::Ordering;
use std::iter::{FusedIterator, Peekable};

use crate::collections::intervals::layered_bounds::{LayeredAbsoluteBounds, LayeredRelativeBounds};
use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound};
use crate::intervals::ops::bound_ord::PartialBoundOrd;
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
use crate::intervals::relative::{RelativeBound, RelativeEndBound};

/// Iterator for uniting an iterator of sorted and paired [`AbsoluteBound`]s
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
    /// The bounds given to the iterator **must be sorted chronologically** in order for the uniting process to work.
    /// The responsibility of sorting the input is left to the caller in order to prevent double-sorting.
    ///
    /// The bounds given to the iterator **must be paired**, that means there should be an equal amount of
    /// [`Start`](AbsoluteBound::Start)s and [`End`](AbsoluteBound::End)s.
    /// This is automatically guaranteed if they are obtained from
    /// [intervals](crate::intervals::absolute::AbsoluteInterval)
    /// or from [paired bounds](crate::intervals::absolute::AbsoluteBounds).
    #[must_use]
    pub fn new(iter: I) -> AbsoluteUnitedBoundsIter<Peekable<I>> {
        // Add debug assertion on iter being sorted
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
    /// The given other [`AbsoluteUnitedBoundsIter`] acts at the second layer in the resulting
    /// [`LayeredAbsoluteBounds`].
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
                    // ACK: Yes, this will panic if we reach u64's limit
                    self.layer += 1;

                    if self.is_next_start_adjacent {
                        self.is_next_start_adjacent = false;
                        continue;
                    }

                    // Since we already incremented the layer, the first counted start bound must be on layer 1
                    // i.e. we were on the bottom layer (0) and it just was incremented to 1.
                    // This technically also guards against start bounds that, after incrementing, remain
                    // on layer 0, but this impossible as it would required going in the negatives
                    // (and since we are using an unsigned number, you see where this is going)
                    if self.layer > 1 {
                        continue;
                    }
                },
                AbsoluteBound::End(next_end) => {
                    // ACK: Yes, this will panic if it attempts to go below 0
                    self.layer -= 1;

                    // Since we already decremented the layer, the last counted end bound must be on layer 0
                    // i.e. we were on the first layer (1) and it just was decremented to 0.
                    if self.layer > 0 {
                        continue;
                    }

                    // If the peeked value is a start bound that is adjacent to the current bound,
                    // we don't return this end bound. Since the layer decrement already happened and we know it's
                    // gonna be incremented again, we know that the layer will end up at 1, which is problematic
                    // as it would be a layer number that makes the start bound considered as the first start bound
                    // of a new interval.
                    // In order to solve this, we set a variable that will tell the iterator to skip the next
                    // start bound, like this end (and the following start) never happened.
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
            inner_size_hint.1.map(|x| x.saturating_mul(2)),
        )
    }
}

impl<I> FusedIterator for AbsoluteUnitedBoundsIter<Peekable<I>> where I: Iterator<Item = AbsoluteBound> {}

fn is_abs_end_bound_adjacent_to_abs_peeked(end: &AbsoluteEndBound, peeked: &AbsoluteBound) -> bool {
    let AbsoluteBound::Start(peeked_start) = peeked else {
        return false;
    };

    matches!(
        end.bound_cmp(peeked_start)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        Ordering::Equal,
    )
}

/// Iterator for uniting an iterator of sorted and paired [`AbsoluteBound`]s
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
    /// The bounds given to the iterator **must be sorted chronologically** in order for the uniting process to work.
    /// The responsibility of sorting the input is left to the caller in order to prevent double-sorting.
    ///
    /// The bounds given to the iterator **must be paired**, that means there should be an equal amount of
    /// [`Start`](RelativeBound::Start)s and [`End`](RelativeBound::End)s.
    /// This is automatically guaranteed if they are obtained from
    /// [intervals](crate::intervals::relative::RelativeInterval)
    /// or from [paired bounds](crate::intervals::relative::RelativeBounds).
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
    /// The given other [`RelativeUnitedBoundsIter`] acts at the second layer in the resulting
    /// [`LayeredRelativeBounds`].
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
                    // ACK: Yes, this will panic if we reach u64's limit
                    self.layer += 1;

                    if self.is_next_start_adjacent {
                        self.is_next_start_adjacent = false;
                        continue;
                    }

                    // Since we already incremented the layer, the first counted start bound must be on layer 1
                    // i.e. we were on the bottom layer (0) and it just was incremented to 1.
                    // This technically also guards against start bounds that, after incrementing, remain
                    // on layer 0, but this impossible as it would required going in the negatives
                    // (and since we are using an unsigned number, you see where this is going)
                    if self.layer > 1 {
                        continue;
                    }
                },
                RelativeBound::End(next_end) => {
                    // ACK: Yes, this will panic if it attempts to go below 0
                    self.layer -= 1;

                    // Since we already decremented the layer, the last counted end bound must be on layer 0
                    // i.e. we were on the first layer (1) and it just was decremented to 0.
                    if self.layer > 0 {
                        continue;
                    }

                    // If the peeked value is a start bound that is adjacent to the current bound,
                    // we don't return this end bound. Since the layer decrement already happened and we know it's
                    // gonna be incremented again, we know that the layer will end up at 1, which is problematic
                    // as it would be a layer number that makes the start bound considered as the first start bound
                    // of a new interval.
                    // In order to solve this, we set a variable that will tell the iterator to skip the next
                    // start bound, like this end (and the following start) never happened.
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
            inner_size_hint.1.map(|x| x.saturating_mul(2)),
        )
    }
}

impl<I> FusedIterator for RelativeUnitedBoundsIter<Peekable<I>> where I: Iterator<Item = RelativeBound> {}

fn is_rel_end_bound_adjacent_to_rel_peeked(end: &RelativeEndBound, peeked: &RelativeBound) -> bool {
    let RelativeBound::Start(peeked_start) = peeked else {
        return false;
    };

    matches!(
        end.bound_cmp(peeked_start)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        Ordering::Equal,
    )
}

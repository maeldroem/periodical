//! United bounds iterators
//!
//! Wraps around [the _normal_ bounds iterators](crate::collections::intervals::bounds) but flattens the iterators
//! so that the returned bounds are non-overlapping.

use std::iter::{FusedIterator, Peekable};

use crate::collections::intervals::bounds::{AbsoluteBoundsIter, RelativeBoundsIter};
use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::meta::HasBoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{RelativeBound, RelativeEndBound, RelativeStartBound};

/// Iterator uniting the bounds of [`AbsoluteBoundsIter`]
pub struct AbsoluteUnitedBoundsIter {
    iter: Peekable<AbsoluteBoundsIter>,
    overlap_count: u64,
    exhausted: bool,
}

impl AbsoluteUnitedBoundsIter {
    #[must_use]
    pub fn new(iter: AbsoluteBoundsIter) -> Self {
        AbsoluteUnitedBoundsIter {
            iter: iter.peekable(),
            overlap_count: 0,
            exhausted: false,
        }
    }
}

impl Iterator for AbsoluteUnitedBoundsIter {
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
                AbsoluteBound::Start(_) => self.overlap_count += 1,
                AbsoluteBound::End(_) => self.overlap_count -= 1,
            }

            if self.overlap_count != 1 {
                continue;
            }

            if let AbsoluteBound::End(next_end) = next
                && self.iter.peek().is_some_and(|peeked| {
                    if let AbsoluteBound::Start(peeked_start) = peeked
                        && let (AbsoluteEndBound::Finite(finite_end), AbsoluteStartBound::Finite(finite_start)) =
                            (next_end, peeked_start)
                        && finite_end == *finite_start
                    {
                        let disambiguated_bound_overlap =
                            BoundOverlapAmbiguity::EndStart(finite_end.inclusivity(), finite_start.inclusivity())
                                .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient);

                        return matches!(disambiguated_bound_overlap, DisambiguatedBoundOverlap::Equal);
                    }

                    false
                })
            {
                // Since the peeked value is a start bound that can be merged with our current "interval",
                // we skip over it by calling `next()` here (preventing `self.overlap_count` from
                // being incremented) and continuing the loop, like we didn't reach the end (which we actually
                // didn't since the current end bound and next start bound are being merged)
                self.iter.next();
                continue;
            }

            return Some(next);
        }
    }
}

impl FusedIterator for AbsoluteUnitedBoundsIter {}

/// Iterator uniting the bounds of [`RelativeBoundsIter`]
pub struct RelativeUnitedBoundsIter {
    iter: Peekable<RelativeBoundsIter>,
    overlap_count: u64,
    exhausted: bool,
}

impl RelativeUnitedBoundsIter {
    #[must_use]
    pub fn new(iter: RelativeBoundsIter) -> Self {
        RelativeUnitedBoundsIter {
            iter: iter.peekable(),
            overlap_count: 0,
            exhausted: false,
        }
    }
}

impl Iterator for RelativeUnitedBoundsIter {
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
                RelativeBound::Start(_) => self.overlap_count += 1,
                RelativeBound::End(_) => self.overlap_count -= 1,
            }

            if self.overlap_count != 1 {
                continue;
            }

            if let RelativeBound::End(next_end) = next
                && self.iter.peek().is_some_and(|peeked| {
                    if let RelativeBound::Start(peeked_start) = peeked
                        && let (RelativeEndBound::Finite(finite_end), RelativeStartBound::Finite(finite_start)) =
                            (next_end, peeked_start)
                        && finite_end == *finite_start
                    {
                        let disambiguated_bound_overlap =
                            BoundOverlapAmbiguity::EndStart(finite_end.inclusivity(), finite_start.inclusivity())
                                .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient);

                        return matches!(disambiguated_bound_overlap, DisambiguatedBoundOverlap::Equal);
                    }

                    false
                })
            {
                // Since the peeked value is a start bound that can be merged with our current "interval",
                // we skip over it by calling `next()` here (preventing `self.overlap_count` from
                // being incremented) and continuing the loop, like we didn't reach the end (which we actually
                // didn't since the current end bound and next start bound are being merged)
                self.iter.next();
                continue;
            }

            return Some(next);
        }
    }
}

impl FusedIterator for RelativeUnitedBoundsIter {}

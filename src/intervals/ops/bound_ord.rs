//! [Partial ordering](PartialOrd) for bounds with [bound overlap ambiguity](BoundOverlapAmbiguity)
//! information on equality

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;

use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{RelativeBound, RelativeEndBound, RelativeStartBound};

use super::prelude::*;

/// [`Ordering`] for bounds, with [`BoundOverlapAmbiguity`] provided when equal in time/offset
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum BoundOrdering {
    Less,
    Equal(Option<BoundOverlapAmbiguity>),
    Greater,
}

impl BoundOrdering {
    /// Transforms the [`BoundOrdering`] to an [`Ordering`] by stripping the additional info
    #[must_use]
    pub fn strip(self) -> Ordering {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(_) => Ordering::Equal,
            Self::Greater => Ordering::Greater,
        }
    }

    /// Disambiguates a [`BoundOrdering`] to an [`Ordering`] using [`BoundOverlapDisambiguationRuleSet`]
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: BoundOverlapDisambiguationRuleSet) -> Ordering {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(None) => Ordering::Equal,
            Self::Equal(Some(ambiguity)) => match ambiguity.disambiguate_using_rule_set(rule_set) {
                DisambiguatedBoundOverlap::Before => Ordering::Greater,
                DisambiguatedBoundOverlap::Equal => Ordering::Equal,
                DisambiguatedBoundOverlap::After => Ordering::Less,
            },
            Self::Greater => Ordering::Greater,
        }
    }

    /// Disambiguates a [`BoundOrdering`] to an [`Ordering`] using the given closure to disambiguate equality ambiguity
    #[must_use]
    pub fn disambiguate_using<F>(self, f: F) -> Ordering
    where
        F: FnOnce(BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap,
    {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(None) => Ordering::Equal,
            Self::Equal(Some(ambiguity)) => match ambiguity.disambiguate_using(f) {
                DisambiguatedBoundOverlap::Before => Ordering::Greater,
                DisambiguatedBoundOverlap::Equal => Ordering::Equal,
                DisambiguatedBoundOverlap::After => Ordering::Less,
            },
            Self::Greater => Ordering::Greater,
        }
    }
}

/// [Partial ordering](PartialOrd) trait with [bound overlap ambiguity](BoundOverlapAmbiguity) information on equality
pub trait PartialBoundOrd<Rhs = Self> {
    /// Compares two bounds
    #[must_use]
    fn bound_cmp(&self, other: &Rhs) -> BoundOrdering;

    /// Returns whether the current bound is lesser than the other
    #[must_use]
    fn bound_lt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::After,
                )
            },
            BoundOrdering::Equal(None) | BoundOrdering::Greater => false,
        }
    }

    /// Returns whether the current bound is less than or equal to the other
    #[must_use]
    fn bound_le(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less | BoundOrdering::Equal(None) => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::Equal | DisambiguatedBoundOverlap::After,
                )
            },
            BoundOrdering::Greater => false,
        }
    }

    /// Returns whether the current bound is greater than the other
    #[must_use]
    fn bound_gt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::Before,
                )
            },
            BoundOrdering::Equal(None) | BoundOrdering::Greater => false,
        }
    }

    /// Returns whether the current bound is greater than or equal to the other
    #[must_use]
    fn bound_ge(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less | BoundOrdering::Equal(None) => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::Before | DisambiguatedBoundOverlap::Equal,
                )
            },
            BoundOrdering::Greater => false,
        }
    }
}

impl PartialBoundOrd for AbsoluteStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (AbsoluteStartBound::Finite(finite_og), AbsoluteStartBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (AbsoluteStartBound::Finite(_), AbsoluteStartBound::InfinitePast) => BoundOrdering::Greater,
            (AbsoluteStartBound::InfinitePast, AbsoluteStartBound::Finite(_)) => BoundOrdering::Less,
            (AbsoluteStartBound::InfinitePast, AbsoluteStartBound::InfinitePast) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<AbsoluteEndBound> for AbsoluteStartBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        match (self, other) {
            (AbsoluteStartBound::Finite(finite_og), AbsoluteEndBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Less,
        }
    }
}

impl PartialBoundOrd<AbsoluteBound> for AbsoluteStartBound {
    fn bound_cmp(&self, other: &AbsoluteBound) -> BoundOrdering {
        match other {
            AbsoluteBound::Start(other_start) => self.bound_cmp(other_start),
            AbsoluteBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for AbsoluteEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (AbsoluteEndBound::Finite(finite_og), AbsoluteEndBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (AbsoluteEndBound::Finite(_), AbsoluteEndBound::InfiniteFuture) => BoundOrdering::Less,
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::Finite(_)) => BoundOrdering::Greater,
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::InfiniteFuture) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<AbsoluteStartBound> for AbsoluteEndBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        match (self, other) {
            (AbsoluteEndBound::Finite(finite_og), AbsoluteStartBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Greater,
        }
    }
}

impl PartialBoundOrd<AbsoluteBound> for AbsoluteEndBound {
    fn bound_cmp(&self, other: &AbsoluteBound) -> BoundOrdering {
        match other {
            AbsoluteBound::Start(other_start) => self.bound_cmp(other_start),
            AbsoluteBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for AbsoluteBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (AbsoluteBound::Start(og_start), AbsoluteBound::Start(other_start)) => og_start.bound_cmp(other_start),
            (AbsoluteBound::Start(og_start), AbsoluteBound::End(other_end)) => og_start.bound_cmp(other_end),
            (AbsoluteBound::End(og_end), AbsoluteBound::Start(other_start)) => og_end.bound_cmp(other_start),
            (AbsoluteBound::End(og_end), AbsoluteBound::End(other_end)) => og_end.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd<AbsoluteStartBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        match self {
            AbsoluteBound::Start(og_start) => og_start.bound_cmp(other),
            AbsoluteBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

impl PartialBoundOrd<AbsoluteEndBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        match self {
            AbsoluteBound::Start(og_start) => og_start.bound_cmp(other),
            AbsoluteBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

impl PartialBoundOrd for RelativeStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (RelativeStartBound::Finite(finite_og), RelativeStartBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (RelativeStartBound::Finite(_), RelativeStartBound::InfinitePast) => BoundOrdering::Greater,
            (RelativeStartBound::InfinitePast, RelativeStartBound::Finite(_)) => BoundOrdering::Less,
            (RelativeStartBound::InfinitePast, RelativeStartBound::InfinitePast) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<RelativeEndBound> for RelativeStartBound {
    fn bound_cmp(&self, other: &RelativeEndBound) -> BoundOrdering {
        match (self, other) {
            (RelativeStartBound::Finite(finite_og), RelativeEndBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Less,
        }
    }
}

impl PartialBoundOrd<RelativeBound> for RelativeStartBound {
    fn bound_cmp(&self, other: &RelativeBound) -> BoundOrdering {
        match other {
            RelativeBound::Start(other_start) => self.bound_cmp(other_start),
            RelativeBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for RelativeEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (RelativeEndBound::Finite(finite_og), RelativeEndBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (RelativeEndBound::Finite(_), RelativeEndBound::InfiniteFuture) => BoundOrdering::Less,
            (RelativeEndBound::InfiniteFuture, RelativeEndBound::Finite(_)) => BoundOrdering::Greater,
            (RelativeEndBound::InfiniteFuture, RelativeEndBound::InfiniteFuture) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<RelativeStartBound> for RelativeEndBound {
    fn bound_cmp(&self, other: &RelativeStartBound) -> BoundOrdering {
        match (self, other) {
            (RelativeEndBound::Finite(finite_og), RelativeStartBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                        finite_og.inclusivity(),
                        finite_other.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Greater,
        }
    }
}

impl PartialBoundOrd<RelativeBound> for RelativeEndBound {
    fn bound_cmp(&self, other: &RelativeBound) -> BoundOrdering {
        match other {
            RelativeBound::Start(other_start) => self.bound_cmp(other_start),
            RelativeBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for RelativeBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (RelativeBound::Start(og_start), RelativeBound::Start(other_start)) => og_start.bound_cmp(other_start),
            (RelativeBound::Start(og_start), RelativeBound::End(other_end)) => og_start.bound_cmp(other_end),
            (RelativeBound::End(og_end), RelativeBound::Start(other_start)) => og_end.bound_cmp(other_start),
            (RelativeBound::End(og_end), RelativeBound::End(other_end)) => og_end.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd<RelativeStartBound> for RelativeBound {
    fn bound_cmp(&self, other: &RelativeStartBound) -> BoundOrdering {
        match self {
            RelativeBound::Start(og_start) => og_start.bound_cmp(other),
            RelativeBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

impl PartialBoundOrd<RelativeEndBound> for RelativeBound {
    fn bound_cmp(&self, other: &RelativeEndBound) -> BoundOrdering {
        match self {
            RelativeBound::Start(og_start) => og_start.bound_cmp(other),
            RelativeBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

//! Absolute finite end bound
//!
//! Represents the finite end bound of an absolute interval.
//! If you need to represent infinity, see [`AbsoluteEndBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteFiniteStartBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{
    BoundEq,
    BoundOrd,
    BoundOrdExtremaOps,
    BoundOrdering,
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteFiniteEndBound(pub(crate) AbsoluteFiniteBoundPosition);

impl AbsoluteFiniteEndBound {
    pub fn new(finite_bound_pos: AbsoluteFiniteBoundPosition) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> AbsoluteFiniteBoundPosition {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut AbsoluteFiniteBoundPosition {
        &mut self.0
    }

    pub fn to_end_bound(self) -> AbsoluteEndBound {
        AbsoluteEndBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> AbsoluteFiniteBound {
        AbsoluteFiniteBound::from(self)
    }

    pub fn to_bound(self) -> AbsoluteBound {
        AbsoluteBound::from(self)
    }

    pub fn opposite(self) -> AbsoluteFiniteStartBound {
        AbsoluteFiniteStartBound::new(AbsoluteFiniteBoundPosition::new_with_inclusivity(
            self.pos().time(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for AbsoluteFiniteEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteFiniteEndBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.pos()
            .cmp(&other.pos())
            .then_with(|| match (self.pos().inclusivity(), other.pos().inclusivity()) {
                (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Greater,
                (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Less,
            })
    }
}

impl BoundEq for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.eq(other)
            && BoundOverlapAmbiguity::BothEnds(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<AbsoluteEndBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_end| self.bound_eq(&finite_end, rule_set))
    }
}

impl BoundEq<AbsoluteFiniteStartBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.pos().eq(&other.pos())
            && BoundOverlapAmbiguity::EndStart(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<AbsoluteStartBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_start| self.bound_eq(&finite_start, rule_set))
    }
}

impl BoundEq<AbsoluteFiniteBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            AbsoluteFiniteBound::Start(finite_start) => self.bound_eq(finite_start, rule_set),
            AbsoluteFiniteBound::End(finite_end) => self.bound_eq(finite_end, rule_set),
        }
    }
}

impl BoundEq<AbsoluteBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            AbsoluteBound::Start(start) => self.bound_eq(start, rule_set),
            AbsoluteBound::End(end) => self.bound_eq(end, rule_set),
        }
    }
}

impl BoundOrd for AbsoluteFiniteEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match self.pos().cmp(&other.pos()) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                self.pos().inclusivity(),
                other.pos().inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrdExtremaOps for AbsoluteFiniteEndBound {}

impl BoundOrd<AbsoluteEndBound> for AbsoluteFiniteEndBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        if let Some(finite_end) = other.finite() {
            self.bound_cmp(&finite_end)
        } else {
            BoundOrdering::Less
        }
    }
}

impl BoundOrd<AbsoluteFiniteStartBound> for AbsoluteFiniteEndBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteStartBound) -> BoundOrdering {
        match self.pos().cmp(&other.pos()) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                self.pos().inclusivity(),
                other.pos().inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<AbsoluteStartBound> for AbsoluteFiniteEndBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        match other {
            AbsoluteStartBound::Finite(finite_end) => self.bound_cmp(finite_end),
            AbsoluteStartBound::InfinitePast => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<AbsoluteFiniteBound> for AbsoluteFiniteEndBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteBound) -> BoundOrdering {
        match other {
            AbsoluteFiniteBound::Start(finite_start) => self.bound_cmp(finite_start),
            AbsoluteFiniteBound::End(finite_end) => self.bound_cmp(finite_end),
        }
    }
}

impl BoundOrd<AbsoluteBound> for AbsoluteFiniteEndBound {
    fn bound_cmp(&self, other: &AbsoluteBound) -> BoundOrdering {
        match other {
            AbsoluteBound::Start(start) => self.bound_cmp(start),
            AbsoluteBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<AbsoluteFiniteBoundPosition> for AbsoluteFiniteEndBound {
    fn from(value: AbsoluteFiniteBoundPosition) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

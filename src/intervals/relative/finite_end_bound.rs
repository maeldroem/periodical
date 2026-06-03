//! Relative finite end bound
//!
//! Represents the finite end bound of an relative interval.
//! If you need to represent infinity, see [`RelEndBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{
    BoundEq,
    BoundOrd,
    BoundOrdExtremaOps,
    BoundOrdering,
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
};
use crate::intervals::relative::{
    RelBound,
    RelEndBound,
    RelFiniteBound,
    RelFiniteBoundPos,
    RelFiniteStartBound,
    RelStartBound,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelFiniteEndBound(pub(crate) RelFiniteBoundPos);

impl RelFiniteEndBound {
    pub fn new(finite_bound_pos: RelFiniteBoundPos) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> RelFiniteBoundPos {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut RelFiniteBoundPos {
        &mut self.0
    }

    pub fn to_end_bound(self) -> RelEndBound {
        RelEndBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> RelFiniteBound {
        RelFiniteBound::from(self)
    }

    pub fn to_bound(self) -> RelBound {
        RelBound::from(self)
    }

    pub fn opposite(self) -> RelFiniteStartBound {
        RelFiniteStartBound::new(RelFiniteBoundPos::new_with_inclusivity(
            self.pos().offset(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for RelFiniteEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelFiniteEndBound {
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

impl BoundEq for RelFiniteEndBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.eq(other)
            && BoundOverlapAmbiguity::BothEnds(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<RelEndBound> for RelFiniteEndBound {
    fn bound_eq(&self, other: &RelEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_end| self.bound_eq(&finite_end, rule_set))
    }
}

impl BoundEq<RelFiniteStartBound> for RelFiniteEndBound {
    fn bound_eq(&self, other: &RelFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.pos().eq(&other.pos())
            && BoundOverlapAmbiguity::EndStart(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<RelStartBound> for RelFiniteEndBound {
    fn bound_eq(&self, other: &RelStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_start| self.bound_eq(&finite_start, rule_set))
    }
}

impl BoundEq<RelFiniteBound> for RelFiniteEndBound {
    fn bound_eq(&self, other: &RelFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            RelFiniteBound::Start(finite_start) => self.bound_eq(finite_start, rule_set),
            RelFiniteBound::End(finite_end) => self.bound_eq(finite_end, rule_set),
        }
    }
}

impl BoundEq<RelBound> for RelFiniteEndBound {
    fn bound_eq(&self, other: &RelBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            RelBound::Start(start) => self.bound_eq(start, rule_set),
            RelBound::End(end) => self.bound_eq(end, rule_set),
        }
    }
}

impl BoundOrd for RelFiniteEndBound {
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

impl BoundOrdExtremaOps for RelFiniteEndBound {}

impl BoundOrd<RelEndBound> for RelFiniteEndBound {
    fn bound_cmp(&self, other: &RelEndBound) -> BoundOrdering {
        if let Some(finite_end) = other.finite() {
            self.bound_cmp(&finite_end)
        } else {
            BoundOrdering::Less
        }
    }
}

impl BoundOrd<RelFiniteStartBound> for RelFiniteEndBound {
    fn bound_cmp(&self, other: &RelFiniteStartBound) -> BoundOrdering {
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

impl BoundOrd<RelStartBound> for RelFiniteEndBound {
    fn bound_cmp(&self, other: &RelStartBound) -> BoundOrdering {
        match other {
            RelStartBound::Finite(finite_end) => self.bound_cmp(finite_end),
            RelStartBound::InfinitePast => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<RelFiniteBound> for RelFiniteEndBound {
    fn bound_cmp(&self, other: &RelFiniteBound) -> BoundOrdering {
        match other {
            RelFiniteBound::Start(finite_start) => self.bound_cmp(finite_start),
            RelFiniteBound::End(finite_end) => self.bound_cmp(finite_end),
        }
    }
}

impl BoundOrd<RelBound> for RelFiniteEndBound {
    fn bound_cmp(&self, other: &RelBound) -> BoundOrdering {
        match other {
            RelBound::Start(start) => self.bound_cmp(start),
            RelBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<RelFiniteBoundPos> for RelFiniteEndBound {
    fn from(value: RelFiniteBoundPos) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

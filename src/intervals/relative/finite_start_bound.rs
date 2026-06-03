//! Relative finite start bound
//!
//! Represents the finite start bound of an relative interval.
//! If you need to represent infinity, see [`RelStartBound`].

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
    RelFiniteEndBound,
    RelStartBound,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelFiniteStartBound(pub(crate) RelFiniteBoundPos);

impl RelFiniteStartBound {
    pub fn new(finite_bound_pos: RelFiniteBoundPos) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> RelFiniteBoundPos {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut RelFiniteBoundPos {
        &mut self.0
    }

    pub fn to_start_bound(self) -> RelStartBound {
        RelStartBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> RelFiniteBound {
        RelFiniteBound::from(self)
    }

    pub fn to_bound(self) -> RelBound {
        RelBound::from(self)
    }

    pub fn opposite(self) -> RelFiniteEndBound {
        RelFiniteEndBound::new(RelFiniteBoundPos::new_with_inclusivity(
            self.pos().offset(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for RelFiniteStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelFiniteStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.pos()
            .cmp(&other.pos())
            .then_with(|| match (self.pos().inclusivity(), other.pos().inclusivity()) {
                (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Less,
                (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Greater,
            })
    }
}

impl BoundEq for RelFiniteStartBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.eq(other)
            && BoundOverlapAmbiguity::BothStarts(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<RelStartBound> for RelFiniteStartBound {
    fn bound_eq(&self, other: &RelStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_start| self.bound_eq(&finite_start, rule_set))
    }
}

impl BoundEq<RelFiniteEndBound> for RelFiniteStartBound {
    fn bound_eq(&self, other: &RelFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.pos().eq(&other.pos())
            && BoundOverlapAmbiguity::StartEnd(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<RelEndBound> for RelFiniteStartBound {
    fn bound_eq(&self, other: &RelEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_end| self.bound_eq(&finite_end, rule_set))
    }
}

impl BoundEq<RelFiniteBound> for RelFiniteStartBound {
    fn bound_eq(&self, other: &RelFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            RelFiniteBound::Start(finite_start) => self.bound_eq(finite_start, rule_set),
            RelFiniteBound::End(finite_end) => self.bound_eq(finite_end, rule_set),
        }
    }
}

impl BoundEq<RelBound> for RelFiniteStartBound {
    fn bound_eq(&self, other: &RelBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            RelBound::Start(start) => self.bound_eq(start, rule_set),
            RelBound::End(end) => self.bound_eq(end, rule_set),
        }
    }
}

impl BoundOrd for RelFiniteStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match self.pos().cmp(&other.pos()) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                self.pos().inclusivity(),
                other.pos().inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrdExtremaOps for RelFiniteStartBound {}

impl BoundOrd<RelStartBound> for RelFiniteStartBound {
    fn bound_cmp(&self, other: &RelStartBound) -> BoundOrdering {
        if let Some(finite_start) = other.finite() {
            self.bound_cmp(&finite_start)
        } else {
            BoundOrdering::Greater
        }
    }
}

impl BoundOrd<RelFiniteEndBound> for RelFiniteStartBound {
    fn bound_cmp(&self, other: &RelFiniteEndBound) -> BoundOrdering {
        match self.pos().cmp(&other.pos()) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                self.pos().inclusivity(),
                other.pos().inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<RelEndBound> for RelFiniteStartBound {
    fn bound_cmp(&self, other: &RelEndBound) -> BoundOrdering {
        match other {
            RelEndBound::Finite(finite_end) => self.bound_cmp(finite_end),
            RelEndBound::InfiniteFuture => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<RelFiniteBound> for RelFiniteStartBound {
    fn bound_cmp(&self, other: &RelFiniteBound) -> BoundOrdering {
        match other {
            RelFiniteBound::Start(finite_start) => self.bound_cmp(finite_start),
            RelFiniteBound::End(finite_end) => self.bound_cmp(finite_end),
        }
    }
}

impl BoundOrd<RelBound> for RelFiniteStartBound {
    fn bound_cmp(&self, other: &RelBound) -> BoundOrdering {
        match other {
            RelBound::Start(start) => self.bound_cmp(start),
            RelBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<RelFiniteBoundPos> for RelFiniteStartBound {
    fn from(value: RelFiniteBoundPos) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

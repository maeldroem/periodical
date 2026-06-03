//! Absolute finite start bound
//!
//! Represents the finite start bound of an absolute interval.
//! If you need to represent infinity, see [`AbsStartBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBound,
    AbsEndBound,
    AbsFiniteBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsStartBound,
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
pub struct AbsFiniteStartBound(pub(crate) AbsFiniteBoundPos);

impl AbsFiniteStartBound {
    pub fn new(finite_bound_pos: AbsFiniteBoundPos) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> AbsFiniteBoundPos {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut AbsFiniteBoundPos {
        &mut self.0
    }

    pub fn to_start_bound(self) -> AbsStartBound {
        AbsStartBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> AbsFiniteBound {
        AbsFiniteBound::from(self)
    }

    pub fn to_bound(self) -> AbsBound {
        AbsBound::from(self)
    }

    pub fn opposite(self) -> AbsFiniteEndBound {
        AbsFiniteEndBound::new(AbsFiniteBoundPos::new_with_incl(
            self.pos().time(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for AbsFiniteStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsFiniteStartBound {
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

impl BoundEq for AbsFiniteStartBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.eq(other)
            && BoundOverlapAmbiguity::BothStarts(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<AbsStartBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_start| self.bound_eq(&finite_start, rule_set))
    }
}

impl BoundEq<AbsFiniteEndBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.pos().eq(&other.pos())
            && BoundOverlapAmbiguity::StartEnd(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<AbsEndBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_end| self.bound_eq(&finite_end, rule_set))
    }
}

impl BoundEq<AbsFiniteBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            AbsFiniteBound::Start(finite_start) => self.bound_eq(finite_start, rule_set),
            AbsFiniteBound::End(finite_end) => self.bound_eq(finite_end, rule_set),
        }
    }
}

impl BoundEq<AbsBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            AbsBound::Start(start) => self.bound_eq(start, rule_set),
            AbsBound::End(end) => self.bound_eq(end, rule_set),
        }
    }
}

impl BoundOrd for AbsFiniteStartBound {
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

impl BoundOrdExtremaOps for AbsFiniteStartBound {}

impl BoundOrd<AbsStartBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsStartBound) -> BoundOrdering {
        if let Some(finite_start) = other.finite() {
            self.bound_cmp(&finite_start)
        } else {
            BoundOrdering::Greater
        }
    }
}

impl BoundOrd<AbsFiniteEndBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsFiniteEndBound) -> BoundOrdering {
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

impl BoundOrd<AbsEndBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsEndBound) -> BoundOrdering {
        match other {
            AbsEndBound::Finite(finite_end) => self.bound_cmp(finite_end),
            AbsEndBound::InfiniteFuture => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<AbsFiniteBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsFiniteBound) -> BoundOrdering {
        match other {
            AbsFiniteBound::Start(finite_start) => self.bound_cmp(finite_start),
            AbsFiniteBound::End(finite_end) => self.bound_cmp(finite_end),
        }
    }
}

impl BoundOrd<AbsBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsBound) -> BoundOrdering {
        match other {
            AbsBound::Start(start) => self.bound_cmp(start),
            AbsBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<AbsFiniteBoundPos> for AbsFiniteStartBound {
    fn from(value: AbsFiniteBoundPos) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

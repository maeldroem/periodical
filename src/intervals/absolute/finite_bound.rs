//! Absolute finite bound representation
//!
//! Represents an absolute finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing absolute bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::absolute::{
    AbsBound,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
    AbsStartBound,
};
use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsFiniteBound {
    Start(AbsFiniteStartBound),
    End(AbsFiniteEndBound),
}

impl AbsFiniteBound {
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    pub fn start(self) -> Option<AbsFiniteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    pub fn end(self) -> Option<AbsFiniteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    pub fn pos(self) -> AbsFiniteBoundPos {
        match self {
            Self::Start(start) => start.pos(),
            Self::End(end) => end.pos(),
        }
    }

    pub fn opposite(self) -> Self {
        match self {
            Self::Start(start) => Self::End(start.opposite()),
            Self::End(end) => Self::Start(end.opposite()),
        }
    }

    pub fn to_bound(self) -> AbsBound {
        AbsBound::from(self)
    }
}

impl HasBoundExtremality for AbsFiniteBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for AbsFiniteBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsFiniteStartBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsFiniteEndBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsStartBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsEndBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for AbsFiniteBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::Start(lhs_finite_start), Self::Start(rhs_finite_start)) => {
                lhs_finite_start.bound_cmp(rhs_finite_start)
            },
            (Self::Start(finite_start), Self::End(finite_end)) => finite_start.bound_cmp(finite_end),
            (Self::End(finite_end), Self::Start(finite_start)) => finite_end.bound_cmp(finite_start),
            (Self::End(lhs_finite_end), Self::End(rhs_finite_end)) => lhs_finite_end.bound_cmp(rhs_finite_end),
        }
    }
}

impl BoundOrdExtremaOps for AbsFiniteBound {}

impl BoundOrd<AbsFiniteStartBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsFiniteEndBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsStartBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsEndBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl From<AbsFiniteStartBound> for AbsFiniteBound {
    fn from(value: AbsFiniteStartBound) -> Self {
        Self::Start(value)
    }
}

impl From<AbsFiniteEndBound> for AbsFiniteBound {
    fn from(value: AbsFiniteEndBound) -> Self {
        Self::End(value)
    }
}

impl From<(AbsFiniteBoundPos, BoundExtremality)> for AbsFiniteBound {
    fn from((finite_pos, extremality): (AbsFiniteBoundPos, BoundExtremality)) -> Self {
        match extremality {
            BoundExtremality::Start => Self::Start(AbsFiniteStartBound::from(finite_pos)),
            BoundExtremality::End => Self::End(AbsFiniteEndBound::from(finite_pos)),
        }
    }
}

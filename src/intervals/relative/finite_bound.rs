//! Relative finite bound representation
//!
//! Represents an relative finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    RelBound,
    RelEndBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelFiniteStartBound,
    RelStartBound,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelFiniteBound {
    Start(RelFiniteStartBound),
    End(RelFiniteEndBound),
}

impl RelFiniteBound {
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    pub fn start(self) -> Option<RelFiniteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    pub fn end(self) -> Option<RelFiniteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    pub fn pos(self) -> RelFiniteBoundPos {
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

    pub fn to_bound(self) -> RelBound {
        RelBound::from(self)
    }
}

impl HasBoundExtremality for RelFiniteBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for RelFiniteBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelFiniteStartBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelFiniteEndBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelStartBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelEndBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for RelFiniteBound {
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

impl BoundOrdExtremaOps for RelFiniteBound {}

impl BoundOrd<RelFiniteStartBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelFiniteEndBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelStartBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelEndBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl From<RelFiniteStartBound> for RelFiniteBound {
    fn from(value: RelFiniteStartBound) -> Self {
        Self::Start(value)
    }
}

impl From<RelFiniteEndBound> for RelFiniteBound {
    fn from(value: RelFiniteEndBound) -> Self {
        Self::End(value)
    }
}

impl From<(RelFiniteBoundPos, BoundExtremality)> for RelFiniteBound {
    fn from((finite_pos, extremality): (RelFiniteBoundPos, BoundExtremality)) -> Self {
        match extremality {
            BoundExtremality::Start => Self::Start(RelFiniteStartBound::from(finite_pos)),
            BoundExtremality::End => Self::End(RelFiniteEndBound::from(finite_pos)),
        }
    }
}

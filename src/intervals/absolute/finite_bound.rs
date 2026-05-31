//! Absolute finite bound representation
//!
//! Represents an absolute finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing absolute bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteFiniteEndBound,
    AbsoluteFiniteStartBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteFiniteBound {
    Start(AbsoluteFiniteStartBound),
    End(AbsoluteFiniteEndBound),
}

impl AbsoluteFiniteBound {
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    pub fn start(self) -> Option<AbsoluteFiniteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    pub fn end(self) -> Option<AbsoluteFiniteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    pub fn pos(self) -> AbsoluteFiniteBoundPosition {
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

    pub fn to_bound(self) -> AbsoluteBound {
        AbsoluteBound::from(self)
    }
}

impl HasBoundExtremality for AbsoluteFiniteBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteFiniteStartBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteFiniteEndBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteStartBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteEndBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for AbsoluteFiniteBound {
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

impl BoundOrdExtremaOps for AbsoluteFiniteBound {}

impl BoundOrd<AbsoluteFiniteStartBound> for AbsoluteFiniteBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteFiniteEndBound> for AbsoluteFiniteBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteStartBound> for AbsoluteFiniteBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteEndBound> for AbsoluteFiniteBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteBound> for AbsoluteFiniteBound {
    fn bound_cmp(&self, other: &AbsoluteBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl From<AbsoluteFiniteStartBound> for AbsoluteFiniteBound {
    fn from(value: AbsoluteFiniteStartBound) -> Self {
        Self::Start(value)
    }
}

impl From<AbsoluteFiniteEndBound> for AbsoluteFiniteBound {
    fn from(value: AbsoluteFiniteEndBound) -> Self {
        Self::End(value)
    }
}

impl From<(AbsoluteFiniteBoundPosition, BoundExtremality)> for AbsoluteFiniteBound {
    fn from((finite_pos, extremality): (AbsoluteFiniteBoundPosition, BoundExtremality)) -> Self {
        match extremality {
            BoundExtremality::Start => Self::Start(AbsoluteFiniteStartBound::from(finite_pos)),
            BoundExtremality::End => Self::End(AbsoluteFiniteEndBound::from(finite_pos)),
        }
    }
}

//! Relative finite bound representation
//!
//! Represents an relative finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    RelativeBound,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteEndBound,
    RelativeFiniteStartBound,
    RelativeStartBound,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeFiniteBound {
    Start(RelativeFiniteStartBound),
    End(RelativeFiniteEndBound),
}

impl RelativeFiniteBound {
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    pub fn start(self) -> Option<RelativeFiniteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    pub fn end(self) -> Option<RelativeFiniteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    pub fn pos(self) -> RelativeFiniteBoundPosition {
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

    pub fn to_bound(self) -> RelativeBound {
        RelativeBound::from(self)
    }
}

impl HasBoundExtremality for RelativeFiniteBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for RelativeFiniteBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelativeFiniteStartBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelativeFiniteEndBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelativeStartBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelativeEndBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelativeBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for RelativeFiniteBound {
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

impl BoundOrdExtremaOps for RelativeFiniteBound {}

impl BoundOrd<RelativeFiniteStartBound> for RelativeFiniteBound {
    fn bound_cmp(&self, other: &RelativeFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelativeFiniteEndBound> for RelativeFiniteBound {
    fn bound_cmp(&self, other: &RelativeFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelativeStartBound> for RelativeFiniteBound {
    fn bound_cmp(&self, other: &RelativeStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelativeEndBound> for RelativeFiniteBound {
    fn bound_cmp(&self, other: &RelativeEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelativeBound> for RelativeFiniteBound {
    fn bound_cmp(&self, other: &RelativeBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl From<RelativeFiniteStartBound> for RelativeFiniteBound {
    fn from(value: RelativeFiniteStartBound) -> Self {
        Self::Start(value)
    }
}

impl From<RelativeFiniteEndBound> for RelativeFiniteBound {
    fn from(value: RelativeFiniteEndBound) -> Self {
        Self::End(value)
    }
}

impl From<(RelativeFiniteBoundPosition, BoundExtremality)> for RelativeFiniteBound {
    fn from((finite_pos, extremality): (RelativeFiniteBoundPosition, BoundExtremality)) -> Self {
        match extremality {
            BoundExtremality::Start => Self::Start(RelativeFiniteStartBound::from(finite_pos)),
            BoundExtremality::End => Self::End(RelativeFiniteEndBound::from(finite_pos)),
        }
    }
}

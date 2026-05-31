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
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundPartialEq, BoundPartialOrd};

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

impl BoundPartialEq for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &Self) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundEq for AbsoluteFiniteBound {}

impl BoundPartialEq<AbsoluteFiniteStartBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteFiniteStartBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<AbsoluteFiniteEndBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteFiniteEndBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<AbsoluteStartBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteStartBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<AbsoluteEndBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteEndBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<AbsoluteBound> for AbsoluteFiniteBound {
    fn bound_eq(&self, other: &AbsoluteBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialOrd for AbsoluteFiniteBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for AbsoluteFiniteBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::Start(lhs_finite_start), Self::Start(rhs_finite_start)) => {
                lhs_finite_start.bound_cmp(rhs_finite_start)
            },
            (Self::Start(finite_start), Self::End(finite_end)) => {
                // Comparison between start and end is not supposed to fail,
                // `BoundOrdering::Equal(None)` is a safe fallback
                finite_start
                    .bound_partial_cmp(finite_end)
                    .unwrap_or(BoundOrdering::Equal(None))
            },
            (Self::End(finite_end), Self::Start(finite_start)) => {
                // Comparison between start and end is not supposed to fail,
                // `BoundOrdering::Equal(None)` is a safe fallback
                finite_end
                    .bound_partial_cmp(finite_start)
                    .unwrap_or(BoundOrdering::Equal(None))
            },
            (Self::End(lhs_finite_end), Self::End(rhs_finite_end)) => lhs_finite_end.bound_cmp(rhs_finite_end),
        }
    }
}

impl BoundPartialOrd<AbsoluteFiniteStartBound> for AbsoluteFiniteBound {
    fn bound_partial_cmp(&self, other: &AbsoluteFiniteStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<AbsoluteFiniteEndBound> for AbsoluteFiniteBound {
    fn bound_partial_cmp(&self, other: &AbsoluteFiniteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<AbsoluteStartBound> for AbsoluteFiniteBound {
    fn bound_partial_cmp(&self, other: &AbsoluteStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<AbsoluteEndBound> for AbsoluteFiniteBound {
    fn bound_partial_cmp(&self, other: &AbsoluteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<AbsoluteBound> for AbsoluteFiniteBound {
    fn bound_partial_cmp(&self, other: &AbsoluteBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
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

//! Relative finite bound representation
//!
//! Represents an relative finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundPartialEq, BoundPartialOrd};
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

impl BoundPartialEq for RelativeFiniteBound {
    fn bound_eq(&self, other: &Self) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundEq for RelativeFiniteBound {}

impl BoundPartialEq<RelativeFiniteStartBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeFiniteStartBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeFiniteEndBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeFiniteEndBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeStartBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeStartBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeEndBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeEndBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeBound> for RelativeFiniteBound {
    fn bound_eq(&self, other: &RelativeBound) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other),
            Self::End(finite_end) => finite_end.bound_eq(other),
        }
    }
}

impl BoundPartialOrd for RelativeFiniteBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for RelativeFiniteBound {
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

impl BoundPartialOrd<RelativeFiniteStartBound> for RelativeFiniteBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteEndBound> for RelativeFiniteBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeStartBound> for RelativeFiniteBound {
    fn bound_partial_cmp(&self, other: &RelativeStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeEndBound> for RelativeFiniteBound {
    fn bound_partial_cmp(&self, other: &RelativeEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeBound> for RelativeFiniteBound {
    fn bound_partial_cmp(&self, other: &RelativeBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(finite_start) => finite_start.bound_partial_cmp(other),
            Self::End(finite_end) => finite_end.bound_partial_cmp(other),
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

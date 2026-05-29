//! Absolute finite bound representation
//!
//! Represents an absolute finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing absolute bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::absolute::finite_end_bound::AbsoluteFiniteEndBound;
use crate::intervals::absolute::finite_start_bound::AbsoluteFiniteStartBound;
use crate::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBoundPosition};
use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};

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

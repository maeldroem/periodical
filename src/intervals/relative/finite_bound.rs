//! Relative finite bound representation
//!
//! Represents an relative finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::relative::finite_end_bound::RelativeFiniteEndBound;
use crate::intervals::relative::finite_start_bound::RelativeFiniteStartBound;
use crate::intervals::relative::{RelativeBound, RelativeFiniteBoundPosition};

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

//! Absolute finite start bound
//!
//! Represents the finite start bound of an absolute interval.
//! If you need to represent infinity, see [`AbsoluteStartBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::finite_bound::AbsoluteFiniteBound;
use crate::intervals::absolute::finite_end_bound::AbsoluteFiniteEndBound;
use crate::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteFiniteStartBound(AbsoluteFiniteBoundPosition);

impl AbsoluteFiniteStartBound {
    pub fn new(finite_bound_pos: AbsoluteFiniteBoundPosition) -> Self {
        Self(finite_bound_pos)
    }

    pub fn finite_bound_position(&self) -> AbsoluteFiniteBoundPosition {
        self.0
    }

    pub fn to_start_bound(self) -> AbsoluteStartBound {
        AbsoluteStartBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> AbsoluteFiniteBound {
        AbsoluteFiniteBound::from(self)
    }

    pub fn to_bound(self) -> AbsoluteBound {
        AbsoluteBound::from(self)
    }

    pub fn opposite(self) -> AbsoluteFiniteEndBound {
        AbsoluteFiniteEndBound::new(AbsoluteFiniteBoundPosition::new_with_inclusivity(
            self.finite_bound_position().time(),
            self.finite_bound_position().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for AbsoluteFiniteStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteFiniteStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.finite_bound_position()
            .cmp(&other.finite_bound_position())
            .then_with(|| {
                match (
                    self.finite_bound_position().inclusivity(),
                    other.finite_bound_position().inclusivity(),
                ) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Less,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Greater,
                }
            })
    }
}

impl From<AbsoluteFiniteBoundPosition> for AbsoluteFiniteStartBound {
    fn from(value: AbsoluteFiniteBoundPosition) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

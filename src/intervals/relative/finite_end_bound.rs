//! Relative finite end bound
//!
//! Represents the finite end bound of an relative interval.
//! If you need to represent infinity, see [`RelativeEndBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::finite_bound::RelativeFiniteBound;
use crate::intervals::relative::finite_start_bound::RelativeFiniteStartBound;
use crate::intervals::relative::{RelativeBound, RelativeEndBound, RelativeFiniteBoundPosition};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeFiniteEndBound(RelativeFiniteBoundPosition);

impl RelativeFiniteEndBound {
    pub fn new(finite_bound_pos: RelativeFiniteBoundPosition) -> Self {
        Self(finite_bound_pos)
    }

    pub fn finite_bound_position(&self) -> RelativeFiniteBoundPosition {
        self.0
    }

    pub fn to_end_bound(self) -> RelativeEndBound {
        RelativeEndBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> RelativeFiniteBound {
        RelativeFiniteBound::from(self)
    }

    pub fn to_bound(self) -> RelativeBound {
        RelativeBound::from(self)
    }

    pub fn opposite(self) -> RelativeFiniteStartBound {
        RelativeFiniteStartBound::new(RelativeFiniteBoundPosition::new_with_inclusivity(
            self.finite_bound_position().offset(),
            self.finite_bound_position().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for RelativeFiniteEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeFiniteEndBound {
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
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Greater,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Less,
                }
            })
    }
}

impl From<RelativeFiniteBoundPosition> for RelativeFiniteEndBound {
    fn from(value: RelativeFiniteBoundPosition) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

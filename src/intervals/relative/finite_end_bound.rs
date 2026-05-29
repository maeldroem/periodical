//! Relative finite end bound
//!
//! Represents the finite end bound of an relative interval.
//! If you need to represent infinity, see [`RelativeEndBound`].

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::relative::finite_bound::RelativeFiniteBound;
use crate::intervals::relative::{RelativeBound, RelativeFiniteBoundPosition};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeFiniteEndBound(RelativeFiniteBoundPosition);

impl RelativeFiniteEndBound {
    pub fn finite_bound_position(&self) -> RelativeFiniteBoundPosition {
        self.0
    }

    pub fn to_finite_bound(self) -> RelativeFiniteBound {
        todo!();
    }

    pub fn to_bound(self) -> RelativeBound {
        todo!();
    }
}

// impl Ord, conversion, etc.

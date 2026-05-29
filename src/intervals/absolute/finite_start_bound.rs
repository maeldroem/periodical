//! Absolute finite start bound
//!
//! Represents the finite start bound of an absolute interval.
//! If you need to represent infinity, see [`AbsoluteStartBound`].

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::finite_bound::AbsoluteFiniteBound;
use crate::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBoundPosition};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteFiniteStartBound(AbsoluteFiniteBoundPosition);

impl AbsoluteFiniteStartBound {
    pub fn finite_bound_position(&self) -> AbsoluteFiniteBoundPosition {
        self.0
    }

    pub fn to_finite_bound(self) -> AbsoluteFiniteBound {
        todo!();
    }

    pub fn to_bound(self) -> AbsoluteBound {
        todo!();
    }
}

// impl Ord, conversion, etc.

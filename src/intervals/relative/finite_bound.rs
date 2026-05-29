//! Relative finite bound representation
//!
//! Represents an relative finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::relative::RelativeBound;
use crate::intervals::relative::finite_end_bound::RelativeFiniteEndBound;
use crate::intervals::relative::finite_start_bound::RelativeFiniteStartBound;

#[derive(Debug, Clone, Copy)]
pub enum RelativeFiniteBound {
    Start(RelativeFiniteStartBound),
    End(RelativeFiniteEndBound),
}

impl RelativeFiniteBound {
    pub fn is_start(&self) -> bool {
        todo!();
    }

    pub fn is_end(&self) -> bool {
        todo!();
    }

    pub fn start(self) -> Option<RelativeFiniteStartBound> {
        todo!();
    }

    pub fn end(self) -> Option<RelativeFiniteEndBound> {
        todo!();
    }

    pub fn opposite(self) -> Option<Self> {
        todo!();
    }

    pub fn to_bound(self) -> RelativeBound {
        todo!();
    }
}

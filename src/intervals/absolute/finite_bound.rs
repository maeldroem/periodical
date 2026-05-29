//! Absolute finite bound representation
//!
//! Represents an absolute finite bound regardless of its extremality (start/end).
//! This is particularly useful for representing absolute bounds of an interval
//! as a single type, while still conserving its extremality.

use crate::intervals::absolute::AbsoluteBound;
use crate::intervals::absolute::finite_end_bound::AbsoluteFiniteEndBound;
use crate::intervals::absolute::finite_start_bound::AbsoluteFiniteStartBound;

#[derive(Debug, Clone, Copy)]
pub enum AbsoluteFiniteBound {
    Start(AbsoluteFiniteStartBound),
    End(AbsoluteFiniteEndBound),
}

impl AbsoluteFiniteBound {
    pub fn is_start(&self) -> bool {
        todo!();
    }

    pub fn is_end(&self) -> bool {
        todo!();
    }

    pub fn start(self) -> Option<AbsoluteFiniteStartBound> {
        todo!();
    }

    pub fn end(self) -> Option<AbsoluteFiniteEndBound> {
        todo!();
    }

    pub fn opposite(self) -> Option<Self> {
        todo!();
    }

    pub fn to_bound(self) -> AbsoluteBound {
        todo!();
    }
}

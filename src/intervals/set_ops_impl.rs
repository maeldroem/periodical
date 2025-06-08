//! Set operations on intervals
//!
//! Implements set operations for intervals

use crate::collections::{Intervals, Union};
use crate::set_ops::*;

use super::Interval;

impl Unite for Interval {
    type Output = Intervals;

    /// Unites two intervals
    fn unite(self, rhs: Self) -> Union<Self::Output> {
        Union::new(Intervals::from_iter([self, rhs]))
    }
}

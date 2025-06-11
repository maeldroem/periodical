//! `Intervals` iterator and its derivatives

use std::collections::VecDeque;

use crate::collections::set_ops::*;
use crate::intervals::Interval;

/// Simple iterator type containing [`Interval`]s
pub struct Intervals(VecDeque<Interval>);

impl Intervals {
    /// Creates a union of the intervals
    #[must_use]
    pub fn unite(self) -> Union<Self> {
        Union::new(self)
    }
}

impl Iterator for Intervals {
    type Item = Interval;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_back()
    }
}

impl DoubleEndedIterator for Intervals {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }
}

impl FromIterator<Interval> for Intervals {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Interval>,
    {
        Intervals(iter.into_iter().collect::<VecDeque<Interval>>())
    }
}

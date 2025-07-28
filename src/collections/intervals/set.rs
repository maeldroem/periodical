//! Interval set structure for efficient processing of interval sets

use std::collections::BTreeSet;
use std::ops::Bound;

use crate::intervals::prelude::*;
use crate::ops::UnionResult;

/// Set of interval bounds
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteIntervalSet {
    bounds: BTreeSet<AbsoluteBounds>,
}

impl AbsoluteIntervalSet {
    /// Creates a new absolute interval set with the given start and end bounds
    #[must_use]
    pub fn new(bounds: BTreeSet<AbsoluteBounds>) -> Self {
        AbsoluteIntervalSet { bounds }
    }

    /// Returns a reference to the set of bounds
    #[must_use]
    pub fn bounds(&self) -> &BTreeSet<AbsoluteBounds> {
        &self.bounds
    }

    /// Returns a mutable reference to the set of bounds
    #[must_use]
    pub fn bounds_mut(&mut self) -> &mut BTreeSet<AbsoluteBounds> {
        &mut self.bounds
    }

    /// Unites the set of intervals
    #[must_use]
    pub fn unite(&self) -> Vec<AbsoluteBounds> {
        let mut united_intervals = vec![];

        let Some(mut united_so_far) = self.bounds.first().cloned() else {
            // The bounds tree was empty
            return united_intervals;
        };

        let mut last_united = united_so_far.clone();

        loop {
            // Upper bound is last_united's end
            let upper_bound = match last_united.future_continuation() {
                EmptiableAbsoluteBounds::Bound(bound) => Bound::Included(bound),
                EmptiableAbsoluteBounds::Empty => Bound::Unbounded,
            };

            let max_start_overlapping_last_united = self
                .bounds
                .range((Bound::Excluded(last_united.clone()), upper_bound))
                .max();

            if let Some(max_start_overlapping_last_united) = max_start_overlapping_last_united {
                match united_so_far.unite(max_start_overlapping_last_united) {
                    UnionResult::United(united) => {
                        last_united = united.clone();
                        united_so_far = united;
                    },
                    UnionResult::Separate => {
                        unreachable!(
                            "The interval argument has its start within the subject interval, \
                        or touching the subject interval's end, so already qualifies for a union"
                        );
                    },
                }

                continue;
            }

            // No intervals starts within (or touches the end of) the last united interval,
            // so we register what's united so far and prepare for the next round
            united_intervals.push(united_so_far.clone());

            let EmptiableAbsoluteBounds::Bound(last_united_continuation) = last_united.future_continuation() else {
                // If the future continuation of the last united bound is empty,
                // it signifies that there's no possible next bound, so we break the loop
                break;
            };

            let next_disjoint_interval = self
                .bounds
                .range((Bound::Included(last_united_continuation), Bound::Unbounded))
                .min()
                .cloned();

            if let Some(next_disjoint_interval) = next_disjoint_interval {
                // Reset united_so_far and last_united to the next disjoint interval
                last_united = next_disjoint_interval;
                united_so_far = last_united.clone();
            } else {
                // Otherwise if there was no next disjoint interval, it means we are done
                break;
            }
        }

        united_intervals
    }
}

impl<A> Extend<A> for AbsoluteIntervalSet
where
    A: HasEmptiableAbsoluteBounds,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = A>,
    {
        for interval in iter {
            let EmptiableAbsoluteBounds::Bound(bounds) = interval.emptiable_abs_bounds() else {
                continue;
            };

            self.bounds.insert(bounds);
        }
    }
}

impl<A> FromIterator<A> for AbsoluteIntervalSet
where
    A: HasEmptiableAbsoluteBounds,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = A>,
    {
        AbsoluteIntervalSet::new(
            iter.into_iter()
                .filter_map(|interval| {
                    let EmptiableAbsoluteBounds::Bound(bounds) = interval.emptiable_abs_bounds() else {
                        return None;
                    };

                    Some(bounds)
                })
                .collect::<BTreeSet<AbsoluteBounds>>(),
        )
    }
}

// TODO: Implement relative version of AbsoluteIntervalSet & impl to relative, to absolute conversions
// Not the ToAbsolute / ToRelative traits, reserved for intervals

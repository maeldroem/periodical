//! Interval set structure for efficient processing of interval sets

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::ops::Bound;
use std::rc::Rc;

use crate::intervals::prelude::*;
use crate::ops::UnionResult;

/// Newtype for chronologically sorting [`AbsoluteBounds`] by start
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StartSortedAbsBounds(Rc<AbsoluteBounds>);

impl PartialOrd for StartSortedAbsBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for StartSortedAbsBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl Borrow<AbsoluteBounds> for StartSortedAbsBounds {
    fn borrow(&self) -> &AbsoluteBounds {
        self.0.borrow()
    }
}

/// Newtype for chronologically sorting [`AbsoluteBounds`] by end
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EndSortedAbsBounds(Rc<AbsoluteBounds>);

impl PartialOrd for EndSortedAbsBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EndSortedAbsBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.end().cmp(other.0.end()) {
            Ordering::Less => Ordering::Less,
            // We don't reverse the ordering so that the larger interval comes first, allowing better processing
            Ordering::Equal => self.0.start().cmp(other.0.start()),
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl Borrow<AbsoluteBounds> for EndSortedAbsBounds {
    fn borrow(&self) -> &AbsoluteBounds {
        self.0.borrow()
    }
}

/// Set of interval bounds
#[derive(Debug, Clone, Default)]
pub struct AbsoluteIntervalSet {
    sorted_by_start: BTreeSet<StartSortedAbsBounds>,
    sorted_by_end: BTreeSet<EndSortedAbsBounds>,
}

impl AbsoluteIntervalSet {
    /// Creates a new empty absolute interval set
    #[must_use]
    pub fn new() -> Self {
        AbsoluteIntervalSet::default()
    }

    /// Returns a reference to the set of bounds sorted by start bound
    #[must_use]
    pub fn sorted_by_start(&self) -> &BTreeSet<StartSortedAbsBounds> {
        &self.sorted_by_start
    }

    /// Returns a reference to the set of bounds sorted by end bound
    #[must_use]
    pub fn sorted_by_end(&self) -> &BTreeSet<EndSortedAbsBounds> {
        &self.sorted_by_end
    }

    /// Inserts a value in the set
    ///
    /// Returns whether was newly inserted for the start bound and end bound
    pub fn insert(&mut self, bounds: AbsoluteBounds) -> (bool, bool) {
        let bounds_rc = Rc::new(bounds);

        let by_start_insert = self.sorted_by_start.insert(StartSortedAbsBounds(Rc::clone(&bounds_rc)));
        let by_end_insert = self.sorted_by_end.insert(EndSortedAbsBounds(bounds_rc));

        (by_start_insert, by_end_insert)
    }

    /// Gets the [`AbsoluteBounds`], if any, that matches the start bound of the given bounds
    #[must_use]
    pub fn get_by_start(&self, bounds: &AbsoluteBounds) -> Option<&AbsoluteBounds> {
        self.sorted_by_start.get(bounds).map(Borrow::<AbsoluteBounds>::borrow)
    }

    /// Gets the [`AbsoluteBounds`], if any, that matches the end bound of the given bounds
    #[must_use]
    pub fn get_by_end(&self, bounds: &AbsoluteBounds) -> Option<&AbsoluteBounds> {
        self.sorted_by_end.get(bounds).map(Borrow::<AbsoluteBounds>::borrow)
    }

    /// Removes an [`AbsoluteBounds`] from the set
    ///
    /// Returns whether such a [`AbsoluteBounds`] existed in the set
    pub fn remove(&mut self, bounds: &AbsoluteBounds) -> bool {
        let by_start_removal = self.sorted_by_start.remove(bounds);
        let by_end_removal = self.sorted_by_start.remove(bounds);

        by_start_removal || by_end_removal
    }

    /// Unites the set of intervals
    #[must_use]
    pub fn unite(&self) -> Vec<AbsoluteBounds> {
        let mut united_intervals: Vec<AbsoluteBounds> = Vec::new();

        let Some(mut united_so_far) = self
            .sorted_by_start()
            .first()
            .map(Borrow::<AbsoluteBounds>::borrow)
            .cloned()
        else {
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
                .sorted_by_start()
                .range((Bound::Excluded(last_united.clone()), upper_bound.clone()))
                .max()
                .map(Borrow::<AbsoluteBounds>::borrow);

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
                .sorted_by_start()
                .range((Bound::Included(last_united_continuation), Bound::Unbounded))
                .min()
                .map(Borrow::<AbsoluteBounds>::borrow)
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

    /// Intersects the current set with the given other set
    #[must_use]
    pub fn intersect<I>(&self, other: I) -> Vec<AbsoluteBounds>
    where
        I: IntoIterator,
        I::Item: HasEmptiableAbsoluteBounds,
    {
        todo!()
        // let mut intersected_intervals: Vec<AbsoluteBounds> = Vec::new();

        // for other_interval in other {
        //     let EmptiableAbsoluteBounds::Bound(other_interval) = other_interval else {
        //         // Empty intervals never intersect
        //         continue;
        //     };

        //     self.bounds.range((Bound::))
        // }

        // intersected_intervals
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

            self.insert(bounds);
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
        let mut set = AbsoluteIntervalSet::new();

        for emptiable_bounds in iter {
            let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds.emptiable_abs_bounds() else {
                continue;
            };

            set.insert(bounds);
        }

        set
    }
}

// TODO: Implement relative version of AbsoluteIntervalSet & impl to relative, to absolute conversions
// Not the ToAbsolute / ToRelative traits, reserved for intervals

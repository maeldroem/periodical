//! Interval set structure for efficient processing of interval sets

use std::collections::{BTreeSet, HashMap};
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use chrono::{DateTime, Utc};

use super::set_ops::unite::AccumulativelyUnitableIteratorDispatcher;

use crate::intervals::absolute::AbsoluteStartBound;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::prelude::*;
use crate::intervals::relative::{RelativeBounds, RelativeStartBound};
use crate::ops::{DifferenceResult, SymmetricDifferenceResult};

/// Set of non-overlapping absolute interval bounds
///
/// New intervals are united with the others such that the invariant isn't violated.
///
/// # Invariants
///
/// All intervals within the set must not be overlapping nor adjacent.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub struct AbsoluteUnitedIntervalSet {
    intervals: BTreeSet<AbsoluteBounds>,
}

impl AbsoluteUnitedIntervalSet {
    /// Creates a new empty absolute interval set
    #[must_use]
    pub fn new() -> Self {
        AbsoluteUnitedIntervalSet::default()
    }

    /// Returns a vector of clones of the inner non-overlapping intervals
    #[must_use]
    pub fn intervals(&self) -> Vec<AbsoluteBounds> {
        self.intervals.iter().cloned().collect()
    }

    /*
    TODO
    Make a system that is a set of united intervals and can respond to queries such as
    - finding the interval with the closest start to a given point
    - finding the interval with the closest end to a given point
    - other methods useful for set operations
    then implement the set operations OPTIMALLY using those newly created methods
     */

    /// Inserts an interval in the set
    pub fn insert<T>(&mut self, interval: &T)
    where
        T: HasEmptiableAbsoluteBounds,
    {
        let EmptiableAbsoluteBounds::Bound(bounds) = interval.emptiable_abs_bounds() else {
            // An empty interval does nothing in a set
            return;
        };

        // We need to assume the invariant is not broken, so those intervals are not overlapping
        let (intervals_to_remove, intervals_to_unite): (Vec<_>, Vec<_>) = self
            .overlapping_intervals(&bounds, BoundContainmentRuleSet::Lenient)
            .filter_map(|unitable_interval| {
                unitable_interval
                .unite(&bounds)
                .united()
                // We zip the original unitable interval as we need to remove it to conserve the no overlap invariant
                // We are kinda forced to clone the original `unitable_interval` so that we don't keep an immutable
                // reference to `self.intervals` that'd prevent taking a mutable reference to `self.intervals`
                .map(|united| (unitable_interval.clone(), united))
            })
            .unzip();

        let mut united_intervals = intervals_to_unite.iter().acc_union();

        // Only one united interval should be created. If more are created, it is a bug.
        match united_intervals.next() {
            Some(united) => {
                self.intervals.insert(united);
            },
            None => {
                self.intervals.insert(bounds);
            },
        }

        // Check for if there's a second united interval
        debug_assert!(united_intervals.next().is_some());

        for interval_to_remove in intervals_to_remove {
            self.intervals.remove(&interval_to_remove);
        }
    }

    /// Removes an interval from the set
    ///
    /// Returns whether such [`AbsoluteBounds`] existed in the set
    pub fn remove<T>(&mut self, interval: &T) -> bool
    where
        T: HasEmptiableAbsoluteBounds,
    {
        let EmptiableAbsoluteBounds::Bound(bounds) = interval.emptiable_abs_bounds() else {
            return false;
        };

        self.intervals.remove(&bounds)
    }

    /// Returns all the [`AbsoluteBounds`] overlapping the given interval using the predefined overlap rules
    pub fn simple_overlapping_intervals<T>(&self, interval: &T) -> impl Iterator<Item = &AbsoluteBounds>
    where
        T: HasAbsoluteBounds,
    {
        self.overlapping_intervals(interval, BoundContainmentRuleSet::default())
    }

    /// Returns all the [`AbsoluteBounds`] overlapping the given interval using the given rules
    pub fn overlapping_intervals<T>(
        &self,
        interval: &T,
        rule_set: BoundContainmentRuleSet,
    ) -> impl Iterator<Item = &AbsoluteBounds>
    where
        T: HasAbsoluteBounds,
    {
        let bounds = interval.abs_bounds();

        let upper_bound = match bounds.future_continuation() {
            EmptiableAbsoluteBounds::Bound(mut future_continuation) => {
                let more_inclusive_future_continuation_start = match future_continuation.abs_start() {
                    AbsoluteStartBound::Finite(mut finite_future_continuation_start) => {
                        // We make it exclusive so that other calls can still consider exclusive-exclusive adjacency
                        finite_future_continuation_start.set_inclusivity(BoundInclusivity::Exclusive);
                        AbsoluteStartBound::Finite(finite_future_continuation_start)
                    },
                    infinite_future_continuation_start @ AbsoluteStartBound::InfinitePast => {
                        infinite_future_continuation_start
                    },
                };

                future_continuation.set_start(more_inclusive_future_continuation_start);

                Bound::Included(future_continuation)
            },
            EmptiableAbsoluteBounds::Empty => Bound::Unbounded,
        };

        self.intervals
            .range((Bound::Unbounded, upper_bound))
            .filter(move |interval| {
                matches!(
                    bounds.disambiguated_bound_position(interval.end(), rule_set),
                    DisambiguatedBoundPosition::OnStart
                        | DisambiguatedBoundPosition::Equal
                        | DisambiguatedBoundPosition::Inside
                        | DisambiguatedBoundPosition::OnEnd
                        | DisambiguatedBoundPosition::OutsideAfter,
                )
            })
    }

    /// Intersects the current set with the given other set
    #[must_use]
    pub fn intersect<I>(&self, other_iter: I) -> Vec<Vec<AbsoluteBounds>>
    where
        I: IntoIterator,
        I::Item: HasEmptiableAbsoluteBounds,
    {
        other_iter
            .into_iter()
            .filter_map(|other_interval| other_interval.emptiable_abs_bounds().bound())
            .map(|other_interval| {
                self.overlapping_intervals(&other_interval, BoundContainmentRuleSet::Strict)
                    .filter_map(|overlapping_interval| overlapping_interval.intersect(&other_interval).intersected())
                    .collect()
            })
            .collect()
    }

    /// Differentiates the current set with the given other set acting as _removers_
    ///
    /// The _removers_ must be sorted and the contained intervals should not be overlapping.
    /// The responsibility is left to the caller in order to avoid double-processing.
    ///
    /// Possible future change: use a united set as the parameter instead of relying on the caller.
    #[must_use]
    pub fn difference<I>(&self, other_iter: I) -> Vec<AbsoluteBounds>
    where
        I: IntoIterator,
        I::Item: HasEmptiableAbsoluteBounds,
    {
        // NOTE: can be improved by using parallel iterators
        let og_interval_diff_result_map: HashMap<&AbsoluteBounds, DifferenceResult<EmptiableAbsoluteBounds>> =
            other_iter
                .into_iter()
                .filter_map(|other_interval| other_interval.emptiable_abs_bounds().bound())
                .flat_map(|other_interval| {
                    self.overlapping_intervals(&other_interval, BoundContainmentRuleSet::Strict)
                        .map(|overlapping_interval| {
                            (
                                overlapping_interval, // Conserve the original one for later processing
                                overlapping_interval.differentiate(&other_interval),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect();

        let mut result = vec![];

        for bound in &self.intervals {
            // Using our hash map, we can go over all our intervals and look for those affected
            if let Some(diff_res) = og_interval_diff_result_map.get(bound) {
                // If affected, then we check for if we need to ignore it,
                // which happens when the interval got shrunk to nothingness or if it was simply separate,
                // otherwise we push the differentiated parts to the vector =)
                match diff_res {
                    DifferenceResult::Shrunk(EmptiableAbsoluteBounds::Bound(shrunk)) => {
                        result.push(shrunk.clone());
                    },
                    DifferenceResult::Split(
                        EmptiableAbsoluteBounds::Bound(split_first_part),
                        EmptiableAbsoluteBounds::Bound(split_second_part),
                    ) => {
                        result.push(split_first_part.clone());
                        result.push(split_second_part.clone());
                    },
                    DifferenceResult::Separate | DifferenceResult::Shrunk(_) | DifferenceResult::Split(..) => {},
                }
            } else {
                // If not, then we know we just need to push the unaffected interval
                result.push(bound.clone());
            }
        }

        result
    }

    /// Symmetrically differentiates the current set with the given other set
    ///
    /// The other set must be sorted and the contained intervals should not be overlapping.
    /// The responsibility is left to the caller in order to avoid double-processing.
    ///
    /// Possible future change: use a united set as the parameter instead of relying on the caller.
    #[must_use]
    pub fn sym_difference<I>(&self, other_iter: I) -> Vec<AbsoluteBounds>
    where
        I: IntoIterator,
        I::Item: HasEmptiableAbsoluteBounds,
    {
        // NOTE: can be improved by using parallel iterators
        let og_interval_sym_diff_result_map: HashMap<
            &AbsoluteBounds,
            SymmetricDifferenceResult<EmptiableAbsoluteBounds>,
        > = other_iter
            .into_iter()
            .filter_map(|other_interval| other_interval.emptiable_abs_bounds().bound())
            .flat_map(|other_interval| {
                self.overlapping_intervals(&other_interval, BoundContainmentRuleSet::Strict)
                    .map(|overlapping_interval| {
                        (
                            overlapping_interval, // Conserve the original one for later processing
                            overlapping_interval.symmetrically_differentiate(&other_interval),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect();

        let mut result = vec![];

        for bound in &self.intervals {
            // Using our hash map, we can go over all our intervals and look for those affected
            if let Some(sym_diff_res) = og_interval_sym_diff_result_map.get(bound) {
                // If affected, then we check for if we need to ignore it,
                // which happens when the interval got shrunk to nothingness or if it was simply separate,
                // otherwise we push the differentiated parts to the vector =)
                match sym_diff_res {
                    SymmetricDifferenceResult::Shrunk(EmptiableAbsoluteBounds::Bound(shrunk)) => {
                        result.push(shrunk.clone());
                    },
                    SymmetricDifferenceResult::Split(
                        EmptiableAbsoluteBounds::Bound(split_first_part),
                        EmptiableAbsoluteBounds::Bound(split_second_part),
                    ) => {
                        result.push(split_first_part.clone());
                        result.push(split_second_part.clone());
                    },
                    SymmetricDifferenceResult::Separate
                    | SymmetricDifferenceResult::Shrunk(_)
                    | SymmetricDifferenceResult::Split(..) => {},
                }
            } else {
                // If not, then we know we just need to push the unaffected interval
                result.push(bound.clone());
            }
        }

        result
    }

    /// Converts the absolute set into a relative one
    #[must_use]
    pub fn to_relative(self, reference_time: DateTime<Utc>) -> RelativeUnitedIntervalSet {
        self.intervals
            .into_iter()
            .map(|interval| interval.to_relative(reference_time))
            .collect::<RelativeUnitedIntervalSet>()
    }
}

impl<A> Extend<A> for AbsoluteUnitedIntervalSet
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

            self.insert(&bounds);
        }
    }
}

impl<A> FromIterator<A> for AbsoluteUnitedIntervalSet
where
    A: HasEmptiableAbsoluteBounds,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = A>,
    {
        let mut set = AbsoluteUnitedIntervalSet::new();

        for emptiable_bounds in iter {
            let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds.emptiable_abs_bounds() else {
                continue;
            };

            set.insert(&bounds);
        }

        set
    }
}

/// Set of non-overlapping relative interval bounds
///
/// New intervals are united with the others such that the invariant isn't violated.
///
/// # Invariants
///
/// All intervals within the set must not be overlapping nor adjacent.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub struct RelativeUnitedIntervalSet {
    intervals: BTreeSet<RelativeBounds>,
}

impl RelativeUnitedIntervalSet {
    /// Creates a new empty relative interval set
    #[must_use]
    pub fn new() -> Self {
        RelativeUnitedIntervalSet::default()
    }

    /// Returns a vector of clones of the inner non-overlapping intervals
    #[must_use]
    pub fn intervals(&self) -> Vec<RelativeBounds> {
        self.intervals.iter().cloned().collect()
    }

    /*
    TODO
    Make a system that is a set of united intervals and can respond to queries such as
    - finding the interval with the closest start to a given point
    - finding the interval with the closest end to a given point
    - other methods useful for set operations
    then implement the set operations OPTIMALLY using those newly created methods
     */

    /// Inserts an interval in the set
    pub fn insert<T>(&mut self, interval: &T)
    where
        T: HasEmptiableRelativeBounds,
    {
        let EmptiableRelativeBounds::Bound(bounds) = interval.emptiable_rel_bounds() else {
            // An empty interval does nothing in a set
            return;
        };

        // We need to assume the invariant is not broken, so those intervals are not overlapping
        let (intervals_to_remove, intervals_to_unite): (Vec<_>, Vec<_>) = self
            .overlapping_intervals(&bounds, BoundContainmentRuleSet::Lenient)
            .filter_map(|unitable_interval| {
                unitable_interval
                .unite(&bounds)
                .united()
                // We zip the original unitable interval as we need to remove it to conserve the no overlap invariant
                // We are kinda forced to clone the original `unitable_interval` so that we don't keep an immutable
                // reference to `self.intervals` that'd prevent taking a mutable reference to `self.intervals`
                .map(|united| (unitable_interval.clone(), united))
            })
            .unzip();

        let mut united_intervals = intervals_to_unite.iter().acc_union();

        // Only one united interval should be created. If more are created, it is a bug.
        match united_intervals.next() {
            Some(united) => {
                self.intervals.insert(united);
            },
            None => {
                self.intervals.insert(bounds);
            },
        }

        // Check for if there's a second united interval
        debug_assert!(united_intervals.next().is_some());

        for interval_to_remove in intervals_to_remove {
            self.intervals.remove(&interval_to_remove);
        }
    }

    /// Removes an interval from the set
    ///
    /// Returns whether such [`RelativeBounds`] existed in the set
    pub fn remove<T>(&mut self, interval: &T) -> bool
    where
        T: HasEmptiableRelativeBounds,
    {
        let EmptiableRelativeBounds::Bound(bounds) = interval.emptiable_rel_bounds() else {
            return false;
        };

        self.intervals.remove(&bounds)
    }

    /// Returns all the [`RelativeBounds`] overlapping the given interval using the predefined overlap rules
    pub fn simple_overlapping_intervals<T>(&self, interval: &T) -> impl Iterator<Item = &RelativeBounds>
    where
        T: HasRelativeBounds,
    {
        self.overlapping_intervals(interval, BoundContainmentRuleSet::default())
    }

    /// Returns all the [`RelativeBounds`] overlapping the given interval using the given rules
    pub fn overlapping_intervals<T>(
        &self,
        interval: &T,
        rule_set: BoundContainmentRuleSet,
    ) -> impl Iterator<Item = &RelativeBounds>
    where
        T: HasRelativeBounds,
    {
        let bounds = interval.rel_bounds();

        let upper_bound = match bounds.future_continuation() {
            EmptiableRelativeBounds::Bound(mut future_continuation) => {
                let more_inclusive_future_continuation_start = match future_continuation.rel_start() {
                    RelativeStartBound::Finite(mut finite_future_continuation_start) => {
                        // We make it exclusive so that other calls can still consider exclusive-exclusive adjacency
                        finite_future_continuation_start.set_inclusivity(BoundInclusivity::Exclusive);
                        RelativeStartBound::Finite(finite_future_continuation_start)
                    },
                    infinite_future_continuation_start @ RelativeStartBound::InfinitePast => {
                        infinite_future_continuation_start
                    },
                };

                future_continuation.set_start(more_inclusive_future_continuation_start);

                Bound::Included(future_continuation)
            },
            EmptiableRelativeBounds::Empty => Bound::Unbounded,
        };

        self.intervals
            .range((Bound::Unbounded, upper_bound))
            .filter(move |interval| {
                matches!(
                    bounds.disambiguated_bound_position(interval.end(), rule_set),
                    DisambiguatedBoundPosition::OnStart
                        | DisambiguatedBoundPosition::Equal
                        | DisambiguatedBoundPosition::Inside
                        | DisambiguatedBoundPosition::OnEnd
                        | DisambiguatedBoundPosition::OutsideAfter,
                )
            })
    }

    /// Intersects the current set with the given other set
    #[must_use]
    pub fn intersect<I>(&self, other_iter: I) -> Vec<Vec<RelativeBounds>>
    where
        I: IntoIterator,
        I::Item: HasEmptiableRelativeBounds,
    {
        other_iter
            .into_iter()
            .filter_map(|other_interval| other_interval.emptiable_rel_bounds().bound())
            .map(|other_interval| {
                self.overlapping_intervals(&other_interval, BoundContainmentRuleSet::Strict)
                    .filter_map(|overlapping_interval| overlapping_interval.intersect(&other_interval).intersected())
                    .collect()
            })
            .collect()
    }

    /// Differentiates the current set with the given other set acting as _removers_
    ///
    /// The _removers_ must be sorted and the contained intervals should not be overlapping.
    /// The responsibility is left to the caller in order to avoid double-processing.
    ///
    /// Possible future change: use a united set as the parameter instead of relying on the caller.
    #[must_use]
    pub fn difference<I>(&self, other_iter: I) -> Vec<RelativeBounds>
    where
        I: IntoIterator,
        I::Item: HasEmptiableRelativeBounds,
    {
        // NOTE: can be improved by using parallel iterators
        let og_interval_diff_result_map: HashMap<&RelativeBounds, DifferenceResult<EmptiableRelativeBounds>> =
            other_iter
                .into_iter()
                .filter_map(|other_interval| other_interval.emptiable_rel_bounds().bound())
                .flat_map(|other_interval| {
                    self.overlapping_intervals(&other_interval, BoundContainmentRuleSet::Strict)
                        .map(|overlapping_interval| {
                            (
                                overlapping_interval, // Conserve the original one for later processing
                                overlapping_interval.differentiate(&other_interval),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect();

        let mut result = vec![];

        for bound in &self.intervals {
            // Using our hash map, we can go over all our intervals and look for those affected
            if let Some(diff_res) = og_interval_diff_result_map.get(bound) {
                // If affected, then we check for if we need to ignore it,
                // which happens when the interval got shrunk to nothingness or if it was simply separate,
                // otherwise we push the differentiated parts to the vector =)
                match diff_res {
                    DifferenceResult::Shrunk(EmptiableRelativeBounds::Bound(shrunk)) => {
                        result.push(shrunk.clone());
                    },
                    DifferenceResult::Split(
                        EmptiableRelativeBounds::Bound(split_first_part),
                        EmptiableRelativeBounds::Bound(split_second_part),
                    ) => {
                        result.push(split_first_part.clone());
                        result.push(split_second_part.clone());
                    },
                    DifferenceResult::Separate | DifferenceResult::Shrunk(_) | DifferenceResult::Split(..) => {},
                }
            } else {
                // If not, then we know we just need to push the unaffected interval
                result.push(bound.clone());
            }
        }

        result
    }

    /// Symmetrically differentiates the current set with the given other set
    ///
    /// The other set must be sorted and the contained intervals should not be overlapping.
    /// The responsibility is left to the caller in order to avoid double-processing.
    ///
    /// Possible future change: use a united set as the parameter instead of relying on the caller.
    #[must_use]
    pub fn sym_difference<I>(&self, other_iter: I) -> Vec<RelativeBounds>
    where
        I: IntoIterator,
        I::Item: HasEmptiableRelativeBounds,
    {
        // NOTE: can be improved by using parallel iterators
        let og_interval_sym_diff_result_map: HashMap<
            &RelativeBounds,
            SymmetricDifferenceResult<EmptiableRelativeBounds>,
        > = other_iter
            .into_iter()
            .filter_map(|other_interval| other_interval.emptiable_rel_bounds().bound())
            .flat_map(|other_interval| {
                self.overlapping_intervals(&other_interval, BoundContainmentRuleSet::Strict)
                    .map(|overlapping_interval| {
                        (
                            overlapping_interval, // Conserve the original one for later processing
                            overlapping_interval.symmetrically_differentiate(&other_interval),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect();

        let mut result = vec![];

        for bound in &self.intervals {
            // Using our hash map, we can go over all our intervals and look for those affected
            if let Some(sym_diff_res) = og_interval_sym_diff_result_map.get(bound) {
                // If affected, then we check for if we need to ignore it,
                // which happens when the interval got shrunk to nothingness or if it was simply separate,
                // otherwise we push the differentiated parts to the vector =)
                match sym_diff_res {
                    SymmetricDifferenceResult::Shrunk(EmptiableRelativeBounds::Bound(shrunk)) => {
                        result.push(shrunk.clone());
                    },
                    SymmetricDifferenceResult::Split(
                        EmptiableRelativeBounds::Bound(split_first_part),
                        EmptiableRelativeBounds::Bound(split_second_part),
                    ) => {
                        result.push(split_first_part.clone());
                        result.push(split_second_part.clone());
                    },
                    SymmetricDifferenceResult::Separate
                    | SymmetricDifferenceResult::Shrunk(_)
                    | SymmetricDifferenceResult::Split(..) => {},
                }
            } else {
                // If not, then we know we just need to push the unaffected interval
                result.push(bound.clone());
            }
        }

        result
    }

    /// Converts the relative set into an absolute one
    #[must_use]
    pub fn to_absolute(self, reference_time: DateTime<Utc>) -> AbsoluteUnitedIntervalSet {
        self.intervals
            .into_iter()
            .map(|interval| interval.to_absolute(reference_time))
            .collect::<AbsoluteUnitedIntervalSet>()
    }
}

impl<A> Extend<A> for RelativeUnitedIntervalSet
where
    A: HasEmptiableRelativeBounds,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = A>,
    {
        for interval in iter {
            let EmptiableRelativeBounds::Bound(bounds) = interval.emptiable_rel_bounds() else {
                continue;
            };

            self.insert(&bounds);
        }
    }
}

impl<A> FromIterator<A> for RelativeUnitedIntervalSet
where
    A: HasEmptiableRelativeBounds,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = A>,
    {
        let mut set = RelativeUnitedIntervalSet::new();

        for emptiable_bounds in iter {
            let EmptiableRelativeBounds::Bound(bounds) = emptiable_bounds.emptiable_rel_bounds() else {
                continue;
            };

            set.insert(&bounds);
        }

        set
    }
}

// TODO: Implement relative version of AbsoluteIntervalSet & impl to relative, to absolute conversions
// Not the ToAbsolute / ToRelative traits, reserved for intervals

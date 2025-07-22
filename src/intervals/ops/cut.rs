//! Interval cutting

use chrono::{DateTime, Utc};

use super::time_containment_position::CanPositionTimeContainment;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;

/// Cut types, used by [`Cuttable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum CutType {
    /// Where the cut was made, both bound inclusivities will be inclusive
    #[default]
    InclusiveBoth,
    /// Where the cut was made, the future bound inclusivity will be exclusive, while the past one will be inclusive
    ExclusiveFuture,
    /// Where the cut was made, the past bound inclusivity will be exclusive, while the future one will be inclusive
    ExclusivePast,
    /// Where the cut was made, both bound inclusivities will be exclusive
    ExclusiveBoth,
}

impl CutType {
    /// Returns the bound inclusivity for the past side after the cut was made
    #[must_use]
    pub fn past_bound_inclusivity(&self) -> BoundInclusivity {
        match self {
            Self::InclusiveBoth | Self::ExclusiveFuture => BoundInclusivity::Inclusive,
            Self::ExclusivePast | Self::ExclusiveBoth => BoundInclusivity::Exclusive,
        }
    }

    /// Returns the bound inclusivity for the future side after the cut was made
    #[must_use]
    pub fn future_bound_inclusivity(&self) -> BoundInclusivity {
        match self {
            Self::InclusiveBoth | Self::ExclusivePast => BoundInclusivity::Inclusive,
            Self::ExclusiveBoth | Self::ExclusiveFuture => BoundInclusivity::Exclusive,
        }
    }
}

/// Result of a cut
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CutResult<T> {
    /// The cutting point was outside the given interval, or the cut itself was unsuccessful
    Uncut,
    /// The cut was successful, contains the cut two parts
    ///
    /// The two parts are in chronological order, since all intervals are too.
    Cut(T, T),
}

impl<T> CutResult<T> {
    /// Whether the [`CutResult`] is of the [`Uncut`](CutResult::Uncut) variant
    pub fn is_uncut(&self) -> bool {
        matches!(self, CutResult::Uncut)
    }

    /// Whether the [`CutResult`] is of the [`Cut`](CutResult::Cut) variant
    pub fn is_cut(&self) -> bool {
        matches!(self, CutResult::Cut(..))
    }

    /// Maps the contents of the [`Cut`](CutResult::Cut) variant
    pub fn map_cut<F, U>(self, mut f: F) -> CutResult<U>
    where
        F: FnMut(T, T) -> (U, U),
    {
        match self {
            Self::Uncut => CutResult::Uncut,
            Self::Cut(c1, c2) => {
                let mapped_cut = (f)(c1, c2);
                CutResult::Cut(mapped_cut.0, mapped_cut.1)
            },
        }
    }
}

/// Capacity to cut at specific time(s)
///
/// If you are looking for removing a given interval from another, see [`TODO TODO TODO`]
pub trait Cuttable {
    /// Output type
    type Output;

    /// Cuts the interval
    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output>;
}

impl Cuttable for AbsoluteBounds {
    type Output = Self;

    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bounds(self, at, cut_type)
    }
}

impl Cuttable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bounds(self, at, cut_type)
    }
}

impl Cuttable for AbsoluteInterval {
    type Output = Self;

    fn cut_at(&self, at: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bounds(&self.emptiable_abs_bounds(), at, cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

/// Cuts an [`AbsoluteBounds`]
#[must_use]
pub fn cut_abs_bounds(bounds: &AbsoluteBounds, at: DateTime<Utc>, cut_type: CutType) -> CutResult<AbsoluteBounds> {
    if !bounds.simple_contains(at) {
        return CutResult::Uncut;
    }

    let mut past_split = bounds.clone();
    let mut future_split = bounds.clone();

    past_split.set_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    )));

    future_split.set_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    )));

    CutResult::Cut(past_split, future_split)
}

/// Cuts an [`EmptiableAbsoluteBounds`]
#[must_use]
pub fn cut_emptiable_abs_bounds(
    bounds: &EmptiableAbsoluteBounds,
    at: DateTime<Utc>,
    cut_type: CutType,
) -> CutResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(non_empty_bounds) = bounds else {
        // Empty bounds can't be cut
        return CutResult::Uncut;
    };

    cut_abs_bounds(non_empty_bounds, at, cut_type)
        .map_cut(|c1, c2| (EmptiableAbsoluteBounds::from(c1), EmptiableAbsoluteBounds::from(c2)))
}

//! Interval cutting

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use chrono::{DateTime, Duration, Utc};

use super::prelude::*;
use super::time_containment::CanPositionTimeContainment;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval, HasEmptiableAbsoluteBounds,
    check_absolute_bounds_for_interval_creation,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfBoundedRelativeInterval, RelativeBounds, RelativeEndBound, RelativeFiniteBound,
    RelativeStartBound, check_relative_bounds_for_interval_creation,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{BoundedAbsoluteInterval, BoundedRelativeInterval, RelativeInterval};

/// Cut types, used by [`Cuttable`]
///
/// The contained bound inclusivities represent the start and end inclusivities for where the cut will be made.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub struct CutType(BoundInclusivity, BoundInclusivity);

impl CutType {
    /// Creates a new instance of [`CutType`]
    #[must_use]
    pub fn new(past_inclusivity: BoundInclusivity, future_inclusivity: BoundInclusivity) -> Self {
        CutType(past_inclusivity, future_inclusivity)
    }

    /// Returns the bound inclusivity for the past side after the cut was made
    #[must_use]
    pub fn past_bound_inclusivity(&self) -> BoundInclusivity {
        self.0
    }

    /// Returns the bound inclusivity for the future side after the cut was made
    #[must_use]
    pub fn future_bound_inclusivity(&self) -> BoundInclusivity {
        self.1
    }

    /// Returns a copy of the current instance with opposite inclusivities
    #[must_use]
    pub fn opposite(&self) -> Self {
        CutType::new(self.0.opposite(), self.1.opposite())
    }
}

impl From<(BoundInclusivity, BoundInclusivity)> for CutType {
    fn from((past_inclusivity, future_inclusivity): (BoundInclusivity, BoundInclusivity)) -> Self {
        CutType::new(past_inclusivity, future_inclusivity)
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
    #[must_use]
    pub fn is_uncut(&self) -> bool {
        matches!(self, CutResult::Uncut)
    }

    /// Whether the [`CutResult`] is of the [`Cut`](CutResult::Cut) variant
    #[must_use]
    pub fn is_cut(&self) -> bool {
        matches!(self, CutResult::Cut(..))
    }

    /// Returns the content of the [`Cut`](CutResult::Cut) variant
    #[must_use]
    pub fn cut(self) -> Option<(T, T)> {
        match self {
            Self::Uncut => None,
            Self::Cut(a, b) => Some((a, b)),
        }
    }

    /// Maps the contents of the [`Cut`](CutResult::Cut) variant
    #[must_use]
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
/// The generic type parameter `P` corresponds to the type used for positioning the cut.
///
/// If you are looking for removing a given interval from another, see [`TODO TODO TODO`]
pub trait Cuttable<P> {
    /// Output type
    type Output;

    /// Cuts the interval
    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output>;
}

impl<P> Cuttable<P> for AbsoluteBounds
where
    P: Into<DateTime<Utc>>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bounds(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for EmptiableAbsoluteBounds
where
    P: Into<DateTime<Utc>>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bounds(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for AbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bounds(&self.emptiable_abs_bounds(), position.into(), cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for BoundedAbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Output = AbsoluteInterval;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bounds(&self.abs_bounds(), position.into(), cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for HalfBoundedAbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Output = AbsoluteInterval;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bounds(&self.abs_bounds(), position.into(), cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for RelativeBounds
where
    P: Into<Duration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bounds(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for EmptiableRelativeBounds
where
    P: Into<Duration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_rel_bounds(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for RelativeInterval
where
    P: Into<Duration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_rel_bounds(&self.emptiable_rel_bounds(), position.into(), cut_type)
            .map_cut(|c1, c2| (RelativeInterval::from(c1), RelativeInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for BoundedRelativeInterval
where
    P: Into<Duration>,
{
    type Output = RelativeInterval;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bounds(&self.rel_bounds(), position.into(), cut_type)
            .map_cut(|c1, c2| (RelativeInterval::from(c1), RelativeInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for HalfBoundedRelativeInterval
where
    P: Into<Duration>,
{
    type Output = RelativeInterval;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bounds(&self.rel_bounds(), position.into(), cut_type)
            .map_cut(|c1, c2| (RelativeInterval::from(c1), RelativeInterval::from(c2)))
    }
}

// TODO: Find a way to implement these for P: Into<DateTime<Utc>> and P: Into<chrono::Duration>
impl Cuttable<DateTime<Utc>> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn cut_at(&self, position: DateTime<Utc>, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bounds(&self.abs_bounds(), position, cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

impl Cuttable<Duration> for UnboundedInterval {
    type Output = RelativeInterval;

    fn cut_at(&self, position: Duration, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bounds(&self.rel_bounds(), position, cut_type)
            .map_cut(|c1, c2| (RelativeInterval::from(c1), RelativeInterval::from(c2)))
    }
}

// TODO: Find a way to implement these for P: Into<DateTime<Utc>> and P: Into<chrono::Duration>
impl Cuttable<DateTime<Utc>> for EmptyInterval {
    type Output = ();

    fn cut_at(&self, _position: DateTime<Utc>, _cut_type: CutType) -> CutResult<Self::Output> {
        CutResult::Uncut
    }
}

impl Cuttable<Duration> for EmptyInterval {
    type Output = ();

    fn cut_at(&self, _position: Duration, _cut_type: CutType) -> CutResult<Self::Output> {
        CutResult::Uncut
    }
}

/// Cuts an [`AbsoluteBounds`]
#[must_use]
pub fn cut_abs_bounds(bounds: &AbsoluteBounds, at: DateTime<Utc>, cut_type: CutType) -> CutResult<AbsoluteBounds> {
    if !bounds.simple_contains(at) {
        return CutResult::Uncut;
    }

    let past_cut_end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    ));
    let future_cut_start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    ));

    if check_absolute_bounds_for_interval_creation(bounds.start(), &past_cut_end).is_err()
        || check_absolute_bounds_for_interval_creation(&future_cut_start, bounds.end()).is_err()
    {
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

/// Cuts an [`RelativeBounds`]
#[must_use]
pub fn cut_rel_bounds(bounds: &RelativeBounds, at: Duration, cut_type: CutType) -> CutResult<RelativeBounds> {
    if !bounds.simple_contains(at) {
        return CutResult::Uncut;
    }

    let past_cut_end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    ));
    let future_cut_start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    ));

    if check_relative_bounds_for_interval_creation(bounds.start(), &past_cut_end).is_err()
        || check_relative_bounds_for_interval_creation(&future_cut_start, bounds.end()).is_err()
    {
        return CutResult::Uncut;
    }

    let mut past_split = bounds.clone();
    let mut future_split = bounds.clone();

    past_split.set_end(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    )));

    future_split.set_start(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    )));

    CutResult::Cut(past_split, future_split)
}

/// Cuts an [`EmptiableRelativeBounds`]
#[must_use]
pub fn cut_emptiable_rel_bounds(
    bounds: &EmptiableRelativeBounds,
    at: Duration,
    cut_type: CutType,
) -> CutResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(non_empty_bounds) = bounds else {
        // Empty bounds can't be cut
        return CutResult::Uncut;
    };

    cut_rel_bounds(non_empty_bounds, at, cut_type)
        .map_cut(|c1, c2| (EmptiableRelativeBounds::from(c1), EmptiableRelativeBounds::from(c2)))
}

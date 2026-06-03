//! Interval intersection

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsInterval,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::abridge::Abridgable;
use crate::intervals::ops::overlap::CanPositionOverlap;
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelInterval,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::IntersectionResult;

/// Capacity to intersect an interval with another
///
/// # Examples
///
/// ## Intersectable intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::IntersectionResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::set_ops::Intersectable;
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 14:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 12:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 18:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.intersect(&second_interval),
///     IntersectionResult::Intersected(AbsBoundPair::new(
///         AbsFiniteBoundPos::new(
///             "2025-01-01 12:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsFiniteBoundPos::new(
///             "2025-01-01 14:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_end_bound(),
///     )),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::IntersectionResult;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::set_ops::Intersectable;
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 12:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 14:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 18:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.intersect(&second_interval),
///     IntersectionResult::Separate,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Intersectable<Rhs = Self> {
    /// Output type
    type Output;

    /// Intersects two intervals using the default overlap rules
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::IntersectionResult;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::set_ops::Intersectable;
    /// let first_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.intersect(&second_interval),
    ///     IntersectionResult::Intersected(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 14:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output>;

    /// Intersects two intervals using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::IntersectionResult;
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::abridge::Abridgable;
    /// # use periodical::intervals::ops::set_ops::Intersectable;
    /// let first_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let intersection_closure = |
    ///     a: &AbsBoundPair,
    ///     b: &AbsBoundPair,
    /// | -> IntersectionResult<AbsBoundPair> {
    ///     // Always abridge intervals
    ///     if let EmptiableAbsBoundPair::Bound(abridged) = a.abridge(b) {
    ///         IntersectionResult::Intersected(abridged)
    ///     } else {
    ///         IntersectionResult::Separate
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     first_interval.intersect_with(&second_interval, intersection_closure),
    ///     IntersectionResult::Intersected(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         ).to_start_bound(),
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         ).to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn intersect_with<F>(&self, rhs: &Rhs, mut f: F) -> IntersectionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> IntersectionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Intersectable<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = AbsInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = AbsInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = RelInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = RelInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelInterval::from)
    }
}

impl Intersectable<AbsBoundPair> for UnboundedInterval {
    type Output = AbsInterval;

    fn intersect(&self, rhs: &AbsBoundPair) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsInterval::from)
    }
}

impl Intersectable<EmptiableAbsBoundPair> for UnboundedInterval {
    type Output = AbsInterval;

    fn intersect(&self, rhs: &EmptiableAbsBoundPair) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsInterval::from)
    }
}

impl Intersectable<AbsInterval> for UnboundedInterval {
    type Output = AbsInterval;

    fn intersect(&self, rhs: &AbsInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsInterval::from)
    }
}

impl Intersectable<BoundedAbsInterval> for UnboundedInterval {
    type Output = AbsInterval;

    fn intersect(&self, rhs: &BoundedAbsInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsInterval::from)
    }
}

impl Intersectable<HalfBoundedAbsInterval> for UnboundedInterval {
    type Output = AbsInterval;

    fn intersect(&self, rhs: &HalfBoundedAbsInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsInterval::from)
    }
}

impl Intersectable<RelBoundPair> for UnboundedInterval {
    type Output = RelInterval;

    fn intersect(&self, rhs: &RelBoundPair) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelInterval::from)
    }
}

impl Intersectable<EmptiableRelBoundPair> for UnboundedInterval {
    type Output = RelInterval;

    fn intersect(&self, rhs: &EmptiableRelBoundPair) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelInterval::from)
    }
}

impl Intersectable<RelInterval> for UnboundedInterval {
    type Output = RelInterval;

    fn intersect(&self, rhs: &RelInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelInterval::from)
    }
}

impl Intersectable<BoundedRelInterval> for UnboundedInterval {
    type Output = RelInterval;

    fn intersect(&self, rhs: &BoundedRelInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelInterval::from)
    }
}

impl Intersectable<HalfBoundedRelInterval> for UnboundedInterval {
    type Output = RelInterval;

    fn intersect(&self, rhs: &HalfBoundedRelInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelInterval::from)
    }
}

impl Intersectable<UnboundedInterval> for UnboundedInterval {
    type Output = EmptyInterval;

    fn intersect(&self, _rhs: &UnboundedInterval) -> IntersectionResult<Self::Output> {
        IntersectionResult::Intersected(EmptyInterval)
    }
}

impl Intersectable<EmptyInterval> for UnboundedInterval {
    type Output = ();

    fn intersect(&self, _rhs: &EmptyInterval) -> IntersectionResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be used in an intersection
        IntersectionResult::Separate
    }
}

impl<Rhs> Intersectable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = EmptyInterval;

    fn intersect(&self, _rhs: &Rhs) -> IntersectionResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be used in an intersection
        IntersectionResult::Separate
    }
}

/// Intersects two [`AbsBoundPair`]
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableAbsBoundPair::Empty`]
#[must_use]
pub fn intersect_abs_bound_pair(a: &AbsBoundPair, b: &AbsBoundPair) -> IntersectionResult<AbsBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`AbsBoundPair`] with an [`EmptiableAbsBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableAbsBoundPair::Empty`]
#[must_use]
pub fn intersect_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> IntersectionResult<AbsBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableAbsBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
#[must_use]
pub fn intersect_emptiable_abs_bound_pair(
    a: &EmptiableAbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> IntersectionResult<EmptiableAbsBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects two [`RelBoundPair`]
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableRelBoundPair::Empty`]
#[must_use]
pub fn intersect_rel_bound_pair(a: &RelBoundPair, b: &RelBoundPair) -> IntersectionResult<RelBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`RelBoundPair`] with an [`EmptiableRelBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableRelBoundPair::Empty`]
#[must_use]
pub fn intersect_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelBoundPair,
    b: &EmptiableRelBoundPair,
) -> IntersectionResult<RelBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableRelBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
#[must_use]
pub fn intersect_emptiable_rel_bound_pair(
    a: &EmptiableRelBoundPair,
    b: &EmptiableRelBoundPair,
) -> IntersectionResult<EmptiableRelBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

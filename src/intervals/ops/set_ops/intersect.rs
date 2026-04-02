//! Interval intersection

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteInterval,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::abridge::Abridgable;
use crate::intervals::ops::overlap::CanPositionOverlap;
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeInterval,
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
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::set_ops::Intersectable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 18:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.intersect(&second_interval),
///     IntersectionResult::Intersected(AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new(
///             "2025-01-01 12:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsoluteFiniteBound::new(
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
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::set_ops::Intersectable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 12:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 14:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBound::new(
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
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::set_ops::Intersectable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.intersect(&second_interval),
    ///     IntersectionResult::Intersected(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
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
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::abridge::Abridgable;
    /// # use periodical::intervals::ops::set_ops::Intersectable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// let intersection_closure = |
    ///     a: &AbsoluteBoundPair,
    ///     b: &AbsoluteBoundPair,
    /// | -> IntersectionResult<AbsoluteBoundPair> {
    ///     // Always abridge intervals
    ///     if let EmptiableAbsoluteBoundPair::Bound(abridged) = a.abridge(b) {
    ///         IntersectionResult::Intersected(abridged)
    ///     } else {
    ///         IntersectionResult::Separate
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     first_interval.intersect_with(&second_interval, intersection_closure),
    ///     IntersectionResult::Intersected(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new_with_inclusivity(
    ///             "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new_with_inclusivity(
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

impl<Rhs> Intersectable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Intersectable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(Self::Output::from)
    }
}

impl<Rhs> Intersectable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl<Rhs> Intersectable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &Rhs) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<AbsoluteBoundPair> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &AbsoluteBoundPair) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &EmptiableAbsoluteBoundPair) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<AbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &AbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &BoundedAbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn intersect(&self, rhs: &HalfBoundedAbsoluteInterval) -> IntersectionResult<Self::Output> {
        intersect_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()).map_intersected(AbsoluteInterval::from)
    }
}

impl Intersectable<RelativeBoundPair> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &RelativeBoundPair) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &EmptiableRelativeBoundPair) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<RelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &RelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &BoundedRelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelativeInterval::from)
    }
}

impl Intersectable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = RelativeInterval;

    fn intersect(&self, rhs: &HalfBoundedRelativeInterval) -> IntersectionResult<Self::Output> {
        intersect_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()).map_intersected(RelativeInterval::from)
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

/// Intersects two [`AbsoluteBoundPair`]
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableAbsoluteBoundPair::Empty`]
#[must_use]
pub fn intersect_abs_bound_pair(a: &AbsoluteBoundPair, b: &AbsoluteBoundPair) -> IntersectionResult<AbsoluteBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableAbsoluteBoundPair::Empty`]
#[must_use]
pub fn intersect_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> IntersectionResult<AbsoluteBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
#[must_use]
pub fn intersect_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> IntersectionResult<EmptiableAbsoluteBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

/// Intersects two [`RelativeBoundPair`]
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableRelativeBoundPair::Empty`]
#[must_use]
pub fn intersect_rel_bound_pair(a: &RelativeBoundPair, b: &RelativeBoundPair) -> IntersectionResult<RelativeBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
///
/// # Panics
///
/// Panics if two strictly overlapping bounds, when abridged, returns
/// [`EmptiableRelativeBoundPair::Empty`]
#[must_use]
pub fn intersect_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> IntersectionResult<RelativeBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(
        a.abridge(b)
            .bound()
            .expect("Two strictly overlapping bounds can always be abridged"),
    )
}

/// Intersects two [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be intersected.
///
/// See [`Intersectable`] for more information.
#[must_use]
pub fn intersect_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> IntersectionResult<EmptiableRelativeBoundPair> {
    if !a.simple_overlaps(b) {
        return IntersectionResult::Separate;
    }

    IntersectionResult::Intersected(a.abridge(b))
}

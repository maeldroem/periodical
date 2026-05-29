//! Interval union

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
use crate::intervals::ops::extend::Extensible;
use crate::intervals::ops::overlap::{CanPositionOverlap, OverlapRule, OverlapRuleSet};
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
use crate::ops::UnionResult;

/// Capacity to unite an interval with another
///
/// # Examples
///
/// ## Unitable intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::UnionResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
/// # use periodical::intervals::ops::set_ops::Unitable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 14:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 12:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 18:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.unite(&second_interval),
///     UnionResult::United(AbsoluteBoundPair::new(
///         AbsoluteFiniteBoundPosition::new(
///             "2025-01-01 08:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsoluteFiniteBoundPosition::new(
///             "2025-01-01 18:00:00[Europe/Oslo]"
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
/// # use periodical::ops::UnionResult;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
/// # use periodical::intervals::ops::set_ops::Unitable;
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 12:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 14:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 18:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     first_interval.unite(&second_interval),
///     UnionResult::Separate,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Unitable<Rhs = Self> {
    /// Output type
    type Output;

    /// Unites two intervals using default overlap rules
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::UnionResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::ops::set_ops::Unitable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.unite(&second_interval),
    ///     UnionResult::United(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 18:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output>;

    /// Unites two intervals using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::ops::UnionResult;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::ops::extend::Extensible;
    /// # use periodical::intervals::ops::set_ops::Unitable;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 18:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let union_closure =
    ///     |a: &AbsoluteBoundPair, b: &AbsoluteBoundPair| -> UnionResult<AbsoluteBoundPair> {
    ///         // Always unite
    ///         UnionResult::United(a.extend(b))
    ///     };
    ///
    /// assert_eq!(
    ///     first_interval.unite_with(&second_interval, union_closure),
    ///     UnionResult::United(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 18:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn unite_with<F>(&self, rhs: &Rhs, mut f: F) -> UnionResult<Self::Output>
    where
        F: FnMut(&Self, &Rhs) -> UnionResult<Self::Output>,
    {
        (f)(self, rhs)
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(AbsoluteInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = AbsoluteInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map_united(AbsoluteInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Unitable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(Self::Output::from)
    }
}

impl<Rhs> Unitable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(RelativeInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = RelativeInterval;

    fn unite(&self, rhs: &Rhs) -> UnionResult<Self::Output> {
        unite_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map_united(RelativeInterval::from)
    }
}

impl<Rhs> Unitable<Rhs> for UnboundedInterval
where
    Rhs: Interval,
{
    type Output = UnboundedInterval;

    fn unite(&self, _rhs: &Rhs) -> UnionResult<Self::Output> {
        UnionResult::United(*self)
    }
}

impl<Rhs> Unitable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = Rhs;

    fn unite(&self, _rhs: &Rhs) -> UnionResult<Self::Output> {
        // An empty interval is nowhere, and therefore cannot be united with anything
        UnionResult::Separate
    }
}

/// Unites two [`AbsoluteBoundPair`]
#[must_use]
pub fn unite_abs_bound_pair(a: &AbsoluteBoundPair, b: &AbsoluteBoundPair) -> UnionResult<AbsoluteBoundPair> {
    // We use the lenient rule set with allow adjacency rule so that "touching"
    // intervals are united together
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> UnionResult<AbsoluteBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableAbsoluteBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> UnionResult<EmptiableAbsoluteBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`RelativeBoundPair`]
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_rel_bound_pair(a: &RelativeBoundPair, b: &RelativeBoundPair) -> UnionResult<RelativeBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> UnionResult<RelativeBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

/// Unites two [`EmptiableRelativeBoundPair`]
///
/// Empty intervals are not positioned in time, and are always "outside",
/// therefore cannot be united.
///
/// See [`Unitable`] for more information.
#[must_use]
pub fn unite_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> UnionResult<EmptiableRelativeBoundPair> {
    if !a.overlaps(b, OverlapRuleSet::Lenient, &[OverlapRule::AllowAdjacency]) {
        return UnionResult::Separate;
    }

    UnionResult::United(a.extend(b))
}

//! Removal of overlaps between overlapping intervals
//!
//! Given two intervals, adjusts the first interval so that no overlap exists
//! between the two intervals. If the two intervals are not overlapping, the
//! operation produces an error.

use std::error::Error;
use std::fmt::Display;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use super::cut::{CutResult, CutType, Cuttable};
use super::overlap::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity, Interval};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Result of an overlap removal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum OverlapRemovalResult<T> {
    /// Resulted in a single element
    ///
    /// An empty interval counts as one too.
    Single(T),
    /// Resulted in two split elements
    Split(T, T),
}

impl<T> OverlapRemovalResult<T> {
    /// Returns whether it is of the [`Single`](OverlapRemovalResult::Single)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap::OverlapRemovalResult;
    /// assert!(OverlapRemovalResult::<()>::Single(()).is_single());
    /// assert!(!OverlapRemovalResult::<()>::Split((), ()).is_single());
    /// ```
    #[must_use]
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Returns whether it is of the [`Split`](OverlapRemovalResult::Split)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap::OverlapRemovalResult;
    /// assert!(OverlapRemovalResult::<()>::Split((), ()).is_split());
    /// assert!(!OverlapRemovalResult::<()>::Single(()).is_split());
    /// ```
    #[must_use]
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Returns the content of the [`Single`](OverlapRemovalResult::Single)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Single`](OverlapRemovalResult::Single) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap::OverlapRemovalResult;
    /// assert_eq!(OverlapRemovalResult::<u8>::Single(10).single(), Some(10));
    /// assert_eq!(OverlapRemovalResult::<u8>::Split(10, 20).single(), None);
    /// ```
    #[must_use]
    pub fn single(self) -> Option<T> {
        match self {
            Self::Single(s) => Some(s),
            Self::Split(..) => None,
        }
    }

    /// Returns the content of the [`Split`](OverlapRemovalResult::Split)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Split`](OverlapRemovalResult::Split) variant in an [`Option`]. If
    /// Instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap::OverlapRemovalResult;
    /// assert_eq!(
    ///     OverlapRemovalResult::<u8>::Split(10, 20).split(),
    ///     Some((10, 20))
    /// );
    /// assert_eq!(OverlapRemovalResult::<u8>::Single(10).split(), None);
    /// ```
    #[must_use]
    pub fn split(self) -> Option<(T, T)> {
        match self {
            Self::Single(_) => None,
            Self::Split(s1, s2) => Some((s1, s2)),
        }
    }

    /// Maps the contents of the variants
    ///
    /// Uses a closure that describes the transformation from `T` to `U`, used
    /// for each element in the enum.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::remove_overlap::OverlapRemovalResult;
    /// assert_eq!(
    ///     OverlapRemovalResult::<u8>::Single(10).map(|x| x * 2),
    ///     OverlapRemovalResult::<u8>::Single(20),
    /// );
    /// assert_eq!(
    ///     OverlapRemovalResult::<u8>::Split(10, 20).map(|x| x * 2),
    ///     OverlapRemovalResult::<u8>::Split(20, 40),
    /// );
    /// ```
    #[must_use]
    pub fn map<F, U>(self, mut f: F) -> OverlapRemovalResult<U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Self::Single(s) => OverlapRemovalResult::Single((f)(s)),
            Self::Split(s1, s2) => OverlapRemovalResult::Split((f)(s1), (f)(s2)),
        }
    }
}

/// No overlap was found between the intervals when using [`OverlapRemovable`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OverlapRemovalNoOverlapFoundError;

impl Display for OverlapRemovalNoOverlapFoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "No overlap was found between the intervals")
    }
}

impl Error for OverlapRemovalNoOverlapFoundError {}

/// Capacity to remove overlap between two intervals that strictly overlap
pub trait OverlapRemovable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns a result that contains a version of `self` that no longer has a
    /// strict overlap with the given `rhs`
    ///
    /// # Errors
    ///
    /// If the given bounds don't overlap, this method returns
    /// [`OverlapRemovalNoOverlapFoundError`].
    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError>;
}

impl<Rhs> OverlapRemovable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteBoundPair;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeBoundPair;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<AbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &AbsoluteBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableAbsoluteBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<AbsoluteInterval> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &AbsoluteInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableAbsoluteInterval> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableAbsoluteInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<BoundedAbsoluteInterval> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &BoundedAbsoluteInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<HalfBoundedAbsoluteInterval> for UnboundedInterval {
    type Output = EmptiableAbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &HalfBoundedAbsoluteInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<RelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &RelativeBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableRelativeBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<RelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &RelativeInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableRelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableRelativeInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<BoundedRelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &BoundedRelativeInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<HalfBoundedRelativeInterval> for UnboundedInterval {
    type Output = EmptiableRelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &HalfBoundedRelativeInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<UnboundedInterval> for UnboundedInterval {
    type Output = EmptyInterval;

    fn remove_overlap(
        &self,
        _rhs: &UnboundedInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        Ok(OverlapRemovalResult::Single(EmptyInterval))
    }
}

impl OverlapRemovable<EmptyInterval> for UnboundedInterval {
    type Output = UnboundedInterval;

    fn remove_overlap(
        &self,
        _rhs: &EmptyInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        Ok(OverlapRemovalResult::Single(*self))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = EmptyInterval;

    fn remove_overlap(
        &self,
        _rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        Ok(OverlapRemovalResult::Single(*self))
    }
}

/// Removes overlap between two overlapping [`AbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &AbsoluteBoundPair,
) -> Result<OverlapRemovalResult<EmptiableAbsoluteBoundPair>, OverlapRemovalNoOverlapFoundError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(disambiguated_overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match disambiguated_overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore | Dop::OutsideAfter => Err(OverlapRemovalNoOverlapFoundError),
        Dop::EndsOnStart => {
            let AbsoluteEndBound::Finite(mut finite_bound) = a.abs_end() else {
                unreachable!(
                    "If the end of the reference bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OnStart`"
                );
            };

            // Since `OnStart` only happens when two inclusive bounds are equal (since we
            // are using the strict rule set) we can just set the end
            // inclusivity to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(
                AbsoluteBoundPair::new(a.abs_start(), AbsoluteEndBound::from(finite_bound)),
            )))
        },
        Dop::StartsOnEnd => {
            let AbsoluteStartBound::Finite(mut finite_bound) = a.abs_start() else {
                unreachable!(
                    "If the start of the reference bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OnEnd`"
                );
            };

            // Since `OnEnd` only happens when two inclusive bounds are equal (since we are
            // using the strict rule set) we can just set the start inclusivity
            // to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(
                AbsoluteBoundPair::new(AbsoluteStartBound::from(finite_bound), a.abs_end()),
            )))
        },
        Dop::CrossesStart => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(
                AbsoluteBoundPair::new(a.abs_start(), new_end),
            )))
        },
        Dop::CrossesEnd => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(
                AbsoluteBoundPair::new(new_start, a.abs_end()),
            )))
        },
        Dop::Equal | Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd => {
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty))
        },
        Dop::ContainsAndSameStart => Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(
            remove_end_overlap_abs(a, b),
        ))),
        Dop::ContainsAndSameEnd => Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(
            remove_start_overlap_abs(a, b),
        ))),
        Dop::Contains => Ok(OverlapRemovalResult::Split(
            EmptiableAbsoluteBoundPair::from(remove_start_overlap_abs(a, b)),
            EmptiableAbsoluteBoundPair::from(remove_end_overlap_abs(a, b)),
        )),
    }
}

/// Removes the overlap of the two given [`AbsoluteBoundPair`] with
/// a [`ContainsAndSameEnd`](DisambiguatedOverlapPosition::ContainsAndSameEnd)
/// overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_start_overlap_abs(a: &AbsoluteBoundPair, b: &AbsoluteBoundPair) -> AbsoluteBoundPair {
    let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
        unreachable!(
            "If the start of the compared bounds is `InfiniteStart`, then it is impossible that the overlap was \
             `ContainsAndSameEnd`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound.time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` start at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsoluteFiniteBound::new(finite_bound.time());

            AbsoluteBoundPair::new(AbsoluteStartBound::from(point), AbsoluteEndBound::from(point))
        },
        CutResult::Cut(new_a, _) => new_a,
    }
}

/// Removes the overlap of the two given [`AbsoluteBoundPair`] with
/// an [`ContainsAndSameStart`](DisambiguatedOverlapPosition::ContainsAndSameStart) overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_end_overlap_abs(a: &AbsoluteBoundPair, b: &AbsoluteBoundPair) -> AbsoluteBoundPair {
    let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
        unreachable!(
            "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap was \
             `ContainsAndSameStart`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound.time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` ends at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsoluteFiniteBound::new(finite_bound.time());

            AbsoluteBoundPair::new(AbsoluteStartBound::from(point), AbsoluteEndBound::from(point))
        },
        CutResult::Cut(_, new_a) => new_a,
    }
}

/// Removes the overlap of an [`AbsoluteBoundPair`] with an
/// [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> Result<OverlapRemovalResult<EmptiableAbsoluteBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableAbsoluteBoundPair::Bound(b_abs_bound_pair) = b else {
        return Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::from(
            a.clone(),
        )));
    };

    remove_overlap_abs_bound_pair(a, b_abs_bound_pair)
}

/// Removes the overlap of two [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_emptiable_abs_bound_pair(
    a: &EmptiableAbsoluteBoundPair,
    b: &EmptiableAbsoluteBoundPair,
) -> Result<OverlapRemovalResult<EmptiableAbsoluteBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableAbsoluteBoundPair::Bound(a_abs_bound_pair) = a else {
        return Ok(OverlapRemovalResult::Single(a.clone()));
    };

    remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(a_abs_bound_pair, b)
}

/// Removes overlap between two overlapping [`RelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &RelativeBoundPair,
) -> Result<OverlapRemovalResult<EmptiableRelativeBoundPair>, OverlapRemovalNoOverlapFoundError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(disambiguated_overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match disambiguated_overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore | Dop::OutsideAfter => Err(OverlapRemovalNoOverlapFoundError),
        Dop::EndsOnStart => {
            let RelativeEndBound::Finite(mut finite_bound) = a.rel_end() else {
                unreachable!(
                    "If the end of the reference bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OnStart`"
                );
            };

            // Since `OnStart` only happens when two inclusive bounds are equal (since we
            // are using the strict rule set) we can just set the end
            // inclusivity to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::from(
                RelativeBoundPair::new(a.rel_start(), RelativeEndBound::from(finite_bound)),
            )))
        },
        Dop::StartsOnEnd => {
            let RelativeStartBound::Finite(mut finite_bound) = a.rel_start() else {
                unreachable!(
                    "If the start of the reference bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OnEnd`"
                );
            };

            // Since `OnEnd` only happens when two inclusive bounds are equal (since we are
            // using the strict rule set) we can just set the start inclusivity
            // to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::from(
                RelativeBoundPair::new(RelativeStartBound::from(finite_bound), a.rel_end()),
            )))
        },
        Dop::CrossesStart => {
            let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end = RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::from(
                RelativeBoundPair::new(a.rel_start(), new_end),
            )))
        },
        Dop::CrossesEnd => {
            let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start = RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::from(
                RelativeBoundPair::new(new_start, a.rel_end()),
            )))
        },
        Dop::Equal | Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd => {
            Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::Empty))
        },
        Dop::ContainsAndSameStart => Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::from(
            remove_end_overlap_rel(a, b),
        ))),
        Dop::ContainsAndSameEnd => Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::from(
            remove_start_overlap_rel(a, b),
        ))),
        Dop::Contains => Ok(OverlapRemovalResult::Split(
            EmptiableRelativeBoundPair::from(remove_start_overlap_rel(a, b)),
            EmptiableRelativeBoundPair::from(remove_end_overlap_rel(a, b)),
        )),
    }
}

/// Removes the overlap of the two given [`RelativeBoundPair`] with
/// an [`ContainsAndSameEnd`](DisambiguatedOverlapPosition::ContainsAndSameEnd)
/// overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_start_overlap_rel(a: &RelativeBoundPair, b: &RelativeBoundPair) -> RelativeBoundPair {
    let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
        unreachable!(
            "If the start of the compared bounds is `InfiniteStart`, then it is impossible that the overlap was \
             `ContainsAndSameEnd`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound.offset(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` start at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = RelativeFiniteBound::new(finite_bound.offset());

            RelativeBoundPair::new(RelativeStartBound::from(point), RelativeEndBound::from(point))
        },
        CutResult::Cut(new_a, _) => new_a,
    }
}

/// Removes the overlap of the two given [`RelativeBoundPair`] with
/// an [`ContainsAndSameStart`](DisambiguatedOverlapPosition::ContainsAndSameStart) overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_end_overlap_rel(a: &RelativeBoundPair, b: &RelativeBoundPair) -> RelativeBoundPair {
    let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
        unreachable!(
            "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap was \
             `ContainsAndSameStart`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound.offset(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` ends at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = RelativeFiniteBound::new(finite_bound.offset());

            RelativeBoundPair::new(RelativeStartBound::from(point), RelativeEndBound::from(point))
        },
        CutResult::Cut(_, new_a) => new_a,
    }
}

/// Removes the overlap of an [`RelativeBoundPair`] with an
/// [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> Result<OverlapRemovalResult<EmptiableRelativeBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableRelativeBoundPair::Bound(b_rel_bound_pair) = b else {
        return Ok(OverlapRemovalResult::Single(EmptiableRelativeBoundPair::from(
            a.clone(),
        )));
    };

    remove_overlap_rel_bound_pair(a, b_rel_bound_pair)
}

/// Removes the overlap of two [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_emptiable_rel_bound_pair(
    a: &EmptiableRelativeBoundPair,
    b: &EmptiableRelativeBoundPair,
) -> Result<OverlapRemovalResult<EmptiableRelativeBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableRelativeBoundPair::Bound(a_rel_bound_pair) = a else {
        return Ok(OverlapRemovalResult::Single(a.clone()));
    };

    remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(a_rel_bound_pair, b)
}

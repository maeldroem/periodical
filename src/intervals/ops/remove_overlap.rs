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
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity, Interval};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
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

impl<Rhs> OverlapRemovable<Rhs> for AbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsBoundPair;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableAbsBoundPair
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = Self;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(self, &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for AbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

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

impl<Rhs> OverlapRemovable<Rhs> for EmptiableAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
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

impl<Rhs> OverlapRemovable<Rhs> for BoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for HalfBoundedAbsInterval
where
    Rhs: HasEmptiableAbsBoundPair,
{
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for RelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelBoundPair;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableRelBoundPair
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = Self;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for RelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
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

impl<Rhs> OverlapRemovable<Rhs> for BoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for HalfBoundedRelInterval
where
    Rhs: HasEmptiableRelBoundPair,
{
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &Rhs,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<AbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &AbsBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableAbsBoundPair> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableAbsBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(
            &self.abs_bound_pair(),
            &rhs.emptiable_abs_bound_pair(),
        )
        .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<AbsInterval> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &AbsInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableAbsInterval> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableAbsInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<BoundedAbsInterval> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &BoundedAbsInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<HalfBoundedAbsInterval> for UnboundedInterval {
    type Output = EmptiableAbsInterval;

    fn remove_overlap(
        &self,
        rhs: &HalfBoundedAbsInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<RelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &RelBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableRelBoundPair> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableRelBoundPair,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<RelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &RelInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<EmptiableRelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableRelInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(
            &self.rel_bound_pair(),
            &rhs.emptiable_rel_bound_pair(),
        )
        .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<BoundedRelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &BoundedRelInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalNoOverlapFoundError> {
        remove_overlap_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair())
            .map(|overlap_removal_res| overlap_removal_res.map(Self::Output::from))
    }
}

impl OverlapRemovable<HalfBoundedRelInterval> for UnboundedInterval {
    type Output = EmptiableRelInterval;

    fn remove_overlap(
        &self,
        rhs: &HalfBoundedRelInterval,
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

/// Removes overlap between two overlapping [`AbsBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_abs_bound_pair(
    a: &AbsBoundPair,
    b: &AbsBoundPair,
) -> Result<OverlapRemovalResult<EmptiableAbsBoundPair>, OverlapRemovalNoOverlapFoundError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(disambiguated_overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match disambiguated_overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore | Dop::OutsideAfter => Err(OverlapRemovalNoOverlapFoundError),
        Dop::EndsOnStart => {
            let AbsEndBound::Finite(mut finite_bound_position) = a.abs_end() else {
                unreachable!(
                    "If the end of the reference bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OnStart`"
                );
            };

            // Since `OnStart` only happens when two inclusive bounds are equal (since we
            // are using the strict rule set) we can just set the end
            // inclusivity to exclusive.
            finite_bound_position
                .pos_mut()
                .set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(
                AbsBoundPair::new(a.abs_start(), AbsEndBound::from(finite_bound_position)).to_emptiable(),
            ))
        },
        Dop::StartsOnEnd => {
            let AbsStartBound::Finite(mut finite_bound_position) = a.abs_start() else {
                unreachable!(
                    "If the start of the reference bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OnEnd`"
                );
            };

            // Since `OnEnd` only happens when two inclusive bounds are equal (since we are
            // using the strict rule set) we can just set the start inclusivity
            // to exclusive.
            finite_bound_position
                .pos_mut()
                .set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(
                AbsBoundPair::new(AbsStartBound::from(finite_bound_position), a.abs_end()).to_emptiable(),
            ))
        },
        Dop::CrossesStart => {
            let AbsStartBound::Finite(finite_bound_position) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(),
            )
            .to_end_bound();

            Ok(OverlapRemovalResult::Single(
                AbsBoundPair::new(a.abs_start(), new_end).to_emptiable(),
            ))
        },
        Dop::CrossesEnd => {
            let AbsEndBound::Finite(finite_bound_position) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start = AbsFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().time(),
                finite_bound_position.pos().inclusivity().opposite(),
            )
            .to_start_bound();

            Ok(OverlapRemovalResult::Single(
                AbsBoundPair::new(new_start, a.abs_end()).to_emptiable(),
            ))
        },
        Dop::Equal | Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd => {
            Ok(OverlapRemovalResult::Single(EmptiableAbsBoundPair::Empty))
        },
        Dop::ContainsAndSameStart => Ok(OverlapRemovalResult::Single(
            remove_end_overlap_abs(a, b).to_emptiable(),
        )),
        Dop::ContainsAndSameEnd => Ok(OverlapRemovalResult::Single(
            remove_start_overlap_abs(a, b).to_emptiable(),
        )),
        Dop::Contains => Ok(OverlapRemovalResult::Split(
            remove_start_overlap_abs(a, b).to_emptiable(),
            remove_end_overlap_abs(a, b).to_emptiable(),
        )),
    }
}

/// Removes the overlap of the two given [`AbsBoundPair`] with
/// a [`ContainsAndSameEnd`](DisambiguatedOverlapPosition::ContainsAndSameEnd)
/// overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_start_overlap_abs(a: &AbsBoundPair, b: &AbsBoundPair) -> AbsBoundPair {
    let AbsStartBound::Finite(finite_bound_position) = b.abs_start() else {
        unreachable!(
            "If the start of the compared bounds is `InfiniteStart`, then it is impossible that the overlap was \
             `ContainsAndSameEnd`"
        );
    };

    let cut_type = match finite_bound_position.pos().inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound_position.pos().time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` start at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsFiniteBoundPos::new(finite_bound_position.pos().time());

            AbsBoundPair::new(AbsStartBound::from(point), AbsEndBound::from(point))
        },
        CutResult::Cut(new_a, _) => new_a,
    }
}

/// Removes the overlap of the two given [`AbsBoundPair`] with
/// an [`ContainsAndSameStart`](DisambiguatedOverlapPosition::ContainsAndSameStart) overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_end_overlap_abs(a: &AbsBoundPair, b: &AbsBoundPair) -> AbsBoundPair {
    let AbsEndBound::Finite(finite_bound_position) = b.abs_end() else {
        unreachable!(
            "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap was \
             `ContainsAndSameStart`"
        );
    };

    let cut_type = match finite_bound_position.pos().inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound_position.pos().time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` ends at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsFiniteBoundPos::new(finite_bound_position.pos().time());

            AbsBoundPair::new(AbsStartBound::from(point), AbsEndBound::from(point))
        },
        CutResult::Cut(_, new_a) => new_a,
    }
}

/// Removes the overlap of an [`AbsBoundPair`] with an
/// [`EmptiableAbsBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(
    a: &AbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> Result<OverlapRemovalResult<EmptiableAbsBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableAbsBoundPair::Bound(b_abs_bound_pair) = b else {
        return Ok(OverlapRemovalResult::Single(EmptiableAbsBoundPair::from(a.clone())));
    };

    remove_overlap_abs_bound_pair(a, b_abs_bound_pair)
}

/// Removes the overlap of two [`EmptiableAbsBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_emptiable_abs_bound_pair(
    a: &EmptiableAbsBoundPair,
    b: &EmptiableAbsBoundPair,
) -> Result<OverlapRemovalResult<EmptiableAbsBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableAbsBoundPair::Bound(a_abs_bound_pair) = a else {
        return Ok(OverlapRemovalResult::Single(a.clone()));
    };

    remove_overlap_abs_bound_pair_with_emptiable_abs_bound_pair(a_abs_bound_pair, b)
}

/// Removes overlap between two overlapping [`RelBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_rel_bound_pair(
    a: &RelBoundPair,
    b: &RelBoundPair,
) -> Result<OverlapRemovalResult<EmptiableRelBoundPair>, OverlapRemovalNoOverlapFoundError> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(disambiguated_overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match disambiguated_overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore | Dop::OutsideAfter => Err(OverlapRemovalNoOverlapFoundError),
        Dop::EndsOnStart => {
            let RelEndBound::Finite(mut finite_bound_position) = a.rel_end() else {
                unreachable!(
                    "If the end of the reference bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `OnStart`"
                );
            };

            // Since `OnStart` only happens when two inclusive bounds are equal (since we
            // are using the strict rule set) we can just set the end
            // inclusivity to exclusive.
            finite_bound_position
                .pos_mut()
                .set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(
                RelBoundPair::new(a.rel_start(), RelEndBound::from(finite_bound_position)).to_emptiable(),
            ))
        },
        Dop::StartsOnEnd => {
            let RelStartBound::Finite(mut finite_bound_position) = a.rel_start() else {
                unreachable!(
                    "If the start of the reference bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `OnEnd`"
                );
            };

            // Since `OnEnd` only happens when two inclusive bounds are equal (since we are
            // using the strict rule set) we can just set the start inclusivity
            // to exclusive.
            finite_bound_position
                .pos_mut()
                .set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(
                RelBoundPair::new(RelStartBound::from(finite_bound_position), a.rel_end()).to_emptiable(),
            ))
        },
        Dop::CrossesStart => {
            let RelStartBound::Finite(finite_bound_position) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, then it is impossible that the overlap \
                     was `CrossesStart`"
                );
            };

            let new_end = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(),
            )
            .to_end_bound();

            Ok(OverlapRemovalResult::Single(
                RelBoundPair::new(a.rel_start(), new_end).to_emptiable(),
            ))
        },
        Dop::CrossesEnd => {
            let RelEndBound::Finite(finite_bound_position) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap \
                     was `CrossesEnd`"
                );
            };

            let new_start = RelFiniteBoundPos::new_with_inclusivity(
                finite_bound_position.pos().offset(),
                finite_bound_position.pos().inclusivity().opposite(),
            )
            .to_start_bound();

            Ok(OverlapRemovalResult::Single(
                RelBoundPair::new(new_start, a.rel_end()).to_emptiable(),
            ))
        },
        Dop::Equal | Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd => {
            Ok(OverlapRemovalResult::Single(EmptiableRelBoundPair::Empty))
        },
        Dop::ContainsAndSameStart => Ok(OverlapRemovalResult::Single(
            remove_end_overlap_rel(a, b).to_emptiable(),
        )),
        Dop::ContainsAndSameEnd => Ok(OverlapRemovalResult::Single(
            remove_start_overlap_rel(a, b).to_emptiable(),
        )),
        Dop::Contains => Ok(OverlapRemovalResult::Split(
            remove_start_overlap_rel(a, b).to_emptiable(),
            remove_end_overlap_rel(a, b).to_emptiable(),
        )),
    }
}

/// Removes the overlap of the two given [`RelBoundPair`] with
/// an [`ContainsAndSameEnd`](DisambiguatedOverlapPosition::ContainsAndSameEnd)
/// overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_start_overlap_rel(a: &RelBoundPair, b: &RelBoundPair) -> RelBoundPair {
    let RelStartBound::Finite(finite_bound_position) = b.rel_start() else {
        unreachable!(
            "If the start of the compared bounds is `InfiniteStart`, then it is impossible that the overlap was \
             `ContainsAndSameEnd`"
        );
    };

    let cut_type = match finite_bound_position.pos().inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound_position.pos().offset(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` start at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = RelFiniteBoundPos::new(finite_bound_position.pos().offset());

            RelBoundPair::new(RelStartBound::from(point), RelEndBound::from(point))
        },
        CutResult::Cut(new_a, _) => new_a,
    }
}

/// Removes the overlap of the two given [`RelBoundPair`] with
/// an [`ContainsAndSameStart`](DisambiguatedOverlapPosition::ContainsAndSameStart) overlap
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
#[must_use]
pub fn remove_end_overlap_rel(a: &RelBoundPair, b: &RelBoundPair) -> RelBoundPair {
    let RelEndBound::Finite(finite_bound_position) = b.rel_end() else {
        unreachable!(
            "If the end of the compared bounds is `InfiniteFuture`, then it is impossible that the overlap was \
             `ContainsAndSameStart`"
        );
    };

    let cut_type = match finite_bound_position.pos().inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive),
        BoundInclusivity::Exclusive => CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    };

    match a.cut_at(finite_bound_position.pos().offset(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` ends at the same time as `b` does, but b is exclusive on this
            // point whereas `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = RelFiniteBoundPos::new(finite_bound_position.pos().offset());

            RelBoundPair::new(RelStartBound::from(point), RelEndBound::from(point))
        },
        CutResult::Cut(_, new_a) => new_a,
    }
}

/// Removes the overlap of an [`RelBoundPair`] with an
/// [`EmptiableRelBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(
    a: &RelBoundPair,
    b: &EmptiableRelBoundPair,
) -> Result<OverlapRemovalResult<EmptiableRelBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableRelBoundPair::Bound(b_rel_bound_pair) = b else {
        return Ok(OverlapRemovalResult::Single(EmptiableRelBoundPair::from(a.clone())));
    };

    remove_overlap_rel_bound_pair(a, b_rel_bound_pair)
}

/// Removes the overlap of two [`EmptiableRelBoundPair`]
///
/// See [module documentation](crate::intervals::ops::remove_overlap) for more
/// info.
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns
/// [`OverlapRemovalNoOverlapFoundError`].
pub fn remove_overlap_emptiable_rel_bound_pair(
    a: &EmptiableRelBoundPair,
    b: &EmptiableRelBoundPair,
) -> Result<OverlapRemovalResult<EmptiableRelBoundPair>, OverlapRemovalNoOverlapFoundError> {
    let EmptiableRelBoundPair::Bound(a_rel_bound_pair) = a else {
        return Ok(OverlapRemovalResult::Single(a.clone()));
    };

    remove_overlap_rel_bound_pair_with_emptiable_rel_bound_pair(a_rel_bound_pair, b)
}

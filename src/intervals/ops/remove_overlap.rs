//! Removal of overlaps between overlapping intervals

use super::cut::{CutResult, CutType, Cuttable};
use super::overlap_position::{CanPositionOverlap, DisambiguatedOverlapPosition, OverlapRuleSet};
use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::{BoundInclusivity, Interval};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, RelativeBounds, RelativeEndBound, RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};

/// Result of an overlap removal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapRemovalResult<T> {
    Single(T),
    Split(T, T),
}

impl<T> OverlapRemovalResult<T> {
    /// Returns whether the [`OverlapRemovalResult`] is of the [`Single`](OverlapRemovalResult::Single) variant
    #[must_use]
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Returns whether the [`OverlapRemovalResult`] is of the [`Split`](OverlapRemovalResult::Split) variant
    #[must_use]
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Maps the contents of the variants
    ///
    /// Uses a closure that describes the transformation from `T` to `U`, used for each element in the enum.
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapRemovalErr {
    NoOverlap,
}

/// Capacity to remove overlap between two intervals that strictly overlap
pub trait OverlapRemovable<Rhs = Self> {
    /// Output type
    type Output;

    /// Returns a result that contains a version of `self` that no longer has a strict overlap with the given `rhs`
    ///
    /// # Errors
    ///
    /// If the given bounds don't overlap, this method returns [`OverlapRemovalErr::NoOverlap`].
    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr>;
}

impl<Rhs> OverlapRemovable<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = EmptiableAbsoluteBounds;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_abs_bounds_with_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_abs_bounds(self, &rhs.emptiable_abs_bounds())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = Self;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for ClosedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for HalfOpenAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Output = AbsoluteInterval;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_abs_bounds(&self.emptiable_abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = EmptiableRelativeBounds;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_rel_bounds_with_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_rel_bounds(self, &rhs.emptiable_rel_bounds())
    }
}

impl<Rhs> OverlapRemovable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = Self;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for ClosedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for HalfOpenRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Output = RelativeInterval;

    fn remove_overlap(&self, rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_emptiable_rel_bounds(&self.emptiable_rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl OverlapRemovable<AbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap(&self, rhs: &AbsoluteBounds) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl OverlapRemovable<EmptiableAbsoluteBounds> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableAbsoluteBounds,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl OverlapRemovable<AbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap(&self, rhs: &AbsoluteInterval) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_abs_bounds_with_emptiable_abs_bounds(&self.abs_bounds(), &rhs.emptiable_abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl OverlapRemovable<ClosedAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &ClosedAbsoluteInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl OverlapRemovable<HalfOpenAbsoluteInterval> for OpenInterval {
    type Output = AbsoluteInterval;

    fn remove_overlap(
        &self,
        rhs: &HalfOpenAbsoluteInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_abs_bounds(&self.abs_bounds(), &rhs.abs_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(AbsoluteInterval::from))
    }
}

impl OverlapRemovable<RelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap(&self, rhs: &RelativeBounds) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl OverlapRemovable<EmptiableRelativeBounds> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &EmptiableRelativeBounds,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl OverlapRemovable<RelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap(&self, rhs: &RelativeInterval) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_rel_bounds_with_emptiable_rel_bounds(&self.rel_bounds(), &rhs.emptiable_rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl OverlapRemovable<ClosedRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &ClosedRelativeInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl OverlapRemovable<HalfOpenRelativeInterval> for OpenInterval {
    type Output = RelativeInterval;

    fn remove_overlap(
        &self,
        rhs: &HalfOpenRelativeInterval,
    ) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        remove_overlap_rel_bounds(&self.rel_bounds(), &rhs.rel_bounds())
            .map(|overlap_removal_res| overlap_removal_res.map(RelativeInterval::from))
    }
}

impl OverlapRemovable<OpenInterval> for OpenInterval {
    type Output = EmptyInterval;

    fn remove_overlap(&self, _rhs: &OpenInterval) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        Ok(OverlapRemovalResult::Single(EmptyInterval))
    }
}

impl OverlapRemovable<EmptyInterval> for OpenInterval {
    type Output = OpenInterval;

    fn remove_overlap(&self, _rhs: &EmptyInterval) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        Ok(OverlapRemovalResult::Single(self.clone()))
    }
}

impl<Rhs> OverlapRemovable<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Output = EmptyInterval;

    fn remove_overlap(&self, _rhs: &Rhs) -> Result<OverlapRemovalResult<Self::Output>, OverlapRemovalErr> {
        Ok(OverlapRemovalResult::Single(self.clone()))
    }
}

/// Removes overlap between two overlapping [`AbsoluteBounds`]
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns [`OverlapRemovalErr::NoOverlap`].
pub fn remove_overlap_abs_bounds(
    a: &AbsoluteBounds,
    b: &AbsoluteBounds,
) -> Result<OverlapRemovalResult<EmptiableAbsoluteBounds>, OverlapRemovalErr> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(disambiguated_overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match disambiguated_overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore | Dop::OutsideAfter => Err(OverlapRemovalErr::NoOverlap),
        Dop::OnStart => {
            let AbsoluteEndBound::Finite(mut finite_bound) = a.abs_end() else {
                unreachable!(
                    "If the end of the reference bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OnStart`"
                );
            };

            // Since `OnStart` only happens when two inclusive bounds are equal (since we are using the strict rule set)
            // we can just set the end inclusivity to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::from(
                AbsoluteBounds::new(a.abs_start(), AbsoluteEndBound::from(finite_bound)),
            )))
        },
        Dop::OnEnd => {
            let AbsoluteStartBound::Finite(mut finite_bound) = a.abs_start() else {
                unreachable!(
                    "If the start of the reference bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OnEnd`"
                );
            };

            // Since `OnEnd` only happens when two inclusive bounds are equal (since we are using the strict rule set)
            // we can just set the start inclusivity to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::from(
                AbsoluteBounds::new(AbsoluteStartBound::from(finite_bound), a.abs_end()),
            )))
        },
        Dop::CrossesStart => {
            let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `CrossesStart`"
                );
            };

            let new_end = AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::from(
                AbsoluteBounds::new(a.abs_start(), new_end),
            )))
        },
        Dop::CrossesEnd => {
            let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `CrossesEnd`"
                );
            };

            let new_start = AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                finite_bound.time(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::from(
                AbsoluteBounds::new(new_start, a.abs_end()),
            )))
        },
        Dop::Equal | Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd => {
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty))
        },
        Dop::ContainsAndSameStart => Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::from(
            remove_end_overlap_abs(a, b),
        ))),
        Dop::ContainsAndSameEnd => Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::from(
            remove_start_overlap_abs(a, b),
        ))),
        Dop::Contains => Ok(OverlapRemovalResult::Split(
            EmptiableAbsoluteBounds::from(remove_start_overlap_abs(a, b)),
            EmptiableAbsoluteBounds::from(remove_end_overlap_abs(a, b)),
        )),
    }
}

/// Removes the overlap of the two given [`AbsoluteBounds`] with
/// an [`ContainsAndSameEnd`](OverlapPosition::ContainsAndSameEnd) overlap
#[must_use]
pub fn remove_start_overlap_abs(a: &AbsoluteBounds, b: &AbsoluteBounds) -> AbsoluteBounds {
    let AbsoluteStartBound::Finite(finite_bound) = b.abs_start() else {
        unreachable!(
            "If the start of the compared bounds is `InfiniteStart`, \
            then it is impossible that the overlap was `ContainsAndSameEnd`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::InclusiveBoth,
        BoundInclusivity::Exclusive => CutType::ExclusiveBoth,
    };

    match a.cut_at(finite_bound.time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` start at the same time as `b` does, but b is exclusive on this point whereas
            // `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsoluteFiniteBound::new(finite_bound.time());

            AbsoluteBounds::new(AbsoluteStartBound::from(point), AbsoluteEndBound::from(point))
        },
        CutResult::Cut(new_a, _) => new_a,
    }
}

/// Removes the overlap of the two given [`AbsoluteBounds`] with
/// an [`ContainsAndSameStart`](OverlapPosition::ContainsAndSameStart) overlap
#[must_use]
pub fn remove_end_overlap_abs(a: &AbsoluteBounds, b: &AbsoluteBounds) -> AbsoluteBounds {
    let AbsoluteEndBound::Finite(finite_bound) = b.abs_end() else {
        unreachable!(
            "If the end of the compared bounds is `InfiniteFuture`, \
            then it is impossible that the overlap was `ContainsAndSameStart`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::InclusiveBoth,
        BoundInclusivity::Exclusive => CutType::ExclusiveBoth,
    };

    match a.cut_at(finite_bound.time(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` ends at the same time as `b` does, but b is exclusive on this point whereas
            // `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = AbsoluteFiniteBound::new(finite_bound.time());

            AbsoluteBounds::new(AbsoluteStartBound::from(point), AbsoluteEndBound::from(point))
        },
        CutResult::Cut(_, new_a) => new_a,
    }
}

/// Removes the overlap of an [`AbsoluteBounds`] with an [`EmptiableAbsoluteBounds`]
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns [`OverlapRemovalErr::NoOverlap`].
pub fn remove_overlap_abs_bounds_with_emptiable_abs_bounds(
    a: &AbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<OverlapRemovalResult<EmptiableAbsoluteBounds>, OverlapRemovalErr> {
    let EmptiableAbsoluteBounds::Bound(b_abs_bounds) = b else {
        return Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::from(a.clone())));
    };

    remove_overlap_abs_bounds(a, b_abs_bounds)
}

/// Removes the overlap of two [`EmptiableAbsoluteBounds`]
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns [`OverlapRemovalErr::NoOverlap`].
pub fn remove_overlap_emptiable_abs_bounds(
    a: &EmptiableAbsoluteBounds,
    b: &EmptiableAbsoluteBounds,
) -> Result<OverlapRemovalResult<EmptiableAbsoluteBounds>, OverlapRemovalErr> {
    let EmptiableAbsoluteBounds::Bound(a_abs_bounds) = a else {
        return Ok(OverlapRemovalResult::Single(a.clone()));
    };

    remove_overlap_abs_bounds_with_emptiable_abs_bounds(a_abs_bounds, b)
}

/// Removes overlap between two overlapping [`RelativeBounds`]
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns [`OverlapRemovalErr::NoOverlap`].
pub fn remove_overlap_rel_bounds(
    a: &RelativeBounds,
    b: &RelativeBounds,
) -> Result<OverlapRemovalResult<EmptiableRelativeBounds>, OverlapRemovalErr> {
    type Dop = DisambiguatedOverlapPosition;

    let Ok(disambiguated_overlap_position) = a.disambiguated_overlap_position(b, OverlapRuleSet::default());

    match disambiguated_overlap_position {
        Dop::Outside => unreachable!("Only empty intervals can produce `OverlapPosition::Outside`"),
        Dop::OutsideBefore | Dop::OutsideAfter => Err(OverlapRemovalErr::NoOverlap),
        Dop::OnStart => {
            let RelativeEndBound::Finite(mut finite_bound) = a.rel_end() else {
                unreachable!(
                    "If the end of the reference bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `OnStart`"
                );
            };

            // Since `OnStart` only happens when two inclusive bounds are equal (since we are using the strict rule set)
            // we can just set the end inclusivity to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::from(
                RelativeBounds::new(a.rel_start(), RelativeEndBound::from(finite_bound)),
            )))
        },
        Dop::OnEnd => {
            let RelativeStartBound::Finite(mut finite_bound) = a.rel_start() else {
                unreachable!(
                    "If the start of the reference bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `OnEnd`"
                );
            };

            // Since `OnEnd` only happens when two inclusive bounds are equal (since we are using the strict rule set)
            // we can just set the start inclusivity to exclusive.
            finite_bound.set_inclusivity(BoundInclusivity::Exclusive);

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::from(
                RelativeBounds::new(RelativeStartBound::from(finite_bound), a.rel_end()),
            )))
        },
        Dop::CrossesStart => {
            let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
                unreachable!(
                    "If the start of the compared bounds is `InfinitePast`, \
                    then it is impossible that the overlap was `CrossesStart`"
                );
            };

            let new_end = RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::from(
                RelativeBounds::new(a.rel_start(), new_end),
            )))
        },
        Dop::CrossesEnd => {
            let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
                unreachable!(
                    "If the end of the compared bounds is `InfiniteFuture`, \
                    then it is impossible that the overlap was `CrossesEnd`"
                );
            };

            let new_start = RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                finite_bound.offset(),
                finite_bound.inclusivity().opposite(),
            ));

            Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::from(
                RelativeBounds::new(new_start, a.rel_end()),
            )))
        },
        Dop::Equal | Dop::Inside | Dop::InsideAndSameStart | Dop::InsideAndSameEnd => {
            Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::Empty))
        },
        Dop::ContainsAndSameStart => Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::from(
            remove_end_overlap_rel(a, b),
        ))),
        Dop::ContainsAndSameEnd => Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::from(
            remove_start_overlap_rel(a, b),
        ))),
        Dop::Contains => Ok(OverlapRemovalResult::Split(
            EmptiableRelativeBounds::from(remove_start_overlap_rel(a, b)),
            EmptiableRelativeBounds::from(remove_end_overlap_rel(a, b)),
        )),
    }
}

/// Removes the overlap of the two given [`RelativeBounds`] with
/// an [`ContainsAndSameEnd`](OverlapPosition::ContainsAndSameEnd) overlap
#[must_use]
pub fn remove_start_overlap_rel(a: &RelativeBounds, b: &RelativeBounds) -> RelativeBounds {
    let RelativeStartBound::Finite(finite_bound) = b.rel_start() else {
        unreachable!(
            "If the start of the compared bounds is `InfiniteStart`, \
            then it is impossible that the overlap was `ContainsAndSameEnd`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::InclusiveBoth,
        BoundInclusivity::Exclusive => CutType::ExclusiveBoth,
    };

    match a.cut_at(finite_bound.offset(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` start at the same time as `b` does, but b is exclusive on this point whereas
            // `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = RelativeFiniteBound::new(finite_bound.offset());

            RelativeBounds::new(RelativeStartBound::from(point), RelativeEndBound::from(point))
        },
        CutResult::Cut(new_a, _) => new_a,
    }
}

/// Removes the overlap of the two given [`RelativeBounds`] with
/// an [`ContainsAndSameStart`](OverlapPosition::ContainsAndSameStart) overlap
#[must_use]
pub fn remove_end_overlap_rel(a: &RelativeBounds, b: &RelativeBounds) -> RelativeBounds {
    let RelativeEndBound::Finite(finite_bound) = b.rel_end() else {
        unreachable!(
            "If the end of the compared bounds is `InfiniteFuture`, \
            then it is impossible that the overlap was `ContainsAndSameStart`"
        );
    };

    let cut_type = match finite_bound.inclusivity().opposite() {
        BoundInclusivity::Inclusive => CutType::InclusiveBoth,
        BoundInclusivity::Exclusive => CutType::ExclusiveBoth,
    };

    match a.cut_at(finite_bound.offset(), cut_type) {
        CutResult::Uncut => {
            // The only way we can get Uncut as a result would be if the rule set is strict
            // and that `a` ends at the same time as `b` does, but b is exclusive on this point whereas
            // `a` is inclusive.

            // TODO: Fix, this feels flaky
            let point = RelativeFiniteBound::new(finite_bound.offset());

            RelativeBounds::new(RelativeStartBound::from(point), RelativeEndBound::from(point))
        },
        CutResult::Cut(_, new_a) => new_a,
    }
}

/// Removes the overlap of an [`RelativeBounds`] with an [`EmptiableRelativeBounds`]
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns [`OverlapRemovalErr::NoOverlap`].
pub fn remove_overlap_rel_bounds_with_emptiable_rel_bounds(
    a: &RelativeBounds,
    b: &EmptiableRelativeBounds,
) -> Result<OverlapRemovalResult<EmptiableRelativeBounds>, OverlapRemovalErr> {
    let EmptiableRelativeBounds::Bound(b_rel_bounds) = b else {
        return Ok(OverlapRemovalResult::Single(EmptiableRelativeBounds::from(a.clone())));
    };

    remove_overlap_rel_bounds(a, b_rel_bounds)
}

/// Removes the overlap of two [`EmptiableRelativeBounds`]
///
/// # Errors
///
/// If the given bounds don't overlap, this method returns [`OverlapRemovalErr::NoOverlap`].
pub fn remove_overlap_emptiable_rel_bounds(
    a: &EmptiableRelativeBounds,
    b: &EmptiableRelativeBounds,
) -> Result<OverlapRemovalResult<EmptiableRelativeBounds>, OverlapRemovalErr> {
    let EmptiableRelativeBounds::Bound(a_rel_bounds) = a else {
        return Ok(OverlapRemovalResult::Single(a.clone()));
    };

    remove_overlap_rel_bounds_with_emptiable_rel_bounds(a_rel_bounds, b)
}

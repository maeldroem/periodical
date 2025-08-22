use chrono::Utc;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, BoundedAbsoluteInterval,
    EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::ComplementResult;
use crate::test_utils::date;

use super::complement::*;

#[test]
fn complement_of_unbounded_interval() {
    assert_eq!(UnboundedInterval.complement(), ComplementResult::Single(EmptyInterval));
}

#[test]
fn complement_of_empty_interval() {
    assert_eq!(EmptyInterval.complement(), ComplementResult::Single(UnboundedInterval));
}

#[test]
fn complement_of_half_unbounded_interval() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture).complement(),
        ComplementResult::Single(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
    );
}

#[test]
fn complement_of_bounded_interval() {
    assert_eq!(
        BoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).complement(),
        ComplementResult::Split(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

#[test]
fn complement_of_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.complement(),
        ComplementResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        ))),
    );
}

#[test]
fn complement_of_abs_bounds_unbounded() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).complement(),
        ComplementResult::Single(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn complement_of_abs_interval_unbounded() {
    assert_eq!(
        AbsoluteInterval::Unbounded(UnboundedInterval).complement(),
        ComplementResult::Single(AbsoluteInterval::Empty(EmptyInterval)),
    );
}

#[test]
fn complement_of_abs_interval_half_bounded() {
    assert_eq!(
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ))
        .complement(),
        ComplementResult::Single(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )
        )),
    );
}

#[test]
fn complement_of_abs_interval_bounded() {
    assert_eq!(
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ))
        .complement(),
        ComplementResult::Split(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

#[test]
fn complement_of_abs_interval_empty() {
    assert_eq!(
        AbsoluteInterval::Empty(EmptyInterval).complement(),
        ComplementResult::Single(AbsoluteInterval::Unbounded(UnboundedInterval)),
    );
}

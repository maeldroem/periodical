use chrono::Utc;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, ClosedAbsoluteInterval,
    EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::ops::ComplementResult;
use crate::test_utils::date;

use super::complement::*;

#[test]
fn complement_of_open_interval() {
    assert_eq!(OpenInterval.complement(), ComplementResult::Single(EmptyInterval));
}

#[test]
fn complement_of_empty_interval() {
    assert_eq!(EmptyInterval.complement(), ComplementResult::Single(OpenInterval));
}

#[test]
fn complement_of_half_open_interval() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture).complement(),
        ComplementResult::Single(AbsoluteInterval::HalfOpen(
            HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
    );
}

#[test]
fn complement_of_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).complement(),
        ComplementResult::Split(
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
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
fn complement_of_abs_bounds_open() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).complement(),
        ComplementResult::Single(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn complement_of_abs_interval_open() {
    assert_eq!(
        AbsoluteInterval::Open(OpenInterval).complement(),
        ComplementResult::Single(AbsoluteInterval::Empty(EmptyInterval)),
    );
}

#[test]
fn complement_of_abs_interval_half_open() {
    assert_eq!(
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ))
        .complement(),
        ComplementResult::Single(AbsoluteInterval::HalfOpen(
            HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )
        )),
    );
}

#[test]
fn complement_of_abs_interval_closed() {
    assert_eq!(
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ))
        .complement(),
        ComplementResult::Split(
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
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
        ComplementResult::Single(AbsoluteInterval::Open(OpenInterval)),
    );
}

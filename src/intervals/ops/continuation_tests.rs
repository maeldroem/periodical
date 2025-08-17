use chrono::Utc;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    ClosedAbsoluteInterval, EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::test_utils::date;

use super::continuation::*;

#[test]
fn past_continuation_open_interval() {
    assert_eq!(OpenInterval.past_continuation(), EmptyInterval,);
}

#[test]
fn future_continuation_open_interval() {
    assert_eq!(OpenInterval.future_continuation(), EmptyInterval,);
}

#[test]
fn past_continuation_empty_interval() {
    assert_eq!(EmptyInterval.past_continuation(), EmptyInterval,);
}

#[test]
fn future_continuation_empty_interval() {
    assert_eq!(EmptyInterval.future_continuation(), EmptyInterval,);
}

#[test]
fn past_continuation_half_open_to_past_interval() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .past_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_half_open_to_past_interval() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .future_continuation(),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn past_continuation_half_open_to_future_interval() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture,).past_continuation(),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn future_continuation_half_open_to_future_interval() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture,).future_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn past_continuation_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).past_continuation(),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn future_continuation_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).future_continuation(),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn past_continuation_abs_bounds_open() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).past_continuation(),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn future_continuation_abs_bounds_open() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).future_continuation(),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn past_continuation_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        )
        .past_continuation(),
        EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
        )),
    );
}

#[test]
fn future_continuation_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        )
        .future_continuation(),
        EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn past_continuation_abs_interval_open() {
    assert_eq!(
        AbsoluteInterval::Open(OpenInterval).past_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_abs_interval_open() {
    assert_eq!(
        AbsoluteInterval::Open(OpenInterval).future_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn past_continuation_abs_interval_empty() {
    assert_eq!(
        AbsoluteInterval::Empty(EmptyInterval).past_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_abs_interval_empty() {
    assert_eq!(
        AbsoluteInterval::Empty(EmptyInterval).future_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

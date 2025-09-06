use chrono::Utc;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    BoundedAbsoluteInterval, EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::test_utils::date;

use super::continuation::*;

#[test]
fn past_continuation_unbounded_interval() {
    assert_eq!(UnboundedInterval.past_continuation(), EmptyInterval,);
}

#[test]
fn future_continuation_unbounded_interval() {
    assert_eq!(UnboundedInterval.future_continuation(), EmptyInterval,);
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
fn past_continuation_half_bounded_to_past_interval() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .past_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_half_bounded_to_past_interval() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .future_continuation(),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn past_continuation_half_bounded_to_future_interval() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture,).past_continuation(),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn future_continuation_half_bounded_to_future_interval() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture,).future_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn past_continuation_bounded_interval() {
    assert_eq!(
        BoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).past_continuation(),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn future_continuation_bounded_interval() {
    assert_eq!(
        BoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).future_continuation(),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn past_continuation_abs_bounds_unbounded() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).past_continuation(),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn future_continuation_abs_bounds_unbounded() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).future_continuation(),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn past_continuation_abs_bounds_bounded() {
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
fn future_continuation_abs_bounds_bounded() {
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
fn past_continuation_abs_interval_unbounded() {
    assert_eq!(
        AbsoluteInterval::Unbounded(UnboundedInterval).past_continuation(),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_abs_interval_unbounded() {
    assert_eq!(
        AbsoluteInterval::Unbounded(UnboundedInterval).future_continuation(),
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

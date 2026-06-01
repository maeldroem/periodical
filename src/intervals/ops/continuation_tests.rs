use std::error::Error;

use jiff::Zoned;

use super::continuation::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn past_continuation_unbounded_interval() {
    assert_eq!(UnboundedInterval.past_continuation(), EmptyInterval);
}

#[test]
fn future_continuation_unbounded_interval() {
    assert_eq!(UnboundedInterval.future_continuation(), EmptyInterval);
}

#[test]
fn past_continuation_empty_interval() {
    assert_eq!(EmptyInterval.past_continuation(), EmptyInterval);
}

#[test]
fn future_continuation_empty_interval() {
    assert_eq!(EmptyInterval.future_continuation(), EmptyInterval);
}

#[test]
fn past_continuation_half_bounded_to_past_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .past_continuation(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    );

    Ok(())
}

#[test]
fn future_continuation_half_bounded_to_past_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .future_continuation(),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )
        )),
    );

    Ok(())
}

#[test]
fn past_continuation_half_bounded_to_future_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )
        .past_continuation(),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
    );

    Ok(())
}

#[test]
fn future_continuation_half_bounded_to_future_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )
        .future_continuation(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    );

    Ok(())
}

#[test]
fn past_continuation_bounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new_from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )
        .past_continuation(),
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );

    Ok(())
}

#[test]
fn future_continuation_bounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new_from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )
        .future_continuation(),
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        ),
    );

    Ok(())
}

#[test]
fn past_continuation_abs_bounds_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).past_continuation(),
        EmptiableAbsoluteBoundPair::Empty,
    );
}

#[test]
fn future_continuation_abs_bounds_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .future_continuation(),
        EmptiableAbsoluteBoundPair::Empty,
    );
}

#[test]
fn past_continuation_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        )
        .past_continuation(),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn future_continuation_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        )
        .future_continuation(),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn past_continuation_abs_interval_unbounded() {
    assert_eq!(
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Unbounded(UnboundedInterval)).past_continuation(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_abs_interval_unbounded() {
    assert_eq!(
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Unbounded(UnboundedInterval)).future_continuation(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn past_continuation_abs_interval_empty() {
    assert_eq!(
        EmptiableAbsoluteInterval::Empty(EmptyInterval).past_continuation(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_abs_interval_empty() {
    assert_eq!(
        EmptiableAbsoluteInterval::Empty(EmptyInterval).future_continuation(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    );
}

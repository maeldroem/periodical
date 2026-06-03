use std::error::Error;

use jiff::Zoned;

use super::continuation::*;
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
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .past_continuation(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    );

    Ok(())
}

#[test]
fn future_continuation_half_bounded_to_past_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .future_continuation(),
        EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(
            HalfBoundedAbsInterval::new_from_time_and_inclusivity(
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
        HalfBoundedAbsInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )
        .past_continuation(),
        EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(
            HalfBoundedAbsInterval::new_from_time_and_inclusivity(
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
        HalfBoundedAbsInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )
        .future_continuation(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    );

    Ok(())
}

#[test]
fn past_continuation_bounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )
        .past_continuation(),
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
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
        BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )
        .future_continuation(),
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
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
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).past_continuation(),
        EmptiableAbsBoundPair::Empty,
    );
}

#[test]
fn future_continuation_abs_bounds_unbounded() {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).future_continuation(),
        EmptiableAbsBoundPair::Empty,
    );
}

#[test]
fn past_continuation_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .past_continuation(),
        EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_inclusivity(
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .future_continuation(),
        EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn past_continuation_abs_interval_unbounded() {
    assert_eq!(
        EmptiableAbsInterval::Bound(AbsInterval::Unbounded(UnboundedInterval)).past_continuation(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_abs_interval_unbounded() {
    assert_eq!(
        EmptiableAbsInterval::Bound(AbsInterval::Unbounded(UnboundedInterval)).future_continuation(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    );
}

#[test]
fn past_continuation_abs_interval_empty() {
    assert_eq!(
        EmptiableAbsInterval::Empty(EmptyInterval).past_continuation(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    );
}

#[test]
fn future_continuation_abs_interval_empty() {
    assert_eq!(
        EmptiableAbsInterval::Empty(EmptyInterval).future_continuation(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    );
}

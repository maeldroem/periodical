use std::error::Error;

use jiff::Zoned;

use super::complement::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::ComplementResult;

#[test]
fn unbounded_interval() {
    assert_eq!(UnboundedInterval.complement(), ComplementResult::Single(EmptyInterval));
}

#[test]
fn empty_interval() {
    assert_eq!(EmptyInterval.complement(), ComplementResult::Single(UnboundedInterval));
}

#[test]
fn half_unbounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )
        .complement(),
        ComplementResult::Single(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );

    Ok(())
}

#[test]
fn bounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )
        .complement(),
        ComplementResult::Split(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            ),
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            ),
        ),
    );

    Ok(())
}

#[test]
fn emptiable_abs_bound_pair_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.complement(),
        ComplementResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        ))),
    );
}

#[test]
fn abs_bound_pair_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).complement(),
        ComplementResult::Single(EmptiableAbsoluteBoundPair::Empty),
    );
}

#[test]
fn abs_interval_unbounded() {
    assert_eq!(
        AbsoluteInterval::Unbounded(UnboundedInterval).complement(),
        ComplementResult::Single(EmptiableAbsoluteInterval::Empty(EmptyInterval)),
    );
}

#[test]
fn abs_interval_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ))
        .complement(),
        ComplementResult::Single(EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )
        ))),
    );

    Ok(())
}

#[test]
fn abs_interval_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))
        .complement(),
        ComplementResult::Split(
            EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            ))),
            EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            ))),
        ),
    );

    Ok(())
}

#[test]
fn abs_interval_empty() {
    assert_eq!(
        EmptiableAbsoluteInterval::Empty(EmptyInterval).complement(),
        ComplementResult::Single(EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Unbounded(UnboundedInterval))),
    );
}

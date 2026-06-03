use std::error::Error;

use jiff::Zoned;

use super::complement::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
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
        HalfBoundedAbsInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )
        .complement(),
        ComplementResult::Single(HalfBoundedAbsInterval::new_from_time_and_inclusivity(
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
        BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )
        .complement(),
        ComplementResult::Split(
            HalfBoundedAbsInterval::new_from_time_and_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            ),
            HalfBoundedAbsInterval::new_from_time_and_inclusivity(
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
        EmptiableAbsBoundPair::Empty.complement(),
        ComplementResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        ))),
    );
}

#[test]
fn abs_bound_pair_unbounded() {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).complement(),
        ComplementResult::Single(EmptiableAbsBoundPair::Empty),
    );
}

#[test]
fn abs_interval_unbounded() {
    assert_eq!(
        AbsInterval::Unbounded(UnboundedInterval).complement(),
        ComplementResult::Single(EmptiableAbsInterval::Empty(EmptyInterval)),
    );
}

#[test]
fn abs_interval_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ))
        .complement(),
        ComplementResult::Single(EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(
            HalfBoundedAbsInterval::new_from_time_and_inclusivity(
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
        AbsInterval::Bounded(BoundedAbsInterval::from_times_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))
        .complement(),
        ComplementResult::Split(
            EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                )
            )),
            EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::new_from_time_and_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                )
            )),
        ),
    );

    Ok(())
}

#[test]
fn abs_interval_empty() {
    assert_eq!(
        EmptiableAbsInterval::Empty(EmptyInterval).complement(),
        ComplementResult::Single(EmptiableAbsInterval::Bound(AbsInterval::Unbounded(UnboundedInterval))),
    );
}

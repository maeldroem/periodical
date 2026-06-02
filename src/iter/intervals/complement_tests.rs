use std::error::Error;

use jiff::Zoned;

use super::complement::*;
use crate::intervals::absolute::{
    AbsoluteInterval,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::ComplementResult;

#[test]
fn create() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )),
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )),
    ];

    intervals.complement();

    Ok(())
}

#[test]
fn run() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )),
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().collect::<Vec<_>>(),
        vec![
            ComplementResult::Split(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable(),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable(),
            ),
            ComplementResult::Single(EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            ComplementResult::Single(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable()
            ),
        ],
    );

    Ok(())
}

#[test]
fn run_reverse() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )),
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().rev().collect::<Vec<_>>(),
        vec![
            ComplementResult::Single(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable()
            ),
            ComplementResult::Single(EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            ComplementResult::Split(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable(),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable(),
            ),
        ],
    );

    Ok(())
}

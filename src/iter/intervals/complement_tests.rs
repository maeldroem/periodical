use std::error::Error;

use jiff::Zoned;

use super::complement::*;
use crate::intervals::absolute::{
    AbsInterval,
    BoundedAbsInterval,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::ComplementResult;

#[test]
fn create() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )),
        AbsInterval::Unbounded(UnboundedInterval),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
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
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )),
        AbsInterval::Unbounded(UnboundedInterval),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().collect::<Vec<_>>(),
        vec![
            ComplementResult::Split(
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable(),
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable(),
            ),
            ComplementResult::Single(EmptiableAbsInterval::Empty(EmptyInterval)),
            ComplementResult::Single(
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
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
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        )),
        AbsInterval::Unbounded(UnboundedInterval),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().rev().collect::<Vec<_>>(),
        vec![
            ComplementResult::Single(
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable()
            ),
            ComplementResult::Single(EmptiableAbsInterval::Empty(EmptyInterval)),
            ComplementResult::Split(
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable(),
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
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

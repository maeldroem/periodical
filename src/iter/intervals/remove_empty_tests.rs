use std::error::Error;

use jiff::Zoned;

use super::remove_empty::*;
use crate::intervals::absolute::{
    AbsInterval,
    BoundedAbsInterval,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
};
use crate::intervals::meta::OpeningDirection;
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn create() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsInterval::Unbounded(UnboundedInterval).to_emptiable(),
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable(),
        EmptiableAbsInterval::Empty(EmptyInterval),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable(),
    ];

    intervals.remove_empty_intervals();

    Ok(())
}

#[test]
fn run() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsInterval::Unbounded(UnboundedInterval).to_emptiable(),
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable(),
        EmptiableAbsInterval::Empty(EmptyInterval),
        EmptiableAbsInterval::Empty(EmptyInterval),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().collect::<Vec<_>>(),
        vec![
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable(),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
            .to_emptiable(),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToPast
            ))
            .to_emptiable(),
        ],
    );

    Ok(())
}

#[test]
fn run_reverse() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsInterval::Unbounded(UnboundedInterval).to_emptiable(),
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable(),
        EmptiableAbsInterval::Empty(EmptyInterval),
        EmptiableAbsInterval::Empty(EmptyInterval),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable(),
        EmptiableAbsInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().rev().collect::<Vec<_>>(),
        vec![
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToPast
            ))
            .to_emptiable(),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
            .to_emptiable(),
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable(),
        ],
    );

    Ok(())
}

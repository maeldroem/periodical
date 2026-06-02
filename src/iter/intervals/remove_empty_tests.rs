use std::error::Error;

use jiff::Zoned;

use super::remove_empty::*;
use crate::intervals::absolute::{
    AbsoluteInterval,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::OpeningDirection;
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn create() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable(),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
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
        AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable(),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable(),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
            .to_emptiable(),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
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
        AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable(),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().rev().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToPast
            ))
            .to_emptiable(),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from_times(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
            .to_emptiable(),
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable(),
        ],
    );

    Ok(())
}

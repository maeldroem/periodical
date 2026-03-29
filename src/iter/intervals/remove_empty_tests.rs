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
        AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable_interval(),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable_interval(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable_interval(),
    ];

    intervals.remove_empty_intervals();

    Ok(())
}

#[test]
fn run() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable_interval(),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable_interval(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable_interval(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable_interval(),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
            .to_emptiable_interval(),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToPast
            ))
            .to_emptiable_interval(),
        ],
    );

    Ok(())
}

#[test]
fn run_reverse() -> Result<(), Box<dyn Error>> {
    let intervals = [
        AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable_interval(),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))
        .to_emptiable_interval(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast,
        ))
        .to_emptiable_interval(),
        EmptiableAbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().rev().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToPast
            ))
            .to_emptiable_interval(),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
            .to_emptiable_interval(),
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable_interval(),
        ],
    );

    Ok(())
}

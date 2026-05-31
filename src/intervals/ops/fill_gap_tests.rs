use std::error::Error;

use jiff::Zoned;

use super::fill_gap::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};

#[test]
fn emptiable_abs_bound_pair_empty_abs_bound_pair_unbounded() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.fill_gap(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
        Ok(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        ))),
    );
}

#[test]
fn abs_bound_pair_unbounded_emptiable_abs_bound_pair_empty() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .fill_gap(&EmptiableAbsoluteBoundPair::Empty),
        Ok(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
    );
}

#[test]
fn emptiable_abs_bound_pair_empty_emptiable_abs_bound_pair_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.fill_gap(&EmptiableAbsoluteBoundPair::Empty),
        Ok(EmptiableAbsoluteBoundPair::Empty),
    );
}

#[test]
fn two_overlapping_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast
        )
        .fill_gap(&HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture
        )),
        Err(GapFillOverlapFoundError),
    );

    Ok(())
}

#[test]
fn two_non_overlapping_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast
        )
        .fill_gap(&HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture
        )),
        Ok(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
    );

    Ok(())
}

#[test]
fn two_strictly_adjacent_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast
        )
        .fill_gap(&HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture
        )),
        Err(GapFillOverlapFoundError),
    );

    Ok(())
}

#[test]
fn two_leniently_adjacent_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .fill_gap(&HalfBoundedAbsoluteInterval::new_from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture
        )),
        Ok(AbsoluteInterval::HalfBounded(
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
fn two_very_leniently_adjacent_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .fill_gap(&HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
        Ok(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )
        )),
    );

    Ok(())
}

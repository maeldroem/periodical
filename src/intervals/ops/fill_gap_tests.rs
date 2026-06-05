use std::error::Error;

use jiff::Zoned;

use super::fill_gap::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsBoundPair,
    HalfBoundedAbsInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};

#[test]
fn emptiable_abs_bound_pair_empty_abs_bound_pair_unbounded() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.fill_gap(&AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture
        )),
        Ok(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        ))),
    );
}

#[test]
fn abs_bound_pair_unbounded_emptiable_abs_bound_pair_empty() {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
            .fill_gap(&EmptiableAbsBoundPair::Empty),
        Ok(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture
        )),
    );
}

#[test]
fn emptiable_abs_bound_pair_empty_emptiable_abs_bound_pair_empty() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.fill_gap(&EmptiableAbsBoundPair::Empty),
        Ok(EmptiableAbsBoundPair::Empty),
    );
}

#[test]
fn two_overlapping_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast
        )
        .fill_gap(&HalfBoundedAbsInterval::from_time(
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
        HalfBoundedAbsInterval::from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast
        )
        .fill_gap(&HalfBoundedAbsInterval::from_time(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture
        )),
        Ok(AbsInterval::HalfBounded(
            HalfBoundedAbsInterval::from_time_incl(
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
        HalfBoundedAbsInterval::from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToPast
        )
        .fill_gap(&HalfBoundedAbsInterval::from_time(
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
        HalfBoundedAbsInterval::from_time_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .fill_gap(&HalfBoundedAbsInterval::from_time(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            OpeningDirection::ToFuture
        )),
        Ok(AbsInterval::HalfBounded(
            HalfBoundedAbsInterval::from_time_incl(
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
        HalfBoundedAbsInterval::from_time_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .fill_gap(&HalfBoundedAbsInterval::from_time_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
        Ok(AbsInterval::HalfBounded(
            HalfBoundedAbsInterval::from_time_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )
        )),
    );

    Ok(())
}

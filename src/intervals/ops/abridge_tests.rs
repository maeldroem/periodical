use std::error::Error;

use jiff::Zoned;

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;

use super::abridge::*;

#[test]
fn abs_bounds_two_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).abridge(
            &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
        ),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
    );
}

#[test]
fn abs_bounds_unbounded_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).abridge(
            &AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::InfiniteFuture,
            )
        ),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_unbounded_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).abridge(
            &AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
        ),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_half_bounded_unbounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_two_equal_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_two_half_bounded_same_ref_time() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()))
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_two_half_bounded_with_gap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_two_half_bounded_same_direction_different_times() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_bounded_half_bounded_with_gap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_two_bounded_with_gap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_two_bounded_overlapping() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )),
    );

    Ok(())
}

#[test]
fn emptiable_abs_bounds_w_abs_bounds() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
    );
}

#[test]
fn abs_bounds_w_emptiable_abs_bounds() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .abridge(&EmptiableAbsoluteBoundPair::Empty),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
    );
}

#[test]
fn abs_bounds_abs_bounds_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )),
    );

    Ok(())
}

#[test]
fn abs_bounds_abs_bounds_adjacent_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Empty,
    );

    Ok(())
}

#[test]
fn abs_bounds_abs_bounds_adjacent_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Empty,
    );

    Ok(())
}

#[test]
fn abs_bounds_abs_bounds_adjacent_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )
        .abridge(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
        )),
    );

    Ok(())
}

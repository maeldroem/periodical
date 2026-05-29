use std::error::Error;

use jiff::Zoned;

use super::intersect::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::IntersectionResult;

#[test]
fn empty_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.intersect(&EmptiableAbsoluteBoundPair::Empty),
        IntersectionResult::Separate,
    );
}

#[test]
fn empty_unbounded() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.intersect(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        IntersectionResult::Separate,
    );
}

#[test]
fn unbounded_empty() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            .intersect(&EmptiableAbsoluteBoundPair::Empty),
        IntersectionResult::Separate,
    );
}

#[test]
fn unbounded_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).intersect(
            &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
        ),
        IntersectionResult::Intersected(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .intersect(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        IntersectionResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )
        .intersect(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        IntersectionResult::Intersected(AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn bounded_adjacent_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )
        .intersect(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        IntersectionResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_adjacent_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .intersect(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        IntersectionResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_adjacent_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .intersect(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        IntersectionResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_clear_overlap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .intersect(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        IntersectionResult::Intersected(AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .intersect(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        IntersectionResult::Intersected(AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).intersect(
            &AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )
        ),
        IntersectionResult::Intersected(AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
    );

    Ok(())
}

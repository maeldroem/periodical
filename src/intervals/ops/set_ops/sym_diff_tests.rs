use std::error::Error;

use jiff::Zoned;

use super::sym_diff::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::SymmetricDifferenceResult;

#[test]
fn empty_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.symmetrically_differentiate(&EmptiableAbsoluteBoundPair::Empty),
        SymmetricDifferenceResult::Separate,
    );
}

#[test]
fn empty_unbounded() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.symmetrically_differentiate(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        SymmetricDifferenceResult::Separate,
    );
}

#[test]
fn unbounded_empty() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            .symmetrically_differentiate(&EmptiableAbsoluteBoundPair::Empty),
        SymmetricDifferenceResult::Separate,
    );
}

#[test]
fn unbounded_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        SymmetricDifferenceResult::Single(EmptiableAbsoluteBoundPair::Empty),
    );
}

#[test]
fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .symmetrically_differentiate(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        SymmetricDifferenceResult::Separate,
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
        .symmetrically_differentiate(&AbsoluteBoundPair::new(
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
        SymmetricDifferenceResult::Split(
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
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
            )),
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
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
        ),
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
        .symmetrically_differentiate(&AbsoluteBoundPair::new(
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
        SymmetricDifferenceResult::Separate,
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
        .symmetrically_differentiate(&AbsoluteBoundPair::new(
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
        SymmetricDifferenceResult::Separate,
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
        .symmetrically_differentiate(&AbsoluteBoundPair::new(
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
        SymmetricDifferenceResult::Separate,
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
        .symmetrically_differentiate(&AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        SymmetricDifferenceResult::Split(
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
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
            )),
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
        ),
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
        .symmetrically_differentiate(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        SymmetricDifferenceResult::Split(
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            )),
        ),
    );

    Ok(())
}

#[test]
fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )),
        SymmetricDifferenceResult::Split(
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            )),
        ),
    );

    Ok(())
}

use std::error::Error;

use jiff::Zoned;

use super::sym_diff::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
    EmptiableAbsBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::SymmetricDifferenceResult;

#[test]
fn empty_empty() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.symmetrically_differentiate(&EmptiableAbsBoundPair::Empty),
        SymmetricDifferenceResult::Separate,
    );
}

#[test]
fn empty_unbounded() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.symmetrically_differentiate(&AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
        SymmetricDifferenceResult::Separate,
    );
}

#[test]
fn unbounded_empty() {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,)
            .symmetrically_differentiate(&EmptiableAbsBoundPair::Empty),
        SymmetricDifferenceResult::Separate,
    );
}

#[test]
fn unbounded_unbounded() {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,)
            .symmetrically_differentiate(&AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture,
            )),
        SymmetricDifferenceResult::Single(EmptiableAbsBoundPair::Empty),
    );
}

#[test]
fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .symmetrically_differentiate(&AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        SymmetricDifferenceResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )
        .symmetrically_differentiate(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        SymmetricDifferenceResult::Split(
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )
        .symmetrically_differentiate(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .symmetrically_differentiate(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .symmetrically_differentiate(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .symmetrically_differentiate(&AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        SymmetricDifferenceResult::Split(
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .symmetrically_differentiate(&AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
        SymmetricDifferenceResult::Split(
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            )),
        ),
    );

    Ok(())
}

#[test]
fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,)
            .symmetrically_differentiate(&AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )),
        SymmetricDifferenceResult::Split(
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            )),
        ),
    );

    Ok(())
}

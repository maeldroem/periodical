use std::error::Error;

use jiff::Zoned;

use super::unite::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
    EmptiableAbsBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::UnionResult;

#[test]
fn empty_empty() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.unite(&EmptiableAbsBoundPair::Empty),
        UnionResult::Separate,
    );
}

#[test]
fn empty_unbounded() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.unite(&AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
        UnionResult::Separate,
    );
}

#[test]
fn unbounded_empty() {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,)
            .unite(&EmptiableAbsBoundPair::Empty),
        UnionResult::Separate,
    );
}

#[test]
fn unbounded_unbounded() {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,).unite(
            &AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,)
        ),
        UnionResult::United(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )
        .unite(&AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        UnionResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )
        .unite(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        UnionResult::United(AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )
        .unite(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        UnionResult::United(AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn bounded_adjacent_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .unite(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        UnionResult::United(AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn bounded_adjacent_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .unite(&AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        )),
        UnionResult::Separate,
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
        .unite(&AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
        UnionResult::United(AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        )),
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
        .unite(&AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
        UnionResult::United(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,).unite(
            &AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )
        ),
        UnionResult::United(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

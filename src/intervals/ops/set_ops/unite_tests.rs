use std::error::Error;

use jiff::Zoned;

use super::unite::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::UnionResult;

#[test]
fn empty_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.unite(&EmptiableAbsoluteBoundPair::Empty),
        UnionResult::Separate,
    );
}

#[test]
fn empty_unbounded() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.unite(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        UnionResult::Separate,
    );
}

#[test]
fn unbounded_empty() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            .unite(&EmptiableAbsoluteBoundPair::Empty),
        UnionResult::Separate,
    );
}

#[test]
fn unbounded_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).unite(
            &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
        ),
        UnionResult::United(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )
        .unite(&AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )),
        UnionResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .unite(&AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )),
        UnionResult::United(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )),
    );

    Ok(())
}

#[test]
fn bounded_adjacent_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .unite(&AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )),
        UnionResult::United(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )),
    );

    Ok(())
}

#[test]
fn bounded_adjacent_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )
        .unite(&AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )),
        UnionResult::United(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )),
    );

    Ok(())
}

#[test]
fn bounded_adjacent_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )
        .unite(&AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )),
        UnionResult::Separate,
    );

    Ok(())
}

#[test]
fn bounded_clear_overlap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )
        .unite(&AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )),
        UnionResult::United(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )),
    );

    Ok(())
}

#[test]
fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )
        .unite(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        UnionResult::United(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

#[test]
fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).unite(
            &AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            )
        ),
        UnionResult::United(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );

    Ok(())
}

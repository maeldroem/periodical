use std::error::Error;

use jiff::Zoned;

use super::shrink::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
    EmptiableAbsBoundPair,
};

#[test]
fn shrink_start_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.shrink_start(AbsStartBound::InfinitePast),
        EmptiableAbsBoundPair::Empty,
    );
}

#[test]
fn shrink_end_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.shrink_end(AbsEndBound::InfiniteFuture),
        EmptiableAbsBoundPair::Empty,
    );
}

#[test]
fn shrink_start_to_finite_unbounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).shrink_start(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
        ),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        ),
    );

    Ok(())
}

#[test]
fn shrink_end_to_finite_unbounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).shrink_end(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
        AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
    );

    Ok(())
}

#[test]
fn shrink_start_to_inside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        )
        .shrink_start(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
        ),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
    );

    Ok(())
}

#[test]
fn shrink_end_to_inside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        )
        .shrink_end(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
    );

    Ok(())
}

#[test]
fn shrink_start_to_outside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        )
        .shrink_start(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
        ),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
    );

    Ok(())
}

#[test]
fn shrink_end_to_outside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        )
        .shrink_end(
            AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
    );

    Ok(())
}

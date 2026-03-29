use std::error::Error;

use jiff::Zoned;

use super::extend::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};

#[test]
fn abs_bound_pair_two_unbounded() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).extend(
            &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );
}

#[test]
fn abs_bound_pair_unbounded_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).extend(
            &AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::InfiniteFuture,
            )
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_unbounded_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).extend(
            &AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            )
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_half_bounded_unbounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_two_equal_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        ),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_two_half_bounded_same_ref_time() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_two_half_bounded_with_gap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_two_half_bounded_same_direction_different_times() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        ),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_bounded_half_bounded_with_gap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::InfiniteFuture,
        ),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_two_bounded_with_gap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        ),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_two_bounded_overlapping() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )
        .extend(&AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        )),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        ),
    );

    Ok(())
}

#[test]
fn emptiable_abs_bound_pair_w_abs_bound_pair() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.extend(&AbsoluteBoundPair::new(
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
fn abs_bound_pair_w_emptiable_abs_bound_pair() {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .extend(&EmptiableAbsoluteBoundPair::Empty),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );
}

use std::error::Error;

use jiff::Zoned;

use super::grow::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};

#[test]
fn start_emptiable_abs_bound_pair_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.grow_start(AbsoluteStartBound::InfinitePast),
        EmptiableAbsoluteBoundPair::Empty,
    );
}

#[test]
fn end_emptiable_abs_bound_pair_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.grow_end(AbsoluteEndBound::InfiniteFuture),
        EmptiableAbsoluteBoundPair::Empty,
    );
}

#[test]
fn start_to_finite_unbounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).grow_start(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn end_to_finite_unbounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).grow_end(
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn start_to_inside_abs_bound_pair_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .grow_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

#[test]
fn end_to_inside_abs_bound_pair_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .grow_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

#[test]
fn start_to_outside_abs_bound_pair_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .grow_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

#[test]
fn end_to_outside_abs_bound_pair_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .grow_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

use std::error::Error;

use jiff::Zoned;

use super::shrink::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};

#[test]
fn shrink_start_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.shrink_start(AbsoluteStartBound::InfinitePast),
        EmptiableAbsoluteBoundPair::Empty,
    );
}

#[test]
fn shrink_end_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.shrink_end(AbsoluteEndBound::InfiniteFuture),
        EmptiableAbsoluteBoundPair::Empty,
    );
}

#[test]
fn shrink_start_to_finite_unbounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).shrink_start(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
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
fn shrink_end_to_finite_unbounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).shrink_end(
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
        ),
    );

    Ok(())
}

#[test]
fn shrink_start_to_inside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .shrink_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

#[test]
fn shrink_end_to_inside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .shrink_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

#[test]
fn shrink_start_to_outside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .shrink_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

#[test]
fn shrink_end_to_outside_abs_bounds_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        )
        .shrink_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
        ))),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            ))
        ),
    );

    Ok(())
}

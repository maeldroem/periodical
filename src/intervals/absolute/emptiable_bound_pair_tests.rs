use std::error::Error;

use jiff::Timestamp;

use super::emptiable_bound_pair::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};

#[test]
fn bound_bound() -> Result<(), Box<dyn Error>> {
    let bound_pair = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );
    let emptiable_bound_pair = bound_pair.clone().to_emptiable();

    assert_eq!(emptiable_bound_pair.bound(), Some(bound_pair),);
    Ok(())
}

#[test]
fn bound_empty() {
    assert_eq!(EmptiableAbsoluteBoundPair::Empty.bound(), None);
}

#[test]
fn from_absolute_bounds() {
    assert_eq!(
        EmptiableAbsoluteBoundPair::from(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
}

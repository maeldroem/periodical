use jiff::SignedDuration;

use crate::intervals::relative::{RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};

use super::emptiable_bound_pair::*;

#[test]
fn bound_bound() {
    let bound_pair = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );
    let emptiable_bound_pair = bound_pair.clone().to_emptiable();

    assert_eq!(
        emptiable_bound_pair.bound(),
        Some(bound_pair),
    );
}

#[test]
fn bound_empty() {
    assert_eq!(EmptiableRelativeBoundPair::Empty.bound(), None);
}

#[test]
fn from_absolute_bounds() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
        EmptiableRelativeBoundPair::Bound(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
    );
}

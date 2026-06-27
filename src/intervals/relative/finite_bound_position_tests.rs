use std::ops::Bound;

use jiff::SignedDuration;

use super::finite_bound_position::*;
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::{RelEndBound, RelStartBound};

#[test]
fn new() {
    let offset = SignedDuration::from_hours(1);
    let rel_finite_bound_position = RelFiniteBoundPos::new(offset);

    assert_eq!(rel_finite_bound_position.offset(), offset);
    assert_eq!(rel_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let offset = SignedDuration::from_hours(1);
    let rel_finite_bound_position = RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive);

    assert_eq!(rel_finite_bound_position.offset(), offset);
    assert_eq!(rel_finite_bound_position.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn offset() {
    let offset = SignedDuration::from_hours(1);
    let interval = RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive);

    assert_eq!(interval.offset(), offset);
}

#[test]
fn set_offset() {
    let mut rel_finite_bound_position = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    rel_finite_bound_position.set_offset(SignedDuration::from_hours(5));

    assert_eq!(rel_finite_bound_position.offset(), SignedDuration::from_hours(5));
}

#[test]
fn set_inclusivity() {
    let mut rel_finite_bound_position =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    rel_finite_bound_position.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(rel_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn to_start_bound() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_start_bound(),
        RelStartBound::Finite(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_finite_start_bound()
        )
    );
}

#[test]
fn to_end_bound() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_end_bound(),
        RelEndBound::Finite(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_finite_end_bound()
        )
    );
}

#[test]
fn inclusivity() {
    let inclusive = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive);
    let exclusive = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    assert_eq!(inclusive.inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(exclusive.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_signed_duration() {
    assert_eq!(
        RelFiniteBoundPos::from(SignedDuration::from_hours(1)),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive),
    );
}

#[test]
fn from_signed_duration_inclusivity_pair() {
    assert_eq!(
        RelFiniteBoundPos::from((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn try_from_bound() {
    assert_eq!(
        RelFiniteBoundPos::try_from(Bound::Included(SignedDuration::from_hours(1))),
        Ok(RelFiniteBoundPos::new_with_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive
        )),
    );
    assert_eq!(
        RelFiniteBoundPos::try_from(Bound::Excluded(SignedDuration::from_hours(1))),
        Ok(RelFiniteBoundPos::new_with_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        )),
    );
    assert_eq!(
        RelFiniteBoundPos::try_from(Bound::Unbounded),
        Err(RelFiniteBoundPosTryFromBoundError),
    );
}

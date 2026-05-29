use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::finite_bound_position::*;
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::{RelativeEndBound, RelativeStartBound};

#[test]
fn new() {
    let offset = SignedDuration::from_hours(1);
    let rel_finite_bound_position = RelativeFiniteBoundPosition::new(offset);

    assert_eq!(rel_finite_bound_position.offset(), offset);
    assert_eq!(rel_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let offset = SignedDuration::from_hours(1);
    let rel_finite_bound_position = RelativeFiniteBoundPosition::new_with_inclusivity(offset, BoundInclusivity::Exclusive);

    assert_eq!(rel_finite_bound_position.offset(), offset);
    assert_eq!(rel_finite_bound_position.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn offset() {
    let offset = SignedDuration::from_hours(1);
    let interval = RelativeFiniteBoundPosition::new_with_inclusivity(offset, BoundInclusivity::Exclusive);

    assert_eq!(interval.offset(), offset);
}

#[test]
fn set_offset() {
    let mut rel_finite_bound_position = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1));

    rel_finite_bound_position.set_offset(SignedDuration::from_hours(5));

    assert_eq!(rel_finite_bound_position.offset(), SignedDuration::from_hours(5));
}

#[test]
fn set_inclusivity() {
    let mut rel_finite_bound_position =
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    rel_finite_bound_position.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(rel_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn to_start_bound() {
    assert_eq!(
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeStartBound::Finite(RelativeFiniteBoundPosition::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        ))
    );
}

#[test]
fn to_end_bound() {
    assert_eq!(
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_end_bound(),
        RelativeEndBound::Finite(RelativeFiniteBoundPosition::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        ))
    );
}

#[test]
fn inclusivity() {
    let inclusive =
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive);
    let exclusive =
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    assert_eq!(inclusive.inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(exclusive.inclusivity(), BoundInclusivity::Exclusive);
}

mod ord {
    use super::*;

    #[test]
    fn greater_times() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2))
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))),
            Ordering::Greater
        );
    }

    #[test]
    fn less_times() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2))),
            Ordering::Less
        );
    }

    #[test]
    fn equal_times_inclusive_inclusive() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive).cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn equal_times_exclusive_exclusive() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn equal_times_inclusive_exclusive() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive).cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn equal_times_exclusive_inclusive() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            ),
            Ordering::Equal
        );
    }
}

#[test]
fn from_signed_duration() {
    assert_eq!(
        RelativeFiniteBoundPosition::from(SignedDuration::from_hours(1)),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive),
    );
}

#[test]
fn from_signed_duration_inclusivity_pair() {
    assert_eq!(
        RelativeFiniteBoundPosition::from((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn try_from_bound() {
    assert_eq!(
        RelativeFiniteBoundPosition::try_from(Bound::Included(SignedDuration::from_hours(1))),
        Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive
        )),
    );
    assert_eq!(
        RelativeFiniteBoundPosition::try_from(Bound::Excluded(SignedDuration::from_hours(1))),
        Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        )),
    );
    assert_eq!(
        RelativeFiniteBoundPosition::try_from(Bound::Unbounded),
        Err(RelativeFiniteBoundPositionTryFromBoundError),
    );
}

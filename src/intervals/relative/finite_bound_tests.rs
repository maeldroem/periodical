use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::finite_bound::*;
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::{RelativeEndBound, RelativeStartBound};

#[test]
fn new() {
    let offset = SignedDuration::from_hours(1);
    let rel_finite_bound = RelativeFiniteBound::new(offset);

    assert_eq!(rel_finite_bound.offset(), offset);
    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let offset = SignedDuration::from_hours(1);
    let rel_finite_bound = RelativeFiniteBound::new_with_inclusivity(offset, BoundInclusivity::Exclusive);

    assert_eq!(rel_finite_bound.offset(), offset);
    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn offset() {
    let offset = SignedDuration::from_hours(1);
    let interval = RelativeFiniteBound::new_with_inclusivity(offset, BoundInclusivity::Exclusive);

    assert_eq!(interval.offset(), offset);
}

#[test]
fn set_offset() {
    let mut rel_finite_bound = RelativeFiniteBound::new(SignedDuration::from_hours(1));

    rel_finite_bound.set_offset(SignedDuration::from_hours(5));

    assert_eq!(rel_finite_bound.offset(), SignedDuration::from_hours(5));
}

#[test]
fn set_inclusivity() {
    let mut rel_finite_bound =
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    rel_finite_bound.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn to_start_bound() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        ))
    );
}

#[test]
fn to_end_bound() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_end_bound(),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        ))
    );
}

#[test]
fn inclusivity() {
    let inclusive =
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive);
    let exclusive =
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    assert_eq!(inclusive.inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(exclusive.inclusivity(), BoundInclusivity::Exclusive);
}

mod ord {
    use super::*;

    #[test]
    fn greater_times() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(2))
                .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            Ordering::Greater
        );
    }

    #[test]
    fn less_times() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(1))
                .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(2))),
            Ordering::Less
        );
    }

    #[test]
    fn equal_times_inclusive_inclusive() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive).cmp(
                &RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn equal_times_exclusive_exclusive() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).cmp(
                &RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn equal_times_inclusive_exclusive() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive).cmp(
                &RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn equal_times_exclusive_inclusive() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).cmp(
                &RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            ),
            Ordering::Equal
        );
    }
}

#[test]
fn from_signed_duration() {
    assert_eq!(
        RelativeFiniteBound::from(SignedDuration::from_hours(1)),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive),
    );
}

#[test]
fn from_signed_duration_inclusivity_pair() {
    assert_eq!(
        RelativeFiniteBound::from((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn try_from_bound() {
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Included(SignedDuration::from_hours(1))),
        Ok(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive
        )),
    );
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Excluded(SignedDuration::from_hours(1))),
        Ok(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        )),
    );
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Unbounded),
        Err(RelativeFiniteBoundTryFromBoundError),
    );
}

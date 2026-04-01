use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::finite_bound::*;
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

#[test]
fn new() {
    let rel_finite_bound = RelativeFiniteBound::new(SignedDuration::from_hours(1));

    assert_eq!(rel_finite_bound.offset(), SignedDuration::from_hours(1));
    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let rel_finite_bound =
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    assert_eq!(rel_finite_bound.offset(), SignedDuration::from_hours(1));
    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
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
fn inclusivity() {
    let rel_finite_bound =
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);

    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn cmp_greater_times() {
    let rel_finite_bound = [
        RelativeFiniteBound::new(SignedDuration::from_hours(2)),
        RelativeFiniteBound::new(SignedDuration::from_hours(1)),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Greater);
}

#[test]
fn cmp_equal_times() {
    let rel_finite_bound = [
        RelativeFiniteBound::new(SignedDuration::from_hours(1)),
        RelativeFiniteBound::new(SignedDuration::from_hours(1)),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Equal);
}

#[test]
fn cmp_equal_time_different_inclusivities() {
    let rel_finite_bound = [
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Equal);
}

#[test]
fn cmp_less() {
    let rel_finite_bound = [
        RelativeFiniteBound::new(SignedDuration::from_hours(1)),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Less);
}

#[test]
fn from_datetime() {
    assert_eq!(
        RelativeFiniteBound::from(SignedDuration::from_hours(1)),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive),
    );
}

#[test]
fn from_datetime_inclusivity_pair() {
    assert_eq!(
        RelativeFiniteBound::from((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn try_from_inclusive_bound() {
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Included(SignedDuration::from_hours(1))),
        Ok(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive
        )),
    );
}

#[test]
fn try_from_exclusive_bound() {
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Excluded(SignedDuration::from_hours(1))),
        Ok(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive
        )),
    );
}

#[test]
fn try_from_unbounded_bound() {
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Unbounded),
        Err(RelativeFiniteBoundTryFromBoundError),
    );
}

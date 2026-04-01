use std::cmp::Ordering;

use jiff::SignedDuration;

use super::bound_pair::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    EmptiableRelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};

#[test]
fn unchecked_new() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let rel_bounds = RelativeBoundPair::unchecked_new(start, end);

    assert_eq!(rel_bounds.rel_start(), start);
    assert_eq!(rel_bounds.rel_end(), end);
}

#[test]
fn new_should_swap() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_exclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_inclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn from_range() {
    let start = SignedDuration::from_hours(1);
    let range = start..;

    let bound_pair = RelativeBoundPair::from_range(range);

    assert_eq!(bound_pair.start(), RelativeFiniteBound::new(start).to_start_bound());
    assert_eq!(bound_pair.end(), RelativeEndBound::InfiniteFuture);
}

#[test]
fn to_emptiable() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(5)).to_end_bound();

    assert_eq!(
        RelativeBoundPair::new(start, end).to_emptiable(),
        EmptiableRelativeBoundPair::Bound(RelativeBoundPair::new(start, end)),
    );
}

#[test]
fn unchecked_set_start() {
    let mut bounds = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );

    let new_start = RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound();

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.rel_start(), new_start);
}

#[test]
fn unchecked_set_end() {
    let mut bounds = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
    );

    let new_end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.rel_end(), new_end);
}

#[test]
fn set_start() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound();
    let mut bounds = RelativeBoundPair::new(start, end);

    assert!(!bounds.set_start(RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound()));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn set_end() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound();
    let mut bounds = RelativeBoundPair::new(start, end);

    assert!(!bounds.set_end(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn unbounded_unbounded_cmp() {
    let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn unbounded_half_bounded_to_future_cmp() {
    let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn unbounded_half_bounded_to_past_cmp() {
    let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn unbounded_bounded_cmp() {
    let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn half_bounded_to_future_unbounded_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_future_after_first_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn half_bounded_to_future_to_future_before_first_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_future_same_time_exclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn half_bounded_to_future_to_future_same_time_exclusive_inclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_future_same_time_inclusive_exclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn half_bounded_to_future_to_future_same_time_inclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn half_bounded_to_future_to_past_before_first_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_past_after_first_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_past_same_time_exclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_past_same_time_exclusive_inclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_past_same_time_inclusive_exclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_to_past_same_time_inclusive_bounds_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_bounded_starts_before_first_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn half_bounded_to_future_bounded_starts_after_first_cmp() {
    let a = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn try_from_emptiable_correct_variant() {
    assert_eq!(
        RelativeBoundPair::try_from(
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture,).to_emptiable()
        ),
        Ok(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn try_from_emptiable_wrong_variant() {
    assert_eq!(
        RelativeBoundPair::try_from(EmptiableRelativeBoundPair::Empty),
        Err(RelativeBoundPairTryFromEmptiableRelativeBoundPairError),
    );
}

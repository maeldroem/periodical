use jiff::SignedDuration;

use super::relative::*;
use crate::intervals::meta::BoundInclusivity;

#[test]
fn relative_start_bound_inf_relative_end_bound_inf_swap() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeEndBound::InfiniteFuture;

    swap_relative_bound_pair(&mut start, &mut end);

    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn relative_start_bound_inf_relative_end_bound_finite_swap() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    swap_relative_bound_pair(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
            .to_start_bound()
    );
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn relative_start_bound_finite_relative_end_bound_inf_swap() {
    let mut start =
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
    let mut end = RelativeEndBound::InfiniteFuture;

    swap_relative_bound_pair(&mut start, &mut end);

    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(
        end,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
            .to_end_bound()
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_swap() {
    let mut start =
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
    let mut end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Inclusive)
        .to_end_bound();

    swap_relative_bound_pair(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Inclusive,)
            .to_start_bound()
    );
    assert_eq!(
        end,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
            .to_end_bound()
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_inf_past_inf_future() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeStartBound::InfinitePast,
            &RelativeEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_inf_past_finite() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeStartBound::InfinitePast,
            &RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_inf_future() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelativeEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_correct_order() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            &RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        Err(RelativeBoundPairCheckForIntervalCreationError::StartPastEnd),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound(),
        ),
        Err(RelativeBoundPairCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_inf_past_inf_future() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeEndBound::InfiniteFuture;

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_inf_past_finite() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(
        end,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_inf_future() {
    let mut start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end = RelativeEndBound::InfiniteFuture;

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_correct_order() {
    let mut start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound();

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(
        end,
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    let mut start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let mut end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
    );
    assert_eq!(
        end,
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    let mut start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(
        end,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    let mut start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(
        end,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()
    );
}

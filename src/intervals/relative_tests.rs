use jiff::SignedDuration;

use super::relative::*;
use crate::intervals::meta::BoundInclusivity;

#[test]
fn relative_start_bound_inf_relative_end_bound_inf_swap() {
    let mut start = RelStartBound::InfinitePast;
    let mut end = RelEndBound::InfiniteFuture;

    swap_rel_start_end_bounds(&mut start, &mut end);

    assert_eq!(start, RelStartBound::InfinitePast);
    assert_eq!(end, RelEndBound::InfiniteFuture);
}

#[test]
fn relative_start_bound_inf_relative_end_bound_finite_swap() {
    let mut start = RelStartBound::InfinitePast;
    let mut end =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_end_bound();

    swap_rel_start_end_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,).to_start_bound()
    );
    assert_eq!(end, RelEndBound::InfiniteFuture);
}

#[test]
fn relative_start_bound_finite_relative_end_bound_inf_swap() {
    let mut start =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_start_bound();
    let mut end = RelEndBound::InfiniteFuture;

    swap_rel_start_end_bounds(&mut start, &mut end);

    assert_eq!(start, RelStartBound::InfinitePast);
    assert_eq!(
        end,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,).to_end_bound()
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_swap() {
    let mut start =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_start_bound();
    let mut end =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Inclusive).to_end_bound();

    swap_rel_start_end_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Inclusive,).to_start_bound()
    );
    assert_eq!(
        end,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,).to_end_bound()
    );
}

#[test]
fn check_relative_start_end_bounds_for_interval_creation_inf_past_inf_future() {
    assert_eq!(
        check_rel_start_end_bounds_for_interval_creation(&RelStartBound::InfinitePast, &RelEndBound::InfiniteFuture,),
        Ok(()),
    );
}

#[test]
fn check_relative_start_end_bounds_for_interval_creation_inf_past_finite() {
    assert_eq!(
        check_rel_start_end_bounds_for_interval_creation(
            &RelStartBound::InfinitePast,
            &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_start_end_bounds_for_interval_creation_finite_inf_future() {
    assert_eq!(
        check_rel_start_end_bounds_for_interval_creation(
            &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_start_end_bounds_for_interval_creation_finite_finite_different_offsets_correct_order() {
    assert_eq!(
        check_rel_start_end_bounds_for_interval_creation(
            &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_start_end_bounds_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    assert_eq!(
        check_rel_start_end_bounds_for_interval_creation(
            &RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
            &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
    );
}

#[test]
fn check_relative_start_end_bounds_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    assert_eq!(
        check_rel_start_end_bounds_for_interval_creation(
            &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_start_end_bounds_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    assert_eq!(
        check_rel_start_end_bounds_for_interval_creation(
            &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound(),
        ),
        Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_inf_past_inf_future() {
    let mut start = RelStartBound::InfinitePast;
    let mut end = RelEndBound::InfiniteFuture;

    let was_changed = prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, RelStartBound::InfinitePast);
    assert_eq!(end, RelEndBound::InfiniteFuture);
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_inf_past_finite() {
    let mut start = RelStartBound::InfinitePast;
    let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    let was_changed = prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, RelStartBound::InfinitePast);
    assert_eq!(
        end,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_inf_future() {
    let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end = RelEndBound::InfiniteFuture;

    let was_changed = prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(end, RelEndBound::InfiniteFuture);
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_correct_order() {
    let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();

    let was_changed = prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(
        end,
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound();
    let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    let was_changed = prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(
        end,
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    let was_changed = prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(
        end,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    let mut end =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_end_bound();

    let was_changed = prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
    );
    assert_eq!(
        end,
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
    );
}

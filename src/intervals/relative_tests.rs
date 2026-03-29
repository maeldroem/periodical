use jiff::SignedDuration;

use crate::intervals::meta::BoundInclusivity;

use super::relative::*;

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
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
    ));

    swap_relative_bound_pair(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ))
    );
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn relative_start_bound_finite_relative_end_bound_inf_swap() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
    ));
    let mut end = RelativeEndBound::InfiniteFuture;

    swap_relative_bound_pair(&mut start, &mut end);

    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ))
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_swap() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
    ));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        SignedDuration::from_hours(2),
        BoundInclusivity::Inclusive,
    ));

    swap_relative_bound_pair(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ))
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
            &RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_inf_future() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            &RelativeEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_correct_order() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(2))),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(2))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
        ),
        Err(RelativeBoundPairCheckForIntervalCreationError::StartPastEnd),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    assert_eq!(
        check_relative_bound_pair_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )),
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
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_inf_future() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
    let mut end = RelativeEndBound::InfiniteFuture;

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_correct_order() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(2)));

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(2)))
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(2)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
    assert_eq!(
        end,
        RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(2)))
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
}

#[test]
fn prepare_relative_bound_pair_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
    ));

    let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
    assert_eq!(
        end,
        RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1)))
    );
}

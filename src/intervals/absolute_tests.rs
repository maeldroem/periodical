use std::error::Error;

use jiff::Timestamp;

use super::absolute::*;
use crate::intervals::meta::BoundInclusivity;

#[test]
fn absolute_start_bound_inf_absolute_end_bound_inf_swap() {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::InfiniteFuture;

    swap_absolute_start_end_bounds(&mut start, &mut end);

    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_finite_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteFiniteBoundPosition::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    swap_absolute_start_end_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
    );
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);

    Ok(())
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_inf_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteFiniteBoundPosition::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let mut end = AbsoluteEndBound::InfiniteFuture;

    swap_absolute_start_end_bounds(&mut start, &mut end);

    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
    );

    Ok(())
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteFiniteBoundPosition::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let mut end = AbsoluteFiniteBoundPosition::new_with_inclusivity(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    swap_absolute_start_end_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound()
    );
    assert_eq!(
        end,
        AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_inf_past_inf_future() {
    assert_eq!(
        check_absolute_start_end_bounds_for_interval_creation(
            &AbsoluteStartBound::InfinitePast,
            &AbsoluteEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_inf_past_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_start_end_bounds_for_interval_creation(
            &AbsoluteStartBound::InfinitePast,
            &AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_inf_future() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_start_end_bounds_for_interval_creation(
            &AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsoluteEndBound::InfiniteFuture,
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_different_times_correct_order()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_start_end_bounds_for_interval_creation(
            &AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_different_times_wrong_order()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_start_end_bounds_for_interval_creation(
            &AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Err(AbsoluteStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_inclusive()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_start_end_bounds_for_interval_creation(
            &AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_exclusive()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_start_end_bounds_for_interval_creation(
            &AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        Err(AbsoluteStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_inf_past_inf_future() {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::InfiniteFuture;

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_inf_past_finite() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_inf_future() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsoluteEndBound::InfiniteFuture;

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_different_times_correct_order()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_different_times_wrong_order()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_inclusive()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_exclusive()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsoluteFiniteBoundPosition::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

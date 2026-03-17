use std::error::Error;

use jiff::Timestamp;

use crate::intervals::meta::BoundInclusivity;

use super::absolute::*;

#[test]
fn absolute_start_bound_inf_absolute_end_bound_inf_swap() {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::InfiniteFuture;

    swap_absolute_bound_pair(&mut start, &mut end);

    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_finite_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    ));

    swap_absolute_bound_pair(&mut start, &mut end);

    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ))
    );
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);

    Ok(())
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_inf_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    ));
    let mut end = AbsoluteEndBound::InfiniteFuture;

    swap_absolute_bound_pair(&mut start, &mut end);

    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ))
    );

    Ok(())
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    ));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    ));

    swap_absolute_bound_pair(&mut start, &mut end);

    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ))
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_inf_past_inf_future() {
    assert_eq!(
        check_absolute_bound_pair_for_interval_creation(
            &AbsoluteStartBound::InfinitePast,
            &AbsoluteEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_inf_past_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_bound_pair_for_interval_creation(
            &AbsoluteStartBound::InfinitePast,
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_inf_future() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_bound_pair_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
            &AbsoluteEndBound::InfiniteFuture,
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_different_times_correct_order() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_bound_pair_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_different_times_wrong_order() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_bound_pair_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        ),
        Err(AbsoluteBoundPairCheckForIntervalCreationError::StartPastEnd),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_bound_pair_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_absolute_bound_pair_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )),
        ),
        Err(AbsoluteBoundPairCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
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
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?));

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_inf_future() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?));
    let mut end = AbsoluteEndBound::InfiniteFuture;

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_different_times_correct_order() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?));

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?))
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_different_times_wrong_order() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?));

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );
    assert_eq!(
        end,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?))
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?));

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    ));

    let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );
    assert_eq!(
        end,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?))
    );

    Ok(())
}

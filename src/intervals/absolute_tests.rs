use std::error::Error;

use jiff::Timestamp;

use super::absolute::*;
use crate::intervals::meta::BoundInclusivity;

#[test]
fn absolute_start_bound_inf_absolute_end_bound_inf_swap() {
    let mut start = AbsStartBound::InfinitePast;
    let mut end = AbsEndBound::InfiniteFuture;

    swap_abs_start_end_bounds(&mut start, &mut end);

    assert_eq!(start, AbsStartBound::InfinitePast);
    assert_eq!(end, AbsEndBound::InfiniteFuture);
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_finite_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsStartBound::InfinitePast;
    let mut end = AbsFiniteBoundPos::new_with_incl(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    swap_abs_start_end_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
    );
    assert_eq!(end, AbsEndBound::InfiniteFuture);

    Ok(())
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_inf_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsFiniteBoundPos::new_with_incl(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let mut end = AbsEndBound::InfiniteFuture;

    swap_abs_start_end_bounds(&mut start, &mut end);

    assert_eq!(start, AbsStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
    );

    Ok(())
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_swap() -> Result<(), Box<dyn Error>> {
    let mut start = AbsFiniteBoundPos::new_with_incl(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let mut end = AbsFiniteBoundPos::new_with_incl(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    swap_abs_start_end_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound()
    );
    assert_eq!(
        end,
        AbsFiniteBoundPos::new_with_incl(
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
        check_abs_start_end_bounds_for_interval_creation(&AbsStartBound::InfinitePast, &AbsEndBound::InfiniteFuture,),
        Ok(()),
    );
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_inf_past_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_abs_start_end_bounds_for_interval_creation(
            &AbsStartBound::InfinitePast,
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_inf_future() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_abs_start_end_bounds_for_interval_creation(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsEndBound::InfiniteFuture,
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_different_times_correct_order()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_abs_start_end_bounds_for_interval_creation(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_different_times_wrong_order()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_abs_start_end_bounds_for_interval_creation(
            &AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_inclusive()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_abs_start_end_bounds_for_interval_creation(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        Ok(()),
    );

    Ok(())
}

#[test]
fn check_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_exclusive()
-> Result<(), Box<dyn Error>> {
    assert_eq!(
        check_abs_start_end_bounds_for_interval_creation(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            &AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_inf_past_inf_future() {
    let mut start = AbsStartBound::InfinitePast;
    let mut end = AbsEndBound::InfiniteFuture;

    let was_changed = prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, AbsStartBound::InfinitePast);
    assert_eq!(end, AbsEndBound::InfiniteFuture);
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_inf_past_finite() -> Result<(), Box<dyn Error>> {
    let mut start = AbsStartBound::InfinitePast;
    let mut end = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, AbsStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_inf_future() -> Result<(), Box<dyn Error>> {
    let mut start = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsEndBound::InfiniteFuture;

    let was_changed = prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(end, AbsEndBound::InfiniteFuture);

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_different_times_correct_order()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_different_times_wrong_order()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_inclusive()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let was_changed = prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

#[test]
fn prepare_absolute_bound_pair_for_interval_creation_finite_finite_same_time_inclusive_exclusive()
-> Result<(), Box<dyn Error>> {
    let mut start = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let mut end = AbsFiniteBoundPos::new_with_incl(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let was_changed = prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        end,
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );

    Ok(())
}

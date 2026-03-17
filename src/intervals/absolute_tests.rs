use std::cmp::Ordering;
use std::ops::Bound;

use chrono::{DateTime, Datelike, Duration, FixedOffset, Month, NaiveDate, Utc, Weekday};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::test_utils::{date, datetime};
use crate::time::{CalendarAnchorOffset, MonthInYear};

use super::absolute::*;

#[test]
fn absolute_start_bound_inf_absolute_end_bound_inf_swap() {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::InfiniteFuture;

    swap_absolute_bounds(&mut start, &mut end);

    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_finite_swap() {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));

    swap_absolute_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
    );
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_inf_swap() {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));
    let mut end = AbsoluteEndBound::InfiniteFuture;

    swap_absolute_bounds(&mut start, &mut end);

    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_swap() {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Inclusive,
    ));

    swap_absolute_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
    );
}

#[test]
fn check_absolute_bounds_for_interval_creation_inf_past_inf_future() {
    assert_eq!(
        check_absolute_bounds_for_interval_creation(
            &AbsoluteStartBound::InfinitePast,
            &AbsoluteEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_absolute_bounds_for_interval_creation_inf_past_finite() {
    assert_eq!(
        check_absolute_bounds_for_interval_creation(
            &AbsoluteStartBound::InfinitePast,
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        Ok(()),
    );
}

#[test]
fn check_absolute_bounds_for_interval_creation_finite_inf_future() {
    assert_eq!(
        check_absolute_bounds_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            &AbsoluteEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_absolute_bounds_for_interval_creation_finite_finite_different_times_correct_order() {
    assert_eq!(
        check_absolute_bounds_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        ),
        Ok(()),
    );
}

#[test]
fn check_absolute_bounds_for_interval_creation_finite_finite_different_times_wrong_order() {
    assert_eq!(
        check_absolute_bounds_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        Err(AbsoluteBoundsCheckForIntervalCreationError::StartPastEnd),
    );
}

#[test]
fn check_absolute_bounds_for_interval_creation_finite_finite_same_time_inclusive_inclusive() {
    assert_eq!(
        check_absolute_bounds_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        Ok(()),
    );
}

#[test]
fn check_absolute_bounds_for_interval_creation_finite_finite_same_time_inclusive_exclusive() {
    assert_eq!(
        check_absolute_bounds_for_interval_creation(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
        ),
        Err(AbsoluteBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
    );
}

#[test]
fn prepare_absolute_bounds_for_interval_creation_inf_past_inf_future() {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::InfiniteFuture;

    let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn prepare_absolute_bounds_for_interval_creation_inf_past_finite() {
    let mut start = AbsoluteStartBound::InfinitePast;
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));

    let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(start, AbsoluteStartBound::InfinitePast);
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
}

#[test]
fn prepare_absolute_bounds_for_interval_creation_finite_inf_future() {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));
    let mut end = AbsoluteEndBound::InfiniteFuture;

    let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
    assert_eq!(end, AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn prepare_absolute_bounds_for_interval_creation_finite_finite_different_times_correct_order() {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)));

    let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
    );
}

#[test]
fn prepare_absolute_bounds_for_interval_creation_finite_finite_different_times_wrong_order() {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));

    let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
    assert_eq!(
        end,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
    );
}

#[test]
fn prepare_absolute_bounds_for_interval_creation_finite_finite_same_time_inclusive_inclusive() {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));

    let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);

    assert!(!was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
    assert_eq!(
        end,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
}

#[test]
fn prepare_absolute_bounds_for_interval_creation_finite_finite_same_time_inclusive_exclusive() {
    let mut start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));
    let mut end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));

    let was_changed = prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);

    assert!(was_changed);
    assert_eq!(
        start,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
    assert_eq!(
        end,
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
}

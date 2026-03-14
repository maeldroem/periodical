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
fn absolute_bound_is_start() {
    assert!(AbsoluteBound::Start(AbsoluteStartBound::InfinitePast).is_start());
    assert!(!AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture).is_start());
}

#[test]
fn absolute_bound_is_end() {
    assert!(!AbsoluteBound::Start(AbsoluteStartBound::InfinitePast).is_end());
    assert!(AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture).is_end());
}

#[test]
fn absolute_bound_start() {
    assert_eq!(
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
        .start(),
        Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
    );
    assert_eq!(
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
        .start(),
        None,
    );
}

#[test]
fn absolute_bound_end() {
    assert_eq!(
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
        .end(),
        None,
    );
    assert_eq!(
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
        .end(),
        Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
    );
}

#[test]
fn absolute_bound_start_inf_past_opposite() {
    assert_eq!(AbsoluteBound::Start(AbsoluteStartBound::InfinitePast).opposite(), None,);
}

#[test]
fn absolute_bound_start_finite_opposite() {
    assert_eq!(
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
        .opposite(),
        Some(AbsoluteBound::End(AbsoluteEndBound::Finite(
            AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive,)
        ))),
    );
}

#[test]
fn absolute_bound_end_inf_future_opposite() {
    assert_eq!(AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture).opposite(), None,);
}

#[test]
fn absolute_bound_end_finite_opposite() {
    assert_eq!(
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
        .opposite(),
        Some(AbsoluteBound::Start(AbsoluteStartBound::Finite(
            AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive,)
        ))),
    );
}

#[test]
fn absolute_bound_from_absolute_start_bound() {
    assert_eq!(
        AbsoluteBound::from(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
    );
}

#[test]
fn absolute_bound_from_absolute_end_bound() {
    assert_eq!(
        AbsoluteBound::from(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
    );
}

#[test]
fn absolute_bounds_unchecked_new() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));

    let abs_bounds = AbsoluteBounds::unchecked_new(start, end);

    assert_eq!(abs_bounds.abs_start(), start);
    assert_eq!(abs_bounds.abs_end(), end);
}

#[test]
fn absolute_bounds_new_should_swap() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));

    let abs_bounds = AbsoluteBounds::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
    );
}

#[test]
fn absolute_bounds_new_from_same_times_exclusive_bounds() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));

    let abs_bounds = AbsoluteBounds::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn absolute_bounds_new_from_same_times_inclusive_exclusive_bounds() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    ));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));

    let abs_bounds = AbsoluteBounds::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn absolute_bounds_new_from_same_times_exclusive_inclusive_bounds() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    ));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    ));

    let abs_bounds = AbsoluteBounds::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn absolute_bounds_new_from_same_times_inclusive_bounds() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    ));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    ));

    let abs_bounds = AbsoluteBounds::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn absolute_bounds_unchecked_set_start() {
    let mut bounds = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
    );

    let new_start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)));

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.abs_start(), new_start);
}

#[test]
fn absolute_bounds_unchecked_set_end() {
    let mut bounds = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
    );

    let new_end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.abs_end(), new_end);
}

#[test]
fn absolute_bounds_set_start() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)));
    let mut bounds = AbsoluteBounds::new(start, end);

    assert!(
        !bounds.set_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 3
        ))))
    );

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
}

#[test]
fn absolute_bounds_set_end() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)));
    let mut bounds = AbsoluteBounds::new(start, end);

    assert!(!bounds.set_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
        &Utc, 2025, 1, 1
    )))));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
}

#[test]
fn absolute_bounds_unbounded_absolute_bounds_unbounded_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn absolute_bounds_unbounded_absolute_bounds_half_bounded_to_future_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_unbounded_absolute_bounds_half_bounded_to_past_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn absolute_bounds_unbounded_absolute_bounds_bounded_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_unbounded_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_future_after_first_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_future_before_first_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_future_same_time_exclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_future_same_time_exclusive_inclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_future_same_time_inclusive_exclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_future_same_time_inclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_past_before_first_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_past_after_first_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_past_same_time_exclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_past_same_time_exclusive_inclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_past_same_time_inclusive_exclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_to_past_same_time_inclusive_bounds_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_bounded_starts_before_first_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_bounded_to_future_absolute_bounds_bounded_starts_after_first_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_from_bound_pair() {
    assert_eq!(
        AbsoluteBounds::from((Bound::Excluded(date(&Utc, 2025, 1, 1)), Bound::Unbounded)),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        ),
    );
}

#[test]
fn absolute_bounds_try_from_emptiable_absolute_bounds_correct_variant() {
    assert_eq!(
        AbsoluteBounds::try_from(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        ))),
        Ok(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn absolute_bounds_try_from_emptiable_absolute_bounds_wrong_variant() {
    assert_eq!(
        AbsoluteBounds::try_from(EmptiableAbsoluteBounds::Empty),
        Err(AbsoluteBoundsFromEmptiableAbsoluteBoundsError::EmptyVariant),
    );
}

#[test]
fn emptiable_absolute_bounds_from_absolute_bounds() {
    assert_eq!(
        EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn bounded_absolute_interval_unchecked_new() {
    let interval = BoundedAbsoluteInterval::unchecked_new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_interval_new_no_swap() {
    let interval = BoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_interval_new_swap() {
    let interval = BoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 2), date(&Utc, 2025, 1, 1));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_interval_new_with_inclusivity_no_swap() {
    let interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_interval_new_with_inclusivity_swap() {
    let interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let date = NaiveDate::from_ymd_opt(2026, 1, 5).unwrap();

    let interval = BoundedAbsoluteInterval::from_date(date, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 5, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_max_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let date = NaiveDate::MAX;

    assert_eq!(
        BoundedAbsoluteInterval::from_date(date, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)
    );
}

#[test]
fn bounded_absolute_interval_day_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = BoundedAbsoluteInterval::day_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 4, 29).unwrap(),
        CalendarAnchorOffset::Days(5),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 5, 3, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 4, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_day_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = BoundedAbsoluteInterval::day_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 4, 29).unwrap(),
        CalendarAnchorOffset::Days(5),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 4, 23, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 4, 24, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 5).unwrap();
    let to = NaiveDate::from_ymd_opt(2026, 1, 10).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_date_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 10, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range_max_from_and_to() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    assert_eq!(
        BoundedAbsoluteInterval::from_inclusive_date_range(NaiveDate::MAX, NaiveDate::MAX, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)
    );
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range_max_to() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 1).unwrap();

    assert_eq!(
        BoundedAbsoluteInterval::from_inclusive_date_range(from, NaiveDate::MAX, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)
    );
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range_reversed_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 10).unwrap();
    let to = NaiveDate::from_ymd_opt(2026, 1, 5).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_date_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 10, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().week(Weekday::Tue);

    let week_interval = BoundedAbsoluteInterval::from_week(week, offset_tz).unwrap();

    assert_eq!(week_interval.from_time(), datetime(&Utc, 2026, 4, 27, 22, 0, 0));
    assert_eq!(week_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week_interval.to_time(), datetime(&Utc, 2026, 5, 4, 22, 0, 0));
    assert_eq!(week_interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_week_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().week(Weekday::Mon);
    let to = NaiveDate::from_ymd_opt(2026, 3, 17).unwrap().week(Weekday::Sat);

    let interval = BoundedAbsoluteInterval::from_inclusive_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 3, 20, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_week_range_same_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().week(Weekday::Mon);

    let interval = BoundedAbsoluteInterval::from_inclusive_week_range(week, week, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 11, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_week_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 2, 20).unwrap().week(Weekday::Tue);
    let to = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().week(Weekday::Sat);

    let interval = BoundedAbsoluteInterval::from_inclusive_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 2, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 2, 23, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::week_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::Weeks(Weekday::Mon, 2),
        Weekday::Mon,
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 5, 10, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 5, 17, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::week_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::Weeks(Weekday::Mon, 2),
        Weekday::Mon,
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 4, 12, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 4, 19, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_iso_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let iso_week = NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().iso_week();

    let iso_week_interval = BoundedAbsoluteInterval::from_iso_week(iso_week, offset_tz).unwrap();

    assert_eq!(iso_week_interval.from_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(iso_week_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(iso_week_interval.to_time(), datetime(&Utc, 2026, 5, 3, 22, 0, 0));
    assert_eq!(iso_week_interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_iso_week_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().iso_week();
    let to = NaiveDate::from_ymd_opt(2026, 3, 17).unwrap().iso_week();

    let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 3, 22, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_iso_week_range_same_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().iso_week();

    let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(week, week, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 11, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_iso_week_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 3, 17).unwrap().iso_week();
    let to = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().iso_week();

    let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 3, 22, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_from_iso_year_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let iso_week = BoundedAbsoluteInterval::week_from_iso_year_week(2026, 5, offset_tz).unwrap();

    assert_eq!(iso_week.from_time(), datetime(&Utc, 2026, 1, 25, 22, 0, 0));
    assert_eq!(iso_week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(iso_week.to_time(), datetime(&Utc, 2026, 2, 1, 22, 0, 0));
    assert_eq!(iso_week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_from_iso_year_week_invalid_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    assert_eq!(
        BoundedAbsoluteInterval::week_from_iso_year_week(2026, 60, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::DateOperationError),
    );
}

#[test]
fn bounded_absolute_interval_iso_week_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::iso_week_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::IsoWeeks(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 5, 10, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 5, 17, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_iso_week_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::iso_week_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::IsoWeeks(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 4, 12, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 4, 19, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_from_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let month = BoundedAbsoluteInterval::from_month(MonthInYear::new(2026, Month::May), offset_tz).unwrap();

    assert_eq!(month.from_time(), datetime(&Utc, 2026, 4, 30, 22, 0, 0));
    assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(month.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_month_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_month_range(
        MonthInYear::new(2026, Month::January),
        MonthInYear::new(2026, Month::May),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_month_range_same_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let month = MonthInYear::new(2026, Month::May);

    let interval = BoundedAbsoluteInterval::from_inclusive_month_range(month, month, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 4, 30, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_month_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_month_range(
        MonthInYear::new(2026, Month::May),
        MonthInYear::new(2026, Month::January),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_month_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let month = BoundedAbsoluteInterval::month_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(month.from_time(), datetime(&Utc, 2026, 6, 30, 22, 0, 0));
    assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(month.to_time(), datetime(&Utc, 2026, 7, 31, 22, 0, 0));
    assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_month_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let month = BoundedAbsoluteInterval::month_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(month.from_time(), datetime(&Utc, 2026, 2, 28, 22, 0, 0));
    assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(month.to_time(), datetime(&Utc, 2026, 3, 31, 22, 0, 0));
    assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_year_common() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let year = BoundedAbsoluteInterval::from_year(2026, offset_tz).unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2026, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_year_leap() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let year = BoundedAbsoluteInterval::from_year(2028, offset_tz).unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2027, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2028, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_year_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let years = BoundedAbsoluteInterval::from_inclusive_year_range(2025, 2030, offset_tz).unwrap();

    assert_eq!(years.from_time(), datetime(&Utc, 2024, 12, 31, 22, 0, 0));
    assert_eq!(years.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(years.to_time(), datetime(&Utc, 2030, 12, 31, 22, 0, 0));
    assert_eq!(years.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_year_range_same_year() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let year = BoundedAbsoluteInterval::from_inclusive_year_range(2030, 2030, offset_tz).unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2029, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2030, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_year_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let years = BoundedAbsoluteInterval::from_inclusive_year_range(2030, 2025, offset_tz).unwrap();

    assert_eq!(years.from_time(), datetime(&Utc, 2024, 12, 31, 22, 0, 0));
    assert_eq!(years.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(years.to_time(), datetime(&Utc, 2030, 12, 31, 22, 0, 0));
    assert_eq!(years.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_year_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let year = BoundedAbsoluteInterval::year_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(15),
        offset_tz,
    )
    .unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2026, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2027, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_year_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let year = BoundedAbsoluteInterval::year_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(15),
        offset_tz,
    )
    .unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2024, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_unchecked_set_from() {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_from(date(&Utc, 2025, 1, 3));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 3));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_unchecked_set_to() {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 3),
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_to(date(&Utc, 2025, 1, 1));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_set_from() {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Inclusive,
    );

    assert!(!interval.set_from(date(&Utc, 2025, 1, 3)));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_set_to() {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 3),
        BoundInclusivity::Inclusive,
    );

    assert!(!interval.set_to(date(&Utc, 2025, 1, 1)));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 3));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_set_from_inclusivity() {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Inclusive,
    );

    interval.set_from_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_absolute_set_to_inclusivity() {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Exclusive,
        date(&Utc, 2025, 1, 3),
        BoundInclusivity::Inclusive,
    );

    interval.set_to_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 3));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_datetime_pair_swap() {
    assert_eq!(
        BoundedAbsoluteInterval::from((date(&Utc, 2025, 1, 2), date(&Utc, 2025, 1, 1))),
        BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        ),
    );
}

#[test]
fn bounded_absolute_interval_from_pair_of_datetime_inclusivity_pairs_swap() {
    assert_eq!(
        BoundedAbsoluteInterval::from((
            (date(&Utc, 2025, 1, 2), BoundInclusivity::Exclusive),
            (date(&Utc, 2025, 1, 1), BoundInclusivity::Inclusive),
        )),
        BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn bounded_absolute_interval_from_pair_of_datetime_bool_pairs_swap() {
    assert_eq!(
        BoundedAbsoluteInterval::from(((date(&Utc, 2025, 1, 2), false), (date(&Utc, 2025, 1, 1), true),)),
        BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn bounded_absolute_interval_from_range() {
    assert_eq!(
        BoundedAbsoluteInterval::from(date(&Utc, 2025, 1, 1)..date(&Utc, 2025, 1, 2)),
        BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn bounded_absolute_interval_from_range_inclusive() {
    assert_eq!(
        BoundedAbsoluteInterval::from(date(&Utc, 2025, 1, 1)..=date(&Utc, 2025, 1, 2)),
        BoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)),
    );
}

#[test]
fn bounded_absolute_interval_try_from_absolute_bounds_correct() {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        )),
        Ok(BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn bounded_absolute_interval_try_from_absolute_bounds_wrong() {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        )),
        Err(BoundedAbsoluteIntervalFromAbsoluteBoundsError::NotBoundedInterval),
    );
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(BoundedAbsoluteIntervalFromAbsoluteBoundsError::NotBoundedInterval),
    );
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(BoundedAbsoluteIntervalFromAbsoluteBoundsError::NotBoundedInterval),
    );
}

#[test]
fn bounded_absolute_interval_try_from_absolute_interval_correct() {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        ))),
        Ok(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
    );
}

#[test]
fn bounded_absolute_interval_try_from_absolute_interval_wrong() {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteInterval::Empty(EmptyInterval)),
        Err(BoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteInterval::Unbounded(UnboundedInterval)),
        Err(BoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToFuture,
        ))),
        Err(BoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
}

#[test]
fn half_bounded_absolute_interval_new() {
    let interval = HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture);

    assert_eq!(interval.reference_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn half_bounded_absolute_interval_new_with_inclusivity() {
    let interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.reference_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn half_bounded_absolute_interval_since_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from_first_of_may =
        HalfBoundedAbsoluteInterval::since_date(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(), offset_tz).unwrap();

    assert_eq!(
        from_first_of_may.reference_time(),
        datetime(&Utc, 2026, 4, 30, 22, 0, 0)
    );
    assert_eq!(from_first_of_may.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(from_first_of_may.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let until_first_of_may =
        HalfBoundedAbsoluteInterval::until_date(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(), offset_tz).unwrap();

    assert_eq!(
        until_first_of_may.reference_time(),
        datetime(&Utc, 2026, 4, 30, 22, 0, 0)
    );
    assert_eq!(until_first_of_may.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_first_of_may.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = HalfBoundedAbsoluteInterval::since_week(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().week(Weekday::Mon),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = HalfBoundedAbsoluteInterval::until_week(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().week(Weekday::Mon),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_iso_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval =
        HalfBoundedAbsoluteInterval::since_iso_week(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().iso_week(), offset_tz)
            .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_iso_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval =
        HalfBoundedAbsoluteInterval::until_iso_week(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().iso_week(), offset_tz)
            .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let since_month = HalfBoundedAbsoluteInterval::since_month(MonthInYear::new(2026, Month::March), offset_tz).unwrap();

    assert_eq!(since_month.reference_time(), datetime(&Utc, 2026, 2, 28, 22, 0, 0));
    assert_eq!(since_month.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(since_month.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let until_month = HalfBoundedAbsoluteInterval::until_month(MonthInYear::new(2026, Month::March), offset_tz).unwrap();

    assert_eq!(until_month.reference_time(), datetime(&Utc, 2026, 2, 28, 22, 0, 0));
    assert_eq!(until_month.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_month.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_year() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let since_year = HalfBoundedAbsoluteInterval::since_year(2026, offset_tz).unwrap();

    assert_eq!(since_year.reference_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(since_year.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(since_year.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_year() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let until_year = HalfBoundedAbsoluteInterval::until_year(2026, offset_tz).unwrap();

    assert_eq!(until_year.reference_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(until_year.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_year.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_set_reference_time() {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_time(date(&Utc, 2025, 1, 2));

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn half_bounded_absolute_interval_set_reference_time_inclusivity() {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn half_bounded_absolute_interval_set_opening_direction() {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );
}

#[test]
fn half_bounded_absolute_interval_from_datetime_opening_direction_pair() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from((date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture)),
        HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture),
    );
}

#[test]
fn half_bounded_absolute_interval_from_datetime_bool_pair() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from((date(&Utc, 2025, 1, 1), false)),
        HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToPast),
    );
}

#[test]
fn half_bounded_absolute_interval_from_pair_of_datetime_bound_inclusivity_pair_and_opening_direction() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from((
            (date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive),
            OpeningDirection::ToPast
        )),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_absolute_interval_from_pair_of_datetime_bool_pair_and_opening_direction() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(((date(&Utc, 2025, 1, 1), false), OpeningDirection::ToPast)),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_absolute_interval_from_pair_of_datetime_bool_pair_and_bool() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(((date(&Utc, 2025, 1, 1), false), false)),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_absolute_interval_from_range_from() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(date(&Utc, 2025, 1, 1)..),
        HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture),
    );
}

#[test]
fn half_bounded_absolute_interval_from_range_to() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(..date(&Utc, 2025, 1, 1)),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_absolute_interval_from_range_to_inclusive() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(..=date(&Utc, 2025, 1, 1)),
        HalfBoundedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToPast),
    );
}

#[test]
fn half_bounded_absolute_interval_try_from_absolute_bounds_correct() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
        )),
        Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn half_bounded_absolute_interval_try_from_absolute_bounds_wrong() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError::NotHalfBoundedInterval),
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        )),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError::NotHalfBoundedInterval),
    );
}

#[test]
fn half_bounded_absolute_interval_try_from_absolute_interval_correct() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
        Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn half_bounded_absolute_interval_try_from_absolute_interval_wrong() {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteInterval::Empty(EmptyInterval)),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteInterval::Unbounded(UnboundedInterval)),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        ))),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
}

#[test]
fn absolute_interval_from_absolute_bounds() {
    assert_eq!(
        AbsoluteInterval::from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn absolute_interval_from_emptiable_absolute_bounds() {
    assert_eq!(
        AbsoluteInterval::from(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        ))),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn absolute_interval_from_opt_datetime_pair_unbounded() {
    assert_eq!(
        <AbsoluteInterval as From<(Option<DateTime<Utc>>, Option<DateTime<Utc>>)>>::from((None, None)),
        AbsoluteInterval::Unbounded(UnboundedInterval),
    );
}

#[test]
fn absolute_interval_from_opt_datetime_pair_half_bounded() {
    assert_eq!(
        AbsoluteInterval::from((None, Some(date(&Utc, 2025, 1, 1)))),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn absolute_interval_from_opt_datetime_bound_inclusivity_pairs() {
    assert_eq!(
        AbsoluteInterval::from((
            Some((date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive)),
            Some((date(&Utc, 2025, 1, 2), BoundInclusivity::Exclusive)),
        )),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_interval_from_opt_datetime_bool_pairs() {
    assert_eq!(
        AbsoluteInterval::from((
            Some((date(&Utc, 2025, 1, 1), true)),
            Some((date(&Utc, 2025, 1, 2), false)),
        )),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_interval_from_bool_and_two_opt_datetime_empty() {
    assert_eq!(
        <AbsoluteInterval as From<(bool, Option<DateTime<Utc>>, Option<DateTime<Utc>>)>>::from((true, None, None,)),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn absolute_interval_from_bool_and_two_opt_datetime() {
    assert_eq!(
        AbsoluteInterval::from((false, Some(date(&Utc, 2025, 1, 1)), Some(date(&Utc, 2025, 1, 2)),)),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2)
        )),
    );
}

#[test]
fn absolute_interval_from_bool_and_two_opt_datetime_bound_inclusivity_empty() {
    assert_eq!(
        <AbsoluteInterval as From<(
            bool,
            Option<(DateTime<Utc>, BoundInclusivity)>,
            Option<(DateTime<Utc>, BoundInclusivity)>
        )>>::from((true, None, None,)),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn absolute_interval_from_bool_and_two_opt_datetime_bound_inclusivity() {
    assert_eq!(
        AbsoluteInterval::from((
            false,
            Some((date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive)),
            Some((date(&Utc, 2025, 1, 2), BoundInclusivity::Exclusive)),
        )),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_interval_from_bool_and_two_opt_datetime_bool_empty() {
    assert_eq!(
        <AbsoluteInterval as From<(bool, Option<(DateTime<Utc>, bool)>, Option<(DateTime<Utc>, bool)>)>>::from((
            true, None, None,
        )),
        AbsoluteInterval::Empty(EmptyInterval),
    );
}

#[test]
fn absolute_interval_from_bool_and_two_opt_datetime_bool() {
    assert_eq!(
        AbsoluteInterval::from((
            false,
            Some((date(&Utc, 2025, 1, 1), false)),
            Some((date(&Utc, 2025, 1, 2), false)),
        )),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_interval_from_bound_pair() {
    assert_eq!(
        AbsoluteInterval::from((Bound::Unbounded, Bound::Excluded(date(&Utc, 2025, 1, 1)))),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
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

use std::cmp::Ordering;
use std::ops::Bound;

use chrono::{DateTime, Utc};

use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::prelude::HasBoundInclusivity;
use crate::test_utils::date;

use super::absolute::*;

#[test]
fn absolute_finite_bound_new() {
    let abs_finite_bound = AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1));

    assert_eq!(abs_finite_bound.time(), date(&Utc, 2025, 1, 1));
    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn absolute_finite_bound_new_with_inclusivity() {
    let abs_finite_bound =
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive);

    assert_eq!(abs_finite_bound.time(), date(&Utc, 2025, 1, 1));
    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn absolute_finite_bound_set_time() {
    let mut abs_finite_bound = AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1));

    abs_finite_bound.set_time(date(&Utc, 2025, 5, 1));

    assert_eq!(abs_finite_bound.time(), date(&Utc, 2025, 5, 1));
}

#[test]
fn absolute_finite_bound_set_inclusivity() {
    let mut abs_finite_bound =
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive);

    abs_finite_bound.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn absolute_finite_bound_inclusivity() {
    let abs_finite_bound =
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive);

    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn absolute_finite_bound_cmp_greater_times() {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)),
        AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Greater);
}

#[test]
fn absolute_finite_bound_cmp_equal_times() {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)),
        AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Equal);
}

#[test]
fn absolute_finite_bound_cmp_equal_time_different_inclusivities() {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive),
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Inclusive),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Equal);
}

#[test]
fn absolute_finite_bound_cmp_less() {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)),
        AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Less);
}

#[test]
fn absolute_finite_bound_from_datetime() {
    assert_eq!(
        AbsoluteFiniteBound::from(date(&Utc, 2025, 1, 1)),
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Inclusive),
    );
}

#[test]
fn absolute_finite_bound_from_datetime_inclusivity_pair() {
    assert_eq!(
        AbsoluteFiniteBound::from((date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive)),
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn absolute_finite_bound_from_datetime_bool_pair() {
    assert_eq!(
        AbsoluteFiniteBound::from((date(&Utc, 2025, 1, 1), false)),
        AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn absolute_finite_bound_try_from_inclusive_bound() {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Included(date(&Utc, 2025, 1, 1))),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive
        )),
    );
}

#[test]
fn absolute_finite_bound_try_from_exclusive_bound() {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Excluded(date(&Utc, 2025, 1, 1))),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive
        )),
    );
}

#[test]
fn absolute_finite_bound_try_from_unbounded_bound() {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Unbounded),
        Err(AbsoluteFiniteBoundFromBoundError::IsUnbounded),
    );
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_inf_eq() {
    assert!(!AbsoluteStartBound::InfinitePast.eq(&AbsoluteEndBound::InfiniteFuture));
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_finite_eq() {
    assert!(
        !AbsoluteStartBound::InfinitePast.eq(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_inf_eq() {
    assert!(
        !AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .eq(&AbsoluteEndBound::InfiniteFuture)
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_different_times_eq() {
    assert!(
        !AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).eq(&AbsoluteEndBound::Finite(
            AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))
        )),
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_equal_times_exclusive_bounds_eq() {
    assert!(
        !AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_equal_times_exclusive_inclusive_bounds_eq() {
    assert!(
        !AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_equal_times_inclusive_exclusive_bounds_eq() {
    assert!(
        !AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_finite_equal_times_inclusive_bounds_eq() {
    assert!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn absolute_start_bound_inf_absolute_start_bound_inf_cmp() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.cmp(&AbsoluteStartBound::InfinitePast),
        Ordering::Equal
    );
}

#[test]
fn absolute_start_bound_inf_absolute_start_bound_finite_cmp() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        Ordering::Less,
    );
}

#[test]
fn absolute_start_bound_finite_absolute_start_bound_inf_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .cmp(&AbsoluteStartBound::InfinitePast),
        Ordering::Greater,
    );
}

#[test]
fn absolute_start_bound_different_times_cmp_greater() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))).cmp(&AbsoluteStartBound::Finite(
            AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))
        )),
        Ordering::Greater,
    );
}

#[test]
fn absolute_start_bound_different_times_cmp_less() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).cmp(&AbsoluteStartBound::Finite(
            AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))
        )),
        Ordering::Less,
    );
}

#[test]
fn absolute_start_bound_same_times_exclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn absolute_start_bound_same_times_exclusive_inclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Greater,
    );
}

#[test]
fn absolute_start_bound_same_times_inclusive_exclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Less,
    );
}

#[test]
fn absolute_start_bound_same_times_inclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_inf_partial_cmp() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.partial_cmp(&AbsoluteEndBound::InfiniteFuture),
        Some(Ordering::Less),
    );
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_finite_partial_cmp() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        Some(Ordering::Less),
    );
}

#[test]
fn absolute_start_bound_finite_absolute_end_bound_inf_partial_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .partial_cmp(&AbsoluteEndBound::InfiniteFuture),
        Some(Ordering::Less),
    );
}

#[test]
fn absolute_start_bound_absolute_end_bound_different_times_partial_cmp_greater() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))).partial_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        Some(Ordering::Greater),
    );
}

#[test]
fn absolute_start_bound_absolute_end_bound_different_times_partial_cmp_less() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).partial_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
        Some(Ordering::Less),
    );
}

#[test]
fn absolute_start_bound_absolute_end_bound_same_times_exclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        None,
    );
}

#[test]
fn absolute_start_bound_absolute_end_bound_same_times_exclusive_inclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        None,
    );
}

#[test]
fn absolute_start_bound_absolute_end_bound_same_times_inclusive_exclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        None,
    );
}

#[test]
fn absolute_start_bound_absolute_end_bound_same_times_inclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        Some(Ordering::Equal),
    );
}

#[test]
fn absolute_start_bound_from_absolute_finite_bound() {
    assert_eq!(
        AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_start_bound_from_inclusive_bound() {
    assert_eq!(
        AbsoluteStartBound::from(Bound::Included(date(&Utc, 2025, 1, 1))),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn absolute_start_bound_from_exclusive_bound() {
    assert_eq!(
        AbsoluteStartBound::from(Bound::Excluded(date(&Utc, 2025, 1, 1))),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_start_bound_from_unbounded_bound() {
    assert_eq!(
        AbsoluteStartBound::from(Bound::Unbounded),
        AbsoluteStartBound::InfinitePast
    );
}

#[test]
fn absolute_end_bound_inf_absolute_start_bound_inf_eq() {
    assert!(!AbsoluteEndBound::InfiniteFuture.eq(&AbsoluteStartBound::InfinitePast));
}

#[test]
fn absolute_end_bound_inf_absolute_start_bound_finite_eq() {
    assert!(
        !AbsoluteEndBound::InfiniteFuture.eq(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        ))))
    );
}

#[test]
fn absolute_end_bound_finite_absolute_start_bound_inf_eq() {
    assert!(
        !AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .eq(&AbsoluteStartBound::InfinitePast)
    );
}

#[test]
fn absolute_end_bound_finite_absolute_start_bound_finite_different_times_eq() {
    assert!(
        !AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).eq(&AbsoluteStartBound::Finite(
            AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))
        )),
    );
}

#[test]
fn absolute_end_bound_finite_absolute_start_bound_finite_equal_times_exclusive_bounds_eq() {
    assert!(
        !AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn absolute_end_bound_finite_absolute_start_bound_finite_equal_times_exclusive_inclusive_bounds_eq() {
    assert!(
        !AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn absolute_end_bound_finite_absolute_start_bound_finite_equal_times_inclusive_exclusive_bounds_eq() {
    assert!(
        !AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn absolute_end_bound_finite_absolute_start_bound_finite_equal_times_inclusive_bounds_eq() {
    assert!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn absolute_end_bound_inf_absolute_end_bound_inf_cmp() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.cmp(&AbsoluteEndBound::InfiniteFuture),
        Ordering::Equal
    );
}

#[test]
fn absolute_end_bound_inf_absolute_end_bound_finite_cmp() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        Ordering::Greater,
    );
}

#[test]
fn absolute_end_bound_finite_absolute_end_bound_inf_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .cmp(&AbsoluteEndBound::InfiniteFuture),
        Ordering::Less,
    );
}

#[test]
fn absolute_end_bound_different_times_cmp_greater() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))).cmp(&AbsoluteEndBound::Finite(
            AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))
        )),
        Ordering::Greater,
    );
}

#[test]
fn absolute_end_bound_different_times_cmp_less() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).cmp(&AbsoluteEndBound::Finite(
            AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))
        )),
        Ordering::Less,
    );
}

#[test]
fn absolute_end_bound_same_times_exclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn absolute_end_bound_same_times_exclusive_inclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Less,
    );
}

#[test]
fn absolute_end_bound_same_times_inclusive_exclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Greater,
    );
}

#[test]
fn absolute_end_bound_same_times_inclusive_bounds_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn absolute_end_bound_inf_absolute_start_bound_inf_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.partial_cmp(&AbsoluteStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
}

#[test]
fn absolute_end_bound_inf_absolute_start_bound_finite_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        Some(Ordering::Greater),
    );
}

#[test]
fn absolute_end_bound_finite_absolute_start_bound_inf_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .partial_cmp(&AbsoluteStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
}

#[test]
fn absolute_end_bound_absolute_start_bound_different_times_partial_cmp_greater() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))).partial_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        Some(Ordering::Greater),
    );
}

#[test]
fn absolute_end_bound_absolute_start_bound_different_times_partial_cmp_less() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).partial_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
        Some(Ordering::Less),
    );
}

#[test]
fn absolute_end_bound_absolute_start_bound_same_times_exclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        None,
    );
}

#[test]
fn absolute_end_bound_absolute_start_bound_same_times_exclusive_inclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        None,
    );
}

#[test]
fn absolute_end_bound_absolute_start_bound_same_times_inclusive_exclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        None,
    );
}

#[test]
fn absolute_end_bound_absolute_start_bound_same_times_inclusive_bounds_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
        Some(Ordering::Equal),
    );
}

#[test]
fn absolute_end_bound_from_absolute_finite_bound() {
    assert_eq!(
        AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_end_bound_from_inclusive_bound() {
    assert_eq!(
        AbsoluteEndBound::from(Bound::Included(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn absolute_end_bound_from_exclusive_bound() {
    assert_eq!(
        AbsoluteEndBound::from(Bound::Excluded(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn absolute_end_bound_from_unbounded_bound() {
    assert_eq!(
        AbsoluteEndBound::from(Bound::Unbounded),
        AbsoluteEndBound::InfiniteFuture
    );
}

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
fn absolute_bounds_open_absolute_bounds_open_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn absolute_bounds_open_absolute_bounds_half_open_to_future_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_open_absolute_bounds_half_open_to_past_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
    );

    // When starting on same point, the larger interval should come first
    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_open_absolute_bounds_closed_cmp() {
    let a = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn absolute_bounds_half_open_to_future_absolute_bounds_open_cmp() {
    let a = AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn absolute_bounds_half_open_to_future_absolute_bounds_to_future_after_first_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_future_before_first_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_future_same_time_exclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_future_same_time_exclusive_inclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_future_same_time_inclusive_exclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_future_same_time_inclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_past_before_first_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_past_after_first_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_past_same_time_exclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_past_same_time_exclusive_inclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_past_same_time_inclusive_exclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_to_past_same_time_inclusive_bounds_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_closed_starts_before_first_cmp() {
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
fn absolute_bounds_half_open_to_future_absolute_bounds_closed_starts_after_first_cmp() {
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
fn closed_absolute_interval_unchecked_new() {
    let interval = ClosedAbsoluteInterval::unchecked_new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn closed_absolute_interval_new_no_swap() {
    let interval = ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn closed_absolute_interval_new_swap() {
    let interval = ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 2), date(&Utc, 2025, 1, 1));

    assert_eq!(interval.from_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.to_time(), date(&Utc, 2025, 1, 2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn closed_absolute_interval_new_with_inclusivity_no_swap() {
    let interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_interval_new_with_inclusivity_swap() {
    let interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_unchecked_set_from() {
    let mut interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_unchecked_set_to() {
    let mut interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_set_from() {
    let mut interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_set_to() {
    let mut interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_set_from_inclusivity() {
    let mut interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_set_to_inclusivity() {
    let mut interval = ClosedAbsoluteInterval::new_with_inclusivity(
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
fn closed_absolute_interval_from_datetime_pair_swap() {
    assert_eq!(
        ClosedAbsoluteInterval::from((date(&Utc, 2025, 1, 2), date(&Utc, 2025, 1, 1))),
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        ),
    );
}

#[test]
fn closed_absolute_interval_from_pair_of_datetime_inclusivity_pairs_swap() {
    assert_eq!(
        ClosedAbsoluteInterval::from((
            (date(&Utc, 2025, 1, 2), BoundInclusivity::Exclusive),
            (date(&Utc, 2025, 1, 1), BoundInclusivity::Inclusive),
        )),
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn closed_absolute_interval_from_pair_of_datetime_bool_pairs_swap() {
    assert_eq!(
        ClosedAbsoluteInterval::from(((date(&Utc, 2025, 1, 2), false), (date(&Utc, 2025, 1, 1), true),)),
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn closed_absolute_interval_from_range() {
    assert_eq!(
        ClosedAbsoluteInterval::from(date(&Utc, 2025, 1, 1)..date(&Utc, 2025, 1, 2)),
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn closed_absolute_interval_from_range_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::from(date(&Utc, 2025, 1, 1)..=date(&Utc, 2025, 1, 2)),
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)),
    );
}

#[test]
fn closed_absolute_interval_try_from_absolute_bounds_correct() {
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        )),
        Ok(ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn closed_absolute_interval_try_from_absolute_bounds_wrong() {
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        )),
        Err(ClosedAbsoluteIntervalFromAbsoluteBoundsError::NotClosedInterval),
    );
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(ClosedAbsoluteIntervalFromAbsoluteBoundsError::NotClosedInterval),
    );
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(ClosedAbsoluteIntervalFromAbsoluteBoundsError::NotClosedInterval),
    );
}

#[test]
fn closed_absolute_interval_try_from_absolute_interval_correct() {
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        ))),
        Ok(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
    );
}

#[test]
fn closed_absolute_interval_try_from_absolute_interval_wrong() {
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteInterval::Empty(EmptyInterval)),
        Err(ClosedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteInterval::Open(OpenInterval)),
        Err(ClosedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        ClosedAbsoluteInterval::try_from(AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToFuture,
        ))),
        Err(ClosedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
}

#[test]
fn half_open_absolute_interval_new() {
    let interval = HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture);

    assert_eq!(interval.reference_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_time_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn half_open_absolute_interval_new_with_inclusivity() {
    let interval = HalfOpenAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.reference_time(), date(&Utc, 2025, 1, 1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    assert_eq!(interval.reference_time_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn half_open_absolute_interval_set_reference_time() {
    let mut interval = HalfOpenAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_time(date(&Utc, 2025, 1, 2));

    assert_eq!(
        interval,
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn half_open_absolute_interval_set_reference_time_inclusivity() {
    let mut interval = HalfOpenAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_time_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn half_open_absolute_interval_set_opening_direction() {
    let mut interval = HalfOpenAbsoluteInterval::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );
}

#[test]
fn half_open_absolute_interval_from_datetime_opening_direction_pair() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from((date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture)),
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture),
    );
}

#[test]
fn half_open_absolute_interval_from_datetime_bool_pair() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from((date(&Utc, 2025, 1, 1), false)),
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToPast),
    );
}

#[test]
fn half_open_absolute_interval_from_pair_of_datetime_bound_inclusivity_pair_and_opening_direction() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from((
            (date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive),
            OpeningDirection::ToPast
        )),
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_open_absolute_interval_from_pair_of_datetime_bool_pair_and_opening_direction() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from(((date(&Utc, 2025, 1, 1), false), OpeningDirection::ToPast)),
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_open_absolute_interval_from_pair_of_datetime_bool_pair_and_bool() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from(((date(&Utc, 2025, 1, 1), false), false)),
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_open_absolute_interval_from_range_from() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from(date(&Utc, 2025, 1, 1)..),
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture),
    );
}

#[test]
fn half_open_absolute_interval_from_range_to() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from(..date(&Utc, 2025, 1, 1)),
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_open_absolute_interval_from_range_to_inclusive() {
    assert_eq!(
        HalfOpenAbsoluteInterval::from(..=date(&Utc, 2025, 1, 1)),
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToPast),
    );
}

#[test]
fn half_open_absolute_interval_try_from_absolute_bounds_correct() {
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        Ok(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
        )),
        Ok(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn half_open_absolute_interval_try_from_absolute_bounds_wrong() {
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(HalfOpenAbsoluteIntervalFromAbsoluteBoundsError::NotHalfOpenInterval),
    );
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        )),
        Err(HalfOpenAbsoluteIntervalFromAbsoluteBoundsError::NotHalfOpenInterval),
    );
}

#[test]
fn half_open_absolute_interval_try_from_absolute_interval_correct() {
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteInterval::HalfOpen(
            HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
        Ok(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn half_open_absolute_interval_try_from_absolute_interval_wrong() {
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteInterval::Empty(EmptyInterval)),
        Err(HalfOpenAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteInterval::Open(OpenInterval)),
        Err(HalfOpenAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfOpenAbsoluteInterval::try_from(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        ))),
        Err(HalfOpenAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
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
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
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
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn absolute_interval_from_opt_datetime_pair_open() {
    assert_eq!(
        <AbsoluteInterval as From<(Option<DateTime<Utc>>, Option<DateTime<Utc>>)>>::from((None, None)),
        AbsoluteInterval::Open(OpenInterval),
    );
}

#[test]
fn absolute_interval_from_opt_datetime_pair_half_open() {
    assert_eq!(
        AbsoluteInterval::from((None, Some(date(&Utc, 2025, 1, 1)))),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
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
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
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
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
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
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
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
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
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
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
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
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

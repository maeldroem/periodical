use std::cmp::Ordering;
use std::ops::Bound;

use chrono::Utc;

use crate::intervals::meta::BoundInclusivity;
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
    let abs_finite_bound = AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    );

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
    let mut abs_finite_bound = AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    );

    abs_finite_bound.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn absolute_finite_bound_inclusivity() {
    let abs_finite_bound = AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    );

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
        Ok(AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Inclusive)),
    );
}

#[test]
fn absolute_finite_bound_try_from_exclusive_bound() {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Excluded(date(&Utc, 2025, 1, 1))),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(date(&Utc, 2025, 1, 1), BoundInclusivity::Exclusive)),
    );
}

#[test]
fn absolute_finite_bound_try_from_unbounded_bound() {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Unbounded),
        Err(BoundToAbsoluteFiniteBoundConversionErr::IsUnbounded),
    );
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_inf_eq() {
    assert!(!AbsoluteStartBound::InfinitePast.eq(&AbsoluteEndBound::InfiniteFuture));
}

#[test]
fn absolute_start_bound_inf_absolute_end_bound_finite_eq() {
    assert!(
        !AbsoluteStartBound::InfinitePast
            .eq(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))))
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
        !AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .eq(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
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
    assert_eq!(AbsoluteStartBound::InfinitePast.cmp(&AbsoluteStartBound::InfinitePast), Ordering::Equal);
}

#[test]
fn absolute_start_bound_inf_absolute_start_bound_finite_cmp() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast
            .cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
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
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
            .cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
        Ordering::Greater,
    );
}

#[test]
fn absolute_start_bound_different_times_cmp_less() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
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
        AbsoluteStartBound::InfinitePast
            .partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
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
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
            .partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
        Some(Ordering::Greater),
    );
}

#[test]
fn absolute_start_bound_absolute_end_bound_different_times_partial_cmp_less() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .partial_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
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
    assert_eq!(AbsoluteStartBound::from(Bound::Unbounded), AbsoluteStartBound::InfinitePast);
}

#[test]
fn absolute_end_bound_inf_absolute_start_bound_inf_eq() {
    assert!(!AbsoluteEndBound::InfiniteFuture.eq(&AbsoluteStartBound::InfinitePast));
}

#[test]
fn absolute_end_bound_inf_absolute_start_bound_finite_eq() {
    assert!(
        !AbsoluteEndBound::InfiniteFuture
            .eq(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))))
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
        !AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .eq(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
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
    assert_eq!(AbsoluteEndBound::InfiniteFuture.cmp(&AbsoluteEndBound::InfiniteFuture), Ordering::Equal);
}

#[test]
fn absolute_end_bound_inf_absolute_end_bound_finite_cmp() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture
            .cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
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
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
            .cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
        Ordering::Greater,
    );
}

#[test]
fn absolute_end_bound_different_times_cmp_less() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
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
        AbsoluteEndBound::InfiniteFuture
            .partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
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
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
            .partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
        Some(Ordering::Greater),
    );
}

#[test]
fn absolute_end_bound_absolute_start_bound_different_times_partial_cmp_less() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .partial_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
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
    assert_eq!(AbsoluteEndBound::from(Bound::Unbounded), AbsoluteEndBound::InfiniteFuture);
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

    assert_eq!(start, AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    )));
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
    assert_eq!(end, AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    )));
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

    assert_eq!(start, AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 2),
        BoundInclusivity::Inclusive,
    )));
    assert_eq!(end, AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Exclusive,
    )));
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

    assert_eq!(abs_bounds.abs_start(), AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))));
    assert_eq!(abs_bounds.abs_end(), AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))));
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

    assert_eq!(abs_bounds.abs_start(), AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
    assert_eq!(abs_bounds.abs_end(), AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
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

    assert_eq!(abs_bounds.abs_start(), AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
    assert_eq!(abs_bounds.abs_end(), AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
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

    assert_eq!(abs_bounds.abs_start(), AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
    assert_eq!(abs_bounds.abs_end(), AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
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

    assert_eq!(abs_bounds.abs_start(), AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
    assert_eq!(abs_bounds.abs_end(), AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        date(&Utc, 2025, 1, 1),
        BoundInclusivity::Inclusive,
    )));
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

    assert!(!bounds.set_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
}

#[test]
fn absolute_bounds_set_end() {
    let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)));
    let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)));
    let mut bounds = AbsoluteBounds::new(start, end);

    assert!(!bounds.set_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
}

// TODO: AbsoluteBounds cmp tests

// TODO: AbsoluteBounds from RangeBounds

// TODO: AbsoluteBounds try from EmptiableAbsoluteBounds

// TODO: EmptiableAbsoluteBounds etc.

// TODO: Relative version of those tests

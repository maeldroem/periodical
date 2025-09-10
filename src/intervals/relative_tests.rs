use std::cmp::Ordering;
use std::ops::Bound;

use chrono::Duration;

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

use super::relative::*;

#[test]
fn relative_finite_bound_new() {
    let rel_finite_bound = RelativeFiniteBound::new(Duration::hours(1));

    assert_eq!(rel_finite_bound.offset(), Duration::hours(1));
    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn relative_finite_bound_new_with_inclusivity() {
    let rel_finite_bound = RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive);

    assert_eq!(rel_finite_bound.offset(), Duration::hours(1));
    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn relative_finite_bound_set_offset() {
    let mut rel_finite_bound = RelativeFiniteBound::new(Duration::hours(1));

    rel_finite_bound.set_offset(Duration::hours(5));

    assert_eq!(rel_finite_bound.offset(), Duration::hours(5));
}

#[test]
fn relative_finite_bound_set_inclusivity() {
    let mut rel_finite_bound =
        RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive);

    rel_finite_bound.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn relative_finite_bound_inclusivity() {
    let rel_finite_bound = RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive);

    assert_eq!(rel_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn relative_finite_bound_cmp_greater_times() {
    let rel_finite_bound = [
        RelativeFiniteBound::new(Duration::hours(2)),
        RelativeFiniteBound::new(Duration::hours(1)),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Greater);
}

#[test]
fn relative_finite_bound_cmp_equal_times() {
    let rel_finite_bound = [
        RelativeFiniteBound::new(Duration::hours(1)),
        RelativeFiniteBound::new(Duration::hours(1)),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Equal);
}

#[test]
fn relative_finite_bound_cmp_equal_time_different_inclusivities() {
    let rel_finite_bound = [
        RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive),
        RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Inclusive),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Equal);
}

#[test]
fn relative_finite_bound_cmp_less() {
    let rel_finite_bound = [
        RelativeFiniteBound::new(Duration::hours(1)),
        RelativeFiniteBound::new(Duration::hours(2)),
    ];

    assert_eq!(rel_finite_bound[0].cmp(&rel_finite_bound[1]), Ordering::Less);
}

#[test]
fn relative_finite_bound_from_datetime() {
    assert_eq!(
        RelativeFiniteBound::from(Duration::hours(1)),
        RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Inclusive),
    );
}

#[test]
fn relative_finite_bound_from_datetime_inclusivity_pair() {
    assert_eq!(
        RelativeFiniteBound::from((Duration::hours(1), BoundInclusivity::Exclusive)),
        RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn relative_finite_bound_from_datetime_bool_pair() {
    assert_eq!(
        RelativeFiniteBound::from((Duration::hours(1), false)),
        RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive),
    );
}

#[test]
fn relative_finite_bound_try_from_inclusive_bound() {
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Included(Duration::hours(1))),
        Ok(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive
        )),
    );
}

#[test]
fn relative_finite_bound_try_from_exclusive_bound() {
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Excluded(Duration::hours(1))),
        Ok(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive
        )),
    );
}

#[test]
fn relative_finite_bound_try_from_unbounded_bound() {
    assert_eq!(
        RelativeFiniteBound::try_from(Bound::Unbounded),
        Err(RelativeFiniteBoundFromBoundError::IsUnbounded),
    );
}

#[test]
fn relative_start_bound_is_finite() {
    assert!(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).is_finite());
    assert!(!RelativeStartBound::InfinitePast.is_finite());
}

#[test]
fn relative_start_bound_is_infinite_past() {
    assert!(!RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).is_infinite_past());
    assert!(RelativeStartBound::InfinitePast.is_infinite_past());
}

#[test]
fn relative_start_bound_finite() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).finite(),
        Some(RelativeFiniteBound::new(Duration::hours(1))),
    );
    assert_eq!(RelativeStartBound::InfinitePast.finite(), None,);
}

#[test]
fn relative_start_bound_opposite_finite() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).opposite(),
        Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn relative_start_bound_opposite_infinite_past() {
    assert_eq!(RelativeStartBound::InfinitePast.opposite(), None,);
}

#[test]
fn relative_start_bound_inf_relative_end_bound_inf_eq() {
    assert!(!RelativeStartBound::InfinitePast.eq(&RelativeEndBound::InfiniteFuture));
}

#[test]
fn relative_start_bound_inf_relative_end_bound_finite_eq() {
    assert!(
        !RelativeStartBound::InfinitePast.eq(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))))
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_inf_eq() {
    assert!(
        !RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).eq(&RelativeEndBound::InfiniteFuture)
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_different_times_eq() {
    assert!(
        !RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
            .eq(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))),
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_equal_times_exclusive_bounds_eq() {
    assert!(
        !RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_equal_times_exclusive_inclusive_bounds_eq() {
    assert!(
        !RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_equal_times_inclusive_exclusive_bounds_eq() {
    assert!(
        !RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_equal_times_inclusive_bounds_eq() {
    assert!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn relative_start_bound_inf_relative_start_bound_inf_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast.cmp(&RelativeStartBound::InfinitePast),
        Ordering::Equal
    );
}

#[test]
fn relative_start_bound_inf_relative_start_bound_finite_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast.cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            1
        )))),
        Ordering::Less,
    );
}

#[test]
fn relative_start_bound_finite_relative_start_bound_inf_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).cmp(&RelativeStartBound::InfinitePast),
        Ordering::Greater,
    );
}

#[test]
fn relative_start_bound_different_times_cmp_greater() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))).cmp(&RelativeStartBound::Finite(
            RelativeFiniteBound::new(Duration::hours(1))
        )),
        Ordering::Greater,
    );
}

#[test]
fn relative_start_bound_different_times_cmp_less() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).cmp(&RelativeStartBound::Finite(
            RelativeFiniteBound::new(Duration::hours(2))
        )),
        Ordering::Less,
    );
}

#[test]
fn relative_start_bound_same_times_exclusive_bounds_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn relative_start_bound_same_times_exclusive_inclusive_bounds_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Greater,
    );
}

#[test]
fn relative_start_bound_same_times_inclusive_exclusive_bounds_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Less,
    );
}

#[test]
fn relative_start_bound_same_times_inclusive_bounds_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn relative_start_bound_inf_relative_end_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast.partial_cmp(&RelativeEndBound::InfiniteFuture),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_inf_relative_end_bound_finite_partial_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast
            .partial_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
            .partial_cmp(&RelativeEndBound::InfiniteFuture),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_relative_end_bound_different_times_partial_cmp_greater() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))
            .partial_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_start_bound_relative_end_bound_different_times_partial_cmp_less() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
            .partial_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_relative_end_bound_same_times_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_start_bound_relative_end_bound_same_times_exclusive_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_start_bound_relative_end_bound_same_times_inclusive_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_start_bound_relative_end_bound_same_times_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Some(Ordering::Equal),
    );
}

#[test]
fn relative_start_bound_from_relative_finite_bound() {
    assert_eq!(
        RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_start_bound_from_inclusive_bound() {
    assert_eq!(
        RelativeStartBound::from(Bound::Included(Duration::hours(1))),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn relative_start_bound_from_exclusive_bound() {
    assert_eq!(
        RelativeStartBound::from(Bound::Excluded(Duration::hours(1))),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_start_bound_from_unbounded_bound() {
    assert_eq!(
        RelativeStartBound::from(Bound::Unbounded),
        RelativeStartBound::InfinitePast
    );
}

#[test]
fn relative_end_bound_is_finite() {
    assert!(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).is_finite());
    assert!(!RelativeEndBound::InfiniteFuture.is_finite());
}

#[test]
fn relative_end_bound_is_infinite_future() {
    assert!(!RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).is_infinite_future());
    assert!(RelativeEndBound::InfiniteFuture.is_infinite_future());
}

#[test]
fn relative_end_bound_finite() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).finite(),
        Some(RelativeFiniteBound::new(Duration::hours(1))),
    );
    assert_eq!(RelativeEndBound::InfiniteFuture.finite(), None,);
}

#[test]
fn relative_end_bound_opposite_finite() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).opposite(),
        Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn relative_end_bound_opposite_infinite_past() {
    assert_eq!(RelativeEndBound::InfiniteFuture.opposite(), None,);
}

#[test]
fn relative_end_bound_inf_relative_start_bound_inf_eq() {
    assert!(!RelativeEndBound::InfiniteFuture.eq(&RelativeStartBound::InfinitePast));
}

#[test]
fn relative_end_bound_inf_relative_start_bound_finite_eq() {
    assert!(
        !RelativeEndBound::InfiniteFuture.eq(&RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            1
        ))))
    );
}

#[test]
fn relative_end_bound_finite_relative_start_bound_inf_eq() {
    assert!(
        !RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).eq(&RelativeStartBound::InfinitePast)
    );
}

#[test]
fn relative_end_bound_finite_relative_start_bound_finite_different_times_eq() {
    assert!(
        !RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).eq(&RelativeStartBound::Finite(
            RelativeFiniteBound::new(Duration::hours(2))
        )),
    );
}

#[test]
fn relative_end_bound_finite_relative_start_bound_finite_equal_times_exclusive_bounds_eq() {
    assert!(
        !RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn relative_end_bound_finite_relative_start_bound_finite_equal_times_exclusive_inclusive_bounds_eq() {
    assert!(
        !RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .eq(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn relative_end_bound_finite_relative_start_bound_finite_equal_times_inclusive_exclusive_bounds_eq() {
    assert!(
        !RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )))
    );
}

#[test]
fn relative_end_bound_finite_relative_start_bound_finite_equal_times_inclusive_bounds_eq() {
    assert!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .eq(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )))
    );
}

#[test]
fn relative_end_bound_inf_relative_end_bound_inf_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.cmp(&RelativeEndBound::InfiniteFuture),
        Ordering::Equal
    );
}

#[test]
fn relative_end_bound_inf_relative_end_bound_finite_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
        Ordering::Greater,
    );
}

#[test]
fn relative_end_bound_finite_relative_end_bound_inf_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).cmp(&RelativeEndBound::InfiniteFuture),
        Ordering::Less,
    );
}

#[test]
fn relative_end_bound_different_times_cmp_greater() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))
            .cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
        Ordering::Greater,
    );
}

#[test]
fn relative_end_bound_different_times_cmp_less() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
            .cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))),
        Ordering::Less,
    );
}

#[test]
fn relative_end_bound_same_times_exclusive_bounds_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn relative_end_bound_same_times_exclusive_inclusive_bounds_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Less,
    );
}

#[test]
fn relative_end_bound_same_times_inclusive_exclusive_bounds_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Ordering::Greater,
    );
}

#[test]
fn relative_end_bound_same_times_inclusive_bounds_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Ordering::Equal,
    );
}

#[test]
fn relative_end_bound_inf_relative_start_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.partial_cmp(&RelativeStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_inf_relative_start_bound_finite_partial_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.partial_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new(
            Duration::hours(1)
        ))),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_finite_relative_start_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
            .partial_cmp(&RelativeStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_relative_start_bound_different_times_partial_cmp_greater() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2))).partial_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
        ),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_relative_start_bound_different_times_partial_cmp_less() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))).partial_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))
        ),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_end_bound_relative_start_bound_same_times_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_end_bound_relative_start_bound_same_times_exclusive_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
        .partial_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_end_bound_relative_start_bound_same_times_inclusive_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_end_bound_relative_start_bound_same_times_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
        .partial_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
        Some(Ordering::Equal),
    );
}

#[test]
fn relative_end_bound_from_relative_finite_bound() {
    assert_eq!(
        RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_end_bound_from_inclusive_bound() {
    assert_eq!(
        RelativeEndBound::from(Bound::Included(Duration::hours(1))),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn relative_end_bound_from_exclusive_bound() {
    assert_eq!(
        RelativeEndBound::from(Bound::Excluded(Duration::hours(1))),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_end_bound_from_unbounded_bound() {
    assert_eq!(
        RelativeEndBound::from(Bound::Unbounded),
        RelativeEndBound::InfiniteFuture
    );
}

#[test]
fn relative_start_bound_inf_relative_end_bound_inf_swap() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeEndBound::InfiniteFuture;

    swap_relative_bounds(&mut start, &mut end);

    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn relative_start_bound_inf_relative_end_bound_finite_swap() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));

    swap_relative_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
    );
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn relative_start_bound_finite_relative_end_bound_inf_swap() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));
    let mut end = RelativeEndBound::InfiniteFuture;

    swap_relative_bounds(&mut start, &mut end);

    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
    );
}

#[test]
fn relative_start_bound_finite_relative_end_bound_finite_swap() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(2),
        BoundInclusivity::Inclusive,
    ));

    swap_relative_bounds(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(2),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))
    );
}

#[test]
fn relative_bound_is_start() {
    assert!(RelativeBound::Start(RelativeStartBound::InfinitePast).is_start());
    assert!(!RelativeBound::End(RelativeEndBound::InfiniteFuture).is_start());
}

#[test]
fn relative_bound_is_end() {
    assert!(!RelativeBound::Start(RelativeStartBound::InfinitePast).is_end());
    assert!(RelativeBound::End(RelativeEndBound::InfiniteFuture).is_end());
}

#[test]
fn relative_bound_start() {
    assert_eq!(
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))).start(),
        Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
    );
    assert_eq!(
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))).start(),
        None,
    );
}

#[test]
fn relative_bound_end() {
    assert_eq!(
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))).end(),
        None,
    );
    assert_eq!(
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))).end(),
        Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
    );
}

#[test]
fn relative_bound_start_inf_past_opposite() {
    assert_eq!(RelativeBound::Start(RelativeStartBound::InfinitePast).opposite(), None,);
}

#[test]
fn relative_bound_start_finite_opposite() {
    assert_eq!(
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))).opposite(),
        Some(RelativeBound::End(RelativeEndBound::Finite(
            RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive,)
        ))),
    );
}

#[test]
fn relative_bound_end_inf_future_opposite() {
    assert_eq!(RelativeBound::End(RelativeEndBound::InfiniteFuture).opposite(), None,);
}

#[test]
fn relative_bound_end_finite_opposite() {
    assert_eq!(
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))).opposite(),
        Some(RelativeBound::Start(RelativeStartBound::Finite(
            RelativeFiniteBound::new_with_inclusivity(Duration::hours(1), BoundInclusivity::Exclusive,)
        ))),
    );
}

#[test]
fn relative_bound_from_relative_start_bound() {
    assert_eq!(
        RelativeBound::from(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
    );
}

#[test]
fn relative_bound_from_relative_end_bound() {
    assert_eq!(
        RelativeBound::from(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
    );
}

#[test]
fn relative_bounds_unchecked_new() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2)));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));

    let rel_bounds = RelativeBounds::unchecked_new(start, end);

    assert_eq!(rel_bounds.rel_start(), start);
    assert_eq!(rel_bounds.rel_end(), end);
}

#[test]
fn relative_bounds_new_should_swap() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2)));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));

    let rel_bounds = RelativeBounds::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))
    );
}

#[test]
fn relative_bounds_new_from_same_times_exclusive_bounds() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));

    let rel_bounds = RelativeBounds::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn relative_bounds_new_from_same_times_inclusive_exclusive_bounds() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Inclusive,
    ));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));

    let rel_bounds = RelativeBounds::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn relative_bounds_new_from_same_times_exclusive_inclusive_bounds() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Inclusive,
    ));

    let rel_bounds = RelativeBounds::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn relative_bounds_new_from_same_times_inclusive_bounds() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Inclusive,
    ));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Inclusive,
    ));

    let rel_bounds = RelativeBounds::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))
    );
}

#[test]
fn relative_bounds_unchecked_set_start() {
    let mut bounds = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
    );

    let new_start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(3)));

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.rel_start(), new_start);
}

#[test]
fn relative_bounds_unchecked_set_end() {
    let mut bounds = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(3))),
    );

    let new_end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.rel_end(), new_end);
}

#[test]
fn relative_bounds_set_start() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)));
    let mut bounds = RelativeBounds::new(start, end);

    assert!(!bounds.set_start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(3)))));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn relative_bounds_set_end() {
    let start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2)));
    let end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(3)));
    let mut bounds = RelativeBounds::new(start, end);

    assert!(!bounds.set_end(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn relative_bounds_unbounded_relative_bounds_unbounded_cmp() {
    let a = RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn relative_bounds_unbounded_relative_bounds_half_bounded_to_future_cmp() {
    let a = RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn relative_bounds_unbounded_relative_bounds_half_bounded_to_past_cmp() {
    let a = RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBounds::new(
        RelativeStartBound::InfinitePast,
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn relative_bounds_unbounded_relative_bounds_bounded_cmp() {
    let a = RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_unbounded_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_future_after_first_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_future_before_first_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_future_same_time_exclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_future_same_time_exclusive_inclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_future_same_time_inclusive_exclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_future_same_time_inclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_past_before_first_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::InfinitePast,
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_past_after_first_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::InfinitePast,
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_past_same_time_exclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::InfinitePast,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_past_same_time_exclusive_inclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::InfinitePast,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_past_same_time_inclusive_exclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::InfinitePast,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_to_past_same_time_inclusive_bounds_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::InfinitePast,
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        )),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_bounded_starts_before_first_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(3))),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
}

#[test]
fn relative_bounds_half_bounded_to_future_relative_bounds_bounded_starts_after_first_cmp() {
    let a = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        RelativeEndBound::InfiniteFuture,
    );
    let b = RelativeBounds::new(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(3))),
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(4))),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
}

#[test]
fn relative_bounds_from_bound_pair() {
    assert_eq!(
        RelativeBounds::from((Bound::Excluded(Duration::hours(1)), Bound::Unbounded)),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        ),
    );
}

#[test]
fn relative_bounds_try_from_emptiable_relative_bounds_correct_variant() {
    assert_eq!(
        RelativeBounds::try_from(EmptiableRelativeBounds::Bound(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        ))),
        Ok(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn relative_bounds_try_from_emptiable_relative_bounds_wrong_variant() {
    assert_eq!(
        RelativeBounds::try_from(EmptiableRelativeBounds::Empty),
        Err(RelativeBoundsFromEmptiableRelativeBoundsError::EmptyVariant),
    );
}

#[test]
fn emptiable_relative_bounds_from_relative_bounds() {
    assert_eq!(
        EmptiableRelativeBounds::from(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
        EmptiableRelativeBounds::Bound(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn bounded_relative_interval_new() {
    let interval = BoundedRelativeInterval::new(Duration::hours(1), Duration::hours(2));

    assert_eq!(interval.offset(), Duration::hours(1));
    assert_eq!(interval.length(), Duration::hours(2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_relative_interval_new_with_inclusivity() {
    let interval = BoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
        Duration::hours(2),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.offset(), Duration::hours(1));
    assert_eq!(interval.length(), Duration::hours(2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_relative_set_offset() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
        Duration::hours(2),
        BoundInclusivity::Inclusive,
    );

    interval.set_offset(Duration::hours(3));

    assert_eq!(interval.offset(), Duration::hours(3));
    assert_eq!(interval.length(), Duration::hours(2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_relative_set_length() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(2),
        BoundInclusivity::Exclusive,
        Duration::hours(3),
        BoundInclusivity::Inclusive,
    );

    interval.set_length(Duration::hours(1));

    assert_eq!(interval.offset(), Duration::hours(2));
    assert_eq!(interval.length(), Duration::hours(1));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_relative_set_from_inclusivity() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
        Duration::hours(2),
        BoundInclusivity::Inclusive,
    );

    interval.set_from_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(interval.offset(), Duration::hours(1));
    assert_eq!(interval.length(), Duration::hours(2));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_relative_set_to_inclusivity() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(2),
        BoundInclusivity::Exclusive,
        Duration::hours(3),
        BoundInclusivity::Inclusive,
    );

    interval.set_to_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.offset(), Duration::hours(2));
    assert_eq!(interval.length(), Duration::hours(3));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_relative_interval_from_datetime_pair() {
    assert_eq!(
        BoundedRelativeInterval::from((Duration::hours(2), Duration::hours(1))),
        BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(2),
            BoundInclusivity::Inclusive,
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ),
    );
}

#[test]
fn bounded_relative_interval_from_pair_of_datetime_inclusivity_pairs() {
    assert_eq!(
        BoundedRelativeInterval::from((
            (Duration::hours(2), BoundInclusivity::Exclusive),
            (Duration::hours(1), BoundInclusivity::Inclusive),
        )),
        BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(2),
            BoundInclusivity::Exclusive,
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ),
    );
}

#[test]
fn bounded_relative_interval_from_pair_of_datetime_bool_pairs() {
    assert_eq!(
        BoundedRelativeInterval::from(((Duration::hours(2), false), (Duration::hours(1), true),)),
        BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(2),
            BoundInclusivity::Exclusive,
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ),
    );
}

#[test]
fn bounded_relative_interval_from_range() {
    assert_eq!(
        BoundedRelativeInterval::from(Duration::hours(1)..Duration::hours(2)),
        BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
            Duration::hours(2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn bounded_relative_interval_from_range_inclusive() {
    assert_eq!(
        BoundedRelativeInterval::from(Duration::hours(1)..=Duration::hours(2)),
        BoundedRelativeInterval::new(Duration::hours(1), Duration::hours(2)),
    );
}

#[test]
fn bounded_relative_interval_try_from_relative_bounds_correct() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(2),
                BoundInclusivity::Inclusive,
            )),
        )),
        Ok(BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            Duration::hours(2),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn bounded_relative_interval_try_from_relative_bounds_wrong() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        )),
        Err(BoundedRelativeIntervalFromRelativeBoundsError::NotBoundedInterval),
    );
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            RelativeEndBound::InfiniteFuture,
        )),
        Err(BoundedRelativeIntervalFromRelativeBoundsError::NotBoundedInterval),
    );
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
        Err(BoundedRelativeIntervalFromRelativeBoundsError::NotBoundedInterval),
    );
}

#[test]
fn bounded_relative_interval_try_from_relative_interval_correct() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeInterval::Bounded(BoundedRelativeInterval::new(
            Duration::hours(1),
            Duration::hours(2),
        ))),
        Ok(BoundedRelativeInterval::new(Duration::hours(1), Duration::hours(2),)),
    );
}

#[test]
fn bounded_relative_interval_try_from_relative_interval_wrong() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeInterval::Empty(EmptyInterval)),
        Err(BoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeInterval::Unbounded(UnboundedInterval)),
        Err(BoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            Duration::hours(1),
            OpeningDirection::ToFuture,
        ))),
        Err(BoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
}

#[test]
fn half_bounded_relative_interval_new() {
    let interval = HalfBoundedRelativeInterval::new(Duration::hours(1), OpeningDirection::ToFuture);

    assert_eq!(interval.offset(), Duration::hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_time_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn half_bounded_relative_interval_new_with_inclusivity() {
    let interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.offset(), Duration::hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    assert_eq!(interval.reference_time_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn half_bounded_relative_interval_set_reference_time() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_offset(Duration::hours(2));

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn half_bounded_relative_interval_set_reference_time_inclusivity() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_time_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn half_bounded_relative_interval_set_opening_direction() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );
}

#[test]
fn half_bounded_relative_interval_from_datetime_opening_direction_pair() {
    assert_eq!(
        HalfBoundedRelativeInterval::from((Duration::hours(1), OpeningDirection::ToFuture)),
        HalfBoundedRelativeInterval::new(Duration::hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn half_bounded_relative_interval_from_datetime_bool_pair() {
    assert_eq!(
        HalfBoundedRelativeInterval::from((Duration::hours(1), false)),
        HalfBoundedRelativeInterval::new(Duration::hours(1), OpeningDirection::ToPast),
    );
}

#[test]
fn half_bounded_relative_interval_from_pair_of_datetime_bound_inclusivity_pair_and_opening_direction() {
    assert_eq!(
        HalfBoundedRelativeInterval::from((
            (Duration::hours(1), BoundInclusivity::Exclusive),
            OpeningDirection::ToPast
        )),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_relative_interval_from_pair_of_datetime_bool_pair_and_opening_direction() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(((Duration::hours(1), false), OpeningDirection::ToPast)),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_relative_interval_from_pair_of_datetime_bool_pair_and_bool() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(((Duration::hours(1), false), false)),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_relative_interval_from_range_from() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(Duration::hours(1)..),
        HalfBoundedRelativeInterval::new(Duration::hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn half_bounded_relative_interval_from_range_to() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(..Duration::hours(1)),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn half_bounded_relative_interval_from_range_to_inclusive() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(..=Duration::hours(1)),
        HalfBoundedRelativeInterval::new(Duration::hours(1), OpeningDirection::ToPast),
    );
}

#[test]
fn half_bounded_relative_interval_try_from_relative_bounds_correct() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        )),
        Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            )),
        )),
        Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn half_bounded_relative_interval_try_from_relative_bounds_wrong() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
        Err(HalfBoundedRelativeIntervalFromRelativeBoundsError::NotHalfBoundedInterval),
    );
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        )),
        Err(HalfBoundedRelativeIntervalFromRelativeBoundsError::NotHalfBoundedInterval),
    );
}

#[test]
fn half_bounded_relative_interval_try_from_relative_interval_correct() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeInterval::HalfBounded(
            HalfBoundedRelativeInterval::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
        Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn half_bounded_relative_interval_try_from_relative_interval_wrong() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeInterval::Empty(EmptyInterval)),
        Err(HalfBoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeInterval::Unbounded(UnboundedInterval)),
        Err(HalfBoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeInterval::Bounded(BoundedRelativeInterval::new(
            Duration::hours(1),
            Duration::hours(2),
        ))),
        Err(HalfBoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
}

#[test]
fn relative_interval_from_relative_bounds() {
    assert_eq!(
        RelativeInterval::from(RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        )),
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn relative_interval_from_emptiable_relative_bounds() {
    assert_eq!(
        RelativeInterval::from(EmptiableRelativeBounds::Bound(RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        ))),
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn relative_interval_from_opt_datetime_pair_unbounded() {
    assert_eq!(
        <RelativeInterval as From<(Option<Duration>, Option<Duration>)>>::from((None, None)),
        RelativeInterval::Unbounded(UnboundedInterval),
    );
}

#[test]
fn relative_interval_from_opt_datetime_pair_half_bounded() {
    assert_eq!(
        RelativeInterval::from((None, Some(Duration::hours(1)))),
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            Duration::hours(1),
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn relative_interval_from_opt_datetime_bound_inclusivity_pairs() {
    assert_eq!(
        RelativeInterval::from((
            Some((Duration::hours(1), BoundInclusivity::Exclusive)),
            Some((Duration::hours(2), BoundInclusivity::Exclusive)),
        )),
        RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            Duration::hours(2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_interval_from_opt_datetime_bool_pairs() {
    assert_eq!(
        RelativeInterval::from((Some((Duration::hours(1), true)), Some((Duration::hours(2), false)),)),
        RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
            Duration::hours(2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_empty() {
    assert_eq!(
        <RelativeInterval as From<(bool, Option<Duration>, Option<Duration>)>>::from((true, None, None,)),
        RelativeInterval::Empty(EmptyInterval),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime() {
    assert_eq!(
        RelativeInterval::from((false, Some(Duration::hours(1)), Some(Duration::hours(2)),)),
        RelativeInterval::Bounded(BoundedRelativeInterval::new(Duration::hours(1), Duration::hours(2))),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_bound_inclusivity_empty() {
    assert_eq!(
        <RelativeInterval as From<(
            bool,
            Option<(Duration, BoundInclusivity)>,
            Option<(Duration, BoundInclusivity)>
        )>>::from((true, None, None,)),
        RelativeInterval::Empty(EmptyInterval),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_bound_inclusivity() {
    assert_eq!(
        RelativeInterval::from((
            false,
            Some((Duration::hours(1), BoundInclusivity::Exclusive)),
            Some((Duration::hours(2), BoundInclusivity::Exclusive)),
        )),
        RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            Duration::hours(2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_bool_empty() {
    assert_eq!(
        <RelativeInterval as From<(bool, Option<(Duration, bool)>, Option<(Duration, bool)>)>>::from((
            true, None, None,
        )),
        RelativeInterval::Empty(EmptyInterval),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_bool() {
    assert_eq!(
        RelativeInterval::from((
            false,
            Some((Duration::hours(1), false)),
            Some((Duration::hours(2), false)),
        )),
        RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            Duration::hours(2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_interval_from_bound_pair() {
    assert_eq!(
        RelativeInterval::from((Bound::Unbounded, Bound::Excluded(Duration::hours(1)))),
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn check_relative_bounds_for_interval_creation_inf_past_inf_future() {
    assert_eq!(
        check_relative_bounds_for_interval_creation(
            &RelativeStartBound::InfinitePast,
            &RelativeEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bounds_for_interval_creation_inf_past_finite() {
    assert_eq!(
        check_relative_bounds_for_interval_creation(
            &RelativeStartBound::InfinitePast,
            &RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bounds_for_interval_creation_finite_inf_future() {
    assert_eq!(
        check_relative_bounds_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            &RelativeEndBound::InfiniteFuture,
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bounds_for_interval_creation_finite_finite_different_offsets_correct_order() {
    assert_eq!(
        check_relative_bounds_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bounds_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    assert_eq!(
        check_relative_bounds_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        ),
        Err(RelativeBoundsCheckForIntervalCreationError::StartPastEnd),
    );
}

#[test]
fn check_relative_bounds_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    assert_eq!(
        check_relative_bounds_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        ),
        Ok(()),
    );
}

#[test]
fn check_relative_bounds_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    assert_eq!(
        check_relative_bounds_for_interval_creation(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            &RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            )),
        ),
        Err(RelativeBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
    );
}

#[test]
fn prepare_relative_bounds_for_interval_creation_inf_past_inf_future() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeEndBound::InfiniteFuture;

    prepare_relative_bounds_for_interval_creation(&mut start, &mut end);

    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn prepare_relative_bounds_for_interval_creation_inf_past_finite() {
    let mut start = RelativeStartBound::InfinitePast;
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));

    prepare_relative_bounds_for_interval_creation(&mut start, &mut end);

    assert_eq!(start, RelativeStartBound::InfinitePast);
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
}

#[test]
fn prepare_relative_bounds_for_interval_creation_finite_inf_future() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));
    let mut end = RelativeEndBound::InfiniteFuture;

    prepare_relative_bounds_for_interval_creation(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
    assert_eq!(end, RelativeEndBound::InfiniteFuture);
}

#[test]
fn prepare_relative_bounds_for_interval_creation_finite_finite_different_offsets_correct_order() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)));

    prepare_relative_bounds_for_interval_creation(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))
    );
}

#[test]
fn prepare_relative_bounds_for_interval_creation_finite_finite_different_offsets_wrong_order() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));

    prepare_relative_bounds_for_interval_creation(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
    assert_eq!(
        end,
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(2)))
    );
}

#[test]
fn prepare_relative_bounds_for_interval_creation_finite_finite_same_offset_inclusive_inclusive() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));

    prepare_relative_bounds_for_interval_creation(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
    assert_eq!(
        end,
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
}

#[test]
fn prepare_relative_bounds_for_interval_creation_finite_finite_same_offset_inclusive_exclusive() {
    let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)));
    let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        Duration::hours(1),
        BoundInclusivity::Exclusive,
    ));

    prepare_relative_bounds_for_interval_creation(&mut start, &mut end);

    assert_eq!(
        start,
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
    assert_eq!(
        end,
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))
    );
}

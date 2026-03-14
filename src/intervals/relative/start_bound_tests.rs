use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBound};

use super::start_bound::*;

#[test]
fn is_finite() {
    assert!(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound().is_finite());
    assert!(!RelativeStartBound::InfinitePast.is_finite());
}

#[test]
fn is_infinite_past() {
    assert!(!RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound().is_infinite_past());
    assert!(RelativeStartBound::InfinitePast.is_infinite_past());
}

#[test]
fn finite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound().finite(),
        Some(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
    );
    assert_eq!(RelativeStartBound::InfinitePast.finite(), None);
}

#[test]
fn opposite_finite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound().opposite(),
        Some(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_end_bound()),
    );
}

#[test]
fn opposite_infinite_past() {
    assert_eq!(RelativeStartBound::InfinitePast.opposite(), None);
}

#[test]
fn inf_relative_end_bound_inf_eq() {
    assert_ne!(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
}

#[test]
fn inf_relative_end_bound_finite_eq() {
    assert_ne!(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
    );
}

#[test]
fn finite_relative_end_bound_inf_eq() {
    assert_ne!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
}

#[test]
fn finite_relative_end_bound_finite_different_times_eq() {
    assert_ne!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );
}

#[test]
fn finite_relative_end_bound_finite_equal_times_exclusive_bounds_eq() {
    assert_ne!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
    );
}

#[test]
fn finite_relative_end_bound_finite_equal_times_exclusive_inclusive_bounds_eq() {
    assert_ne!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
    );
}

#[test]
fn finite_relative_end_bound_finite_equal_times_inclusive_exclusive_bounds_eq() {
    assert_ne!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
    );
}

#[test]
fn finite_relative_end_bound_finite_equal_times_inclusive_bounds_eq() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
    );
}

#[test]
fn inf_inf_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast.cmp(&RelativeStartBound::InfinitePast),
        Ordering::Equal
    );
}

#[test]
fn inf_finite_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast
            .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
        Ordering::Less,
    );
}

#[test]
fn finite_inf_cmp() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .cmp(&RelativeStartBound::InfinitePast),
        Ordering::Greater,
    );
}

#[test]
fn different_times_cmp_greater() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(2))
            .to_start_bound()
            .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
        Ordering::Greater,
    );
}

#[test]
fn different_times_cmp_less() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound()),
        Ordering::Less,
    );
}

#[test]
fn same_times_exclusive_bounds_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
            .to_start_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_start_bound()),
        Ordering::Equal,
    );
}

#[test]
fn same_times_exclusive_inclusive_bounds_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
            .to_start_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_start_bound()),
        Ordering::Greater,
    );
}

#[test]
fn same_times_inclusive_exclusive_bounds_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_start_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_start_bound()),
        Ordering::Less,
    );
}

#[test]
fn same_times_inclusive_bounds_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_start_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_start_bound()),
        Ordering::Equal,
    );
}

#[test]
fn inf_relative_end_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast.partial_cmp(&RelativeEndBound::InfiniteFuture),
        Some(Ordering::Less),
    );
}

#[test]
fn inf_relative_end_bound_finite_partial_cmp() {
    assert_eq!(
        RelativeStartBound::InfinitePast
            .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
        Some(Ordering::Less),
    );
}

#[test]
fn finite_relative_end_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .partial_cmp(&RelativeEndBound::InfiniteFuture),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_end_bound_different_times_partial_cmp_greater() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(2))
            .to_start_bound()
            .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_different_times_partial_cmp_less() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_end_bound_same_times_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
            .to_start_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_end_bound()),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_same_times_exclusive_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
            .to_start_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_end_bound()),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_same_times_inclusive_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_start_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_end_bound()),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_end_bound_same_times_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_start_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_end_bound()),
        Some(Ordering::Equal),
    );
}

#[test]
fn from_relative_finite_bound() {
    assert_eq!(
        RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn from_inclusive_bound() {
    assert_eq!(
        RelativeStartBound::from(Bound::Included(SignedDuration::from_hours(1))),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_start_bound(),
    );
}

#[test]
fn from_exclusive_bound() {
    assert_eq!(
        RelativeStartBound::from(Bound::Excluded(SignedDuration::from_hours(1))),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_start_bound(),
    );
}

#[test]
fn from_unbounded_bound() {
    assert_eq!(
        RelativeStartBound::from(Bound::Unbounded),
        RelativeStartBound::InfinitePast
    );
}

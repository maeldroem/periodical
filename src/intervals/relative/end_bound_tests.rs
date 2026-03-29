use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBound, RelativeFiniteBound, RelativeStartBound};

use super::end_bound::*;

#[test]
fn to_bound() {
    let end_bound = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();
    
    assert_eq!(
        end_bound.to_bound(),
        RelativeBound::End(end_bound),
    );
}

#[test]
fn is_finite() {
    assert!(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound().is_finite());
    assert!(!RelativeEndBound::InfiniteFuture.is_finite());
}

#[test]
fn is_infinite_future() {
    assert!(!RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound().is_infinite_future());
    assert!(RelativeEndBound::InfiniteFuture.is_infinite_future());
}

#[test]
fn finite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound().finite(),
        Some(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
    );
    assert_eq!(RelativeEndBound::InfiniteFuture.finite(), None,);
}

#[test]
fn opposite_finite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound().opposite(),
        Some(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_start_bound()),
    );
}

#[test]
fn opposite_infinite_past() {
    assert_eq!(RelativeEndBound::InfiniteFuture.opposite(), None);
}

#[test]
fn inf_relative_start_bound_inf_eq() {
    assert_ne!(RelativeEndBound::InfiniteFuture, RelativeStartBound::InfinitePast);
}

#[test]
fn inf_relative_start_bound_finite_eq() {
    assert_ne!(
        RelativeEndBound::InfiniteFuture,
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
    );
}

#[test]
fn finite_relative_start_bound_inf_eq() {
    assert_ne!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
        RelativeStartBound::InfinitePast,
    );
}

#[test]
fn finite_relative_start_bound_finite_different_times_eq() {
    assert_ne!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
    );
}

#[test]
fn finite_relative_start_bound_finite_equal_times_exclusive_bounds_eq() {
    assert_ne!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_start_bound(),
    );
}

#[test]
fn finite_relative_start_bound_finite_equal_times_exclusive_inclusive_bounds_eq() {
    assert_ne!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_start_bound(),
    );
}

#[test]
fn finite_relative_start_bound_finite_equal_times_inclusive_exclusive_bounds_eq() {
    assert_ne!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_start_bound(),
    );
}

#[test]
fn finite_relative_start_bound_finite_equal_times_inclusive_bounds_eq() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_start_bound(),
    );
}

#[test]
fn inf_inf_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.cmp(&RelativeEndBound::InfiniteFuture),
        Ordering::Equal
    );
}

#[test]
fn inf_finite_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
        Ordering::Greater,
    );
}

#[test]
fn finite_inf_cmp() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .cmp(&RelativeEndBound::InfiniteFuture),
        Ordering::Less,
    );
}

#[test]
fn different_times_cmp_greater() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
            .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
        Ordering::Greater,
    );
}

#[test]
fn different_times_cmp_less() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
            .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()),
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
            .to_end_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_end_bound()),
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
            .to_end_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_end_bound()),
        Ordering::Less,
    );
}

#[test]
fn same_times_inclusive_exclusive_bounds_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_end_bound()),
        Ordering::Greater,
    );
}

#[test]
fn same_times_inclusive_bounds_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_end_bound()),
        Ordering::Equal,
    );
}

#[test]
fn inf_relative_start_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.partial_cmp(&RelativeStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
}

#[test]
fn inf_relative_start_bound_finite_partial_cmp() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture
            .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
        Some(Ordering::Greater),
    );
}

#[test]
fn finite_relative_start_bound_inf_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
            .partial_cmp(&RelativeStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_start_bound_different_times_partial_cmp_greater() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(2))
            .to_end_bound()
            .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
        Some(Ordering::Greater),
    );
}

#[test]
fn relative_start_bound_different_times_partial_cmp_less() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound()),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_same_times_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
            .to_end_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_start_bound()),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_same_times_exclusive_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
            .to_end_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_start_bound()),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_same_times_inclusive_exclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_start_bound()),
        Some(Ordering::Less),
    );
}

#[test]
fn relative_start_bound_same_times_inclusive_bounds_partial_cmp() {
    assert_eq!(
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .partial_cmp(&RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ).to_start_bound()),
        Some(Ordering::Equal),
    );
}

#[test]
fn from_relative_finite_bound() {
    assert_eq!(
        RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn from_inclusive_bound() {
    assert_eq!(
        RelativeEndBound::from(Bound::Included(SignedDuration::from_hours(1))),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
    );
}

#[test]
fn from_exclusive_bound() {
    assert_eq!(
        RelativeEndBound::from(Bound::Excluded(SignedDuration::from_hours(1))),
        RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
    );
}

#[test]
fn from_unbounded_bound() {
    assert_eq!(
        RelativeEndBound::from(Bound::Unbounded),
        RelativeEndBound::InfiniteFuture
    );
}

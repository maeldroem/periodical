use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::end_bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBound, RelativeFiniteBoundPosition, RelativeStartBound};

#[test]
fn to_bound() {
    let end_bound = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound();

    assert_eq!(end_bound.to_bound(), RelativeBound::End(end_bound),);
}

#[test]
fn is_finite() {
    assert!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .is_finite()
    );
    assert!(!RelativeEndBound::InfiniteFuture.is_finite());
}

#[test]
fn is_infinite_future() {
    assert!(
        !RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .is_infinite_future()
    );
    assert!(RelativeEndBound::InfiniteFuture.is_infinite_future());
}

#[test]
fn finite() {
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .finite(),
        Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_finite_end_bound()),
    );
    assert_eq!(RelativeEndBound::InfiniteFuture.finite(), None,);
}

#[test]
fn opposite() {
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .opposite(),
        Some(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
        ),
    );
    assert_eq!(RelativeEndBound::InfiniteFuture.opposite(), None);
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            RelativeEndBound::InfiniteFuture.cmp(&RelativeEndBound::InfiniteFuture),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() {
        assert_eq!(
            RelativeEndBound::InfiniteFuture
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn finite_inf() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                .to_end_bound()
                .cmp(&RelativeEndBound::InfiniteFuture),
            Ordering::Less,
        );
    }

    #[test]
    fn different_times_greater() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2))
                .to_end_bound()
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_less() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                .to_end_bound()
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_exclusive_bounds() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
            Ordering::Equal,
        );
    }

    #[test]
    fn same_times_exclusive_inclusive_bounds() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_inclusive_exclusive_bounds() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
            Ordering::Greater,
        );
    }

    #[test]
    fn same_times_inclusive_bounds() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Ordering::Equal,
        );
    }
}

#[test]
fn from_relative_finite_bound_position() {
    assert_eq!(
        RelativeEndBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeEndBound::Finite(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )
            .to_finite_end_bound()
        ),
    );
}

#[test]
fn from_opt_signed_duration() {
    assert_eq!(
        RelativeEndBound::from(Some(SignedDuration::from_hours(8))),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_end_bound()
    );
    assert_eq!(
        RelativeEndBound::from(None::<SignedDuration>),
        RelativeEndBound::InfiniteFuture
    );
}

#[test]
fn from_opt_signed_duration_inclusivity() {
    assert_eq!(
        RelativeEndBound::from(Some((SignedDuration::from_hours(8), BoundInclusivity::Exclusive))),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound()
    );
    assert_eq!(
        RelativeEndBound::from(None::<(SignedDuration, BoundInclusivity)>),
        RelativeEndBound::InfiniteFuture
    );
}

#[test]
fn from_bound() {
    assert_eq!(
        RelativeEndBound::from(Bound::Included(SignedDuration::from_hours(1))),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
    assert_eq!(
        RelativeEndBound::from(Bound::Excluded(SignedDuration::from_hours(1))),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
            .to_end_bound(),
    );
    assert_eq!(
        RelativeEndBound::from(Bound::Unbounded),
        RelativeEndBound::InfiniteFuture
    );
}

#[test]
fn try_from_rel_bound() {
    assert_eq!(
        RelativeEndBound::try_from(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_end_bound()
                .to_bound()
        ),
        Ok(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_end_bound()
        )
    );
    assert_eq!(
        RelativeEndBound::try_from(RelativeEndBound::InfiniteFuture.to_bound()),
        Ok(RelativeEndBound::InfiniteFuture)
    );

    assert_eq!(
        RelativeEndBound::try_from(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound()
                .to_bound()
        ),
        Err(RelativeEndBoundTryFromRelativeBoundError)
    );
    assert_eq!(
        RelativeEndBound::try_from(RelativeStartBound::InfinitePast.to_bound()),
        Err(RelativeEndBoundTryFromRelativeBoundError)
    );
}

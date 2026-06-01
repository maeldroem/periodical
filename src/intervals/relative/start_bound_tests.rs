use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::start_bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBound, RelativeEndBound, RelativeFiniteBoundPosition};

#[test]
fn to_bound() {
    let start_bound = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound();

    assert_eq!(start_bound.to_bound(), RelativeBound::Start(start_bound),);
}

#[test]
fn is_finite() {
    assert!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .is_finite()
    );
    assert!(!RelativeStartBound::InfinitePast.is_finite());
}

#[test]
fn is_infinite_past() {
    assert!(
        !RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .is_infinite_past()
    );
    assert!(RelativeStartBound::InfinitePast.is_infinite_past());
}

#[test]
fn finite() {
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .finite(),
        Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_finite_start_bound()),
    );
    assert_eq!(RelativeStartBound::InfinitePast.finite(), None);
}

#[test]
fn opposite() {
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .opposite(),
        Some(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
        ),
    );
    assert_eq!(RelativeStartBound::InfinitePast.opposite(), None);
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            RelativeStartBound::InfinitePast.cmp(&RelativeStartBound::InfinitePast),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() {
        assert_eq!(
            RelativeStartBound::InfinitePast
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn finite_inf() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .cmp(&RelativeStartBound::InfinitePast),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_greater() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2))
                .to_start_bound()
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_less() {
        assert_eq!(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .cmp(&RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound()),
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
            .to_start_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
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
            .to_start_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Ordering::Greater,
        );
    }

    #[test]
    fn same_times_inclusive_exclusive_bounds() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_inclusive_bounds() {
        assert_eq!(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound()
            .cmp(
                &RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Ordering::Equal,
        );
    }
}

#[test]
fn from_relative_finite_bound_position() {
    assert_eq!(
        RelativeStartBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelativeStartBound::Finite(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )
            .to_finite_start_bound()
        ),
    );
}

#[test]
fn from_opt_signed_duration() {
    assert_eq!(
        RelativeStartBound::from(Some(SignedDuration::from_hours(8))),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_start_bound()
    );
    assert_eq!(
        RelativeStartBound::from(None::<SignedDuration>),
        RelativeStartBound::InfinitePast
    );
}

#[test]
fn from_opt_signed_duration_inclusivity() {
    assert_eq!(
        RelativeStartBound::from(Some((SignedDuration::from_hours(8), BoundInclusivity::Exclusive))),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_start_bound()
    );
    assert_eq!(
        RelativeStartBound::from(None::<(SignedDuration, BoundInclusivity)>),
        RelativeStartBound::InfinitePast
    );
}

#[test]
fn from_bound() {
    assert_eq!(
        RelativeStartBound::from(Bound::Included(SignedDuration::from_hours(1))),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        RelativeStartBound::from(Bound::Excluded(SignedDuration::from_hours(1))),
        RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        RelativeStartBound::from(Bound::Unbounded),
        RelativeStartBound::InfinitePast
    );
}

#[test]
fn try_from_rel_bound() {
    assert_eq!(
        RelativeStartBound::try_from(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound()
                .to_bound()
        ),
        Ok(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound()
        )
    );
    assert_eq!(
        RelativeStartBound::try_from(RelativeStartBound::InfinitePast.to_bound()),
        Ok(RelativeStartBound::InfinitePast)
    );

    assert_eq!(
        RelativeStartBound::try_from(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_end_bound()
                .to_bound()
        ),
        Err(RelativeStartBoundTryFromRelativeBoundError)
    );
    assert_eq!(
        RelativeStartBound::try_from(RelativeEndBound::InfiniteFuture.to_bound()),
        Err(RelativeStartBoundTryFromRelativeBoundError)
    );
}

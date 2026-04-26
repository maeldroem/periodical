use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::start_bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBound, RelativeEndBound, RelativeFiniteBound};

#[test]
fn to_bound() {
    let start_bound = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();

    assert_eq!(start_bound.to_bound(), RelativeBound::Start(start_bound),);
}

#[test]
fn is_finite() {
    assert!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .is_finite()
    );
    assert!(!RelativeStartBound::InfinitePast.is_finite());
}

#[test]
fn is_infinite_past() {
    assert!(
        !RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .is_infinite_past()
    );
    assert!(RelativeStartBound::InfinitePast.is_infinite_past());
}

#[test]
fn finite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .finite(),
        Some(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
    );
    assert_eq!(RelativeStartBound::InfinitePast.finite(), None);
}

#[test]
fn opposite_finite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .opposite(),
        Some(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound()
        ),
    );
}

#[test]
fn opposite_infinite_past() {
    assert_eq!(RelativeStartBound::InfinitePast.opposite(), None);
}

mod eq {
    use super::*;

    #[test]
    fn inf_relative_end_bound_inf() {
        assert_ne!(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
    }

    #[test]
    fn inf_relative_end_bound_finite() {
        assert_ne!(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
        );
    }

    #[test]
    fn finite_relative_end_bound_inf() {
        assert_ne!(
            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
    }

    #[test]
    fn finite_relative_end_bound_finite_different_times() {
        assert_ne!(
            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
    }

    #[test]
    fn finite_relative_end_bound_finite_equal_times_exclusive_bounds() {
        assert_ne!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound(),
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound(),
        );
    }

    #[test]
    fn finite_relative_end_bound_finite_equal_times_exclusive_inclusive_bounds() {
        assert_ne!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound(),
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_end_bound(),
        );
    }

    #[test]
    fn finite_relative_end_bound_finite_equal_times_inclusive_exclusive_bounds() {
        assert_ne!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound(),
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound(),
        );
    }

    #[test]
    fn finite_relative_end_bound_finite_equal_times_inclusive_bounds() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound(),
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_end_bound(),
        );
    }
}

mod cmp {
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
                .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn finite_inf() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .cmp(&RelativeStartBound::InfinitePast),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_greater() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(2))
                .to_start_bound()
                .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_less() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_exclusive_bounds() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
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
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
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
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
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
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Inclusive,
                    )
                    .to_start_bound()
                ),
            Ordering::Equal,
        );
    }
}

mod partial_cmp_rel_end {
    use super::*;

    #[test]
    fn inf_relative_end_bound_inf() {
        assert_eq!(
            RelativeStartBound::InfinitePast.partial_cmp(&RelativeEndBound::InfiniteFuture),
            Some(Ordering::Less),
        );
    }

    #[test]
    fn inf_relative_end_bound_finite() {
        assert_eq!(
            RelativeStartBound::InfinitePast
                .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
            Some(Ordering::Less),
        );
    }

    #[test]
    fn finite_relative_end_bound_inf() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .partial_cmp(&RelativeEndBound::InfiniteFuture),
            Some(Ordering::Less),
        );
    }

    #[test]
    fn relative_end_bound_different_times_greater() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(2))
                .to_start_bound()
                .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
            Some(Ordering::Greater),
        );
    }

    #[test]
    fn relative_end_bound_different_times_less() {
        assert_eq!(
            RelativeFiniteBound::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .partial_cmp(&RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()),
            Some(Ordering::Less),
        );
    }

    #[test]
    fn relative_end_bound_same_times_exclusive_bounds() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .partial_cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
            Some(Ordering::Greater),
        );
    }

    #[test]
    fn relative_end_bound_same_times_exclusive_inclusive_bounds() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .partial_cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Inclusive,
                    )
                    .to_end_bound()
                ),
            Some(Ordering::Greater),
        );
    }

    #[test]
    fn relative_end_bound_same_times_inclusive_exclusive_bounds() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .partial_cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
            Some(Ordering::Greater),
        );
    }

    #[test]
    fn relative_end_bound_same_times_inclusive_bounds() {
        assert_eq!(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .partial_cmp(
                    &RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Inclusive,
                    )
                    .to_end_bound()
                ),
            Some(Ordering::Equal),
        );
    }
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
fn from_opt_signed_duration() {
    assert_eq!(
        RelativeStartBound::from(Some(SignedDuration::from_hours(8))),
        RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound()
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
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
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
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        RelativeStartBound::from(Bound::Excluded(SignedDuration::from_hours(1))),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        RelativeStartBound::from(Bound::Unbounded),
        RelativeStartBound::InfinitePast
    );
}

#[test]
fn try_from_rel_bound() {
    let start = RelativeFiniteBound::new(SignedDuration::ZERO).to_start_bound();

    assert_eq!(RelativeStartBound::try_from(start.to_bound()), Ok(start));
    assert_eq!(
        RelativeStartBound::try_from(RelativeEndBound::InfiniteFuture.to_bound()),
        Err(RelativeStartBoundTryFromRelativeBoundError)
    );
}

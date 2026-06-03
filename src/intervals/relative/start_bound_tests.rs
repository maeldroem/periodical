use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::start_bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelFiniteBoundPos, RelBound, RelEndBound};

#[test]
fn to_bound() {
    let start_bound = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();

    assert_eq!(start_bound.to_bound(), RelBound::Start(start_bound),);
}

#[test]
fn is_finite() {
    assert!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .is_finite()
    );
    assert!(!RelStartBound::InfinitePast.is_finite());
}

#[test]
fn is_infinite_past() {
    assert!(
        !RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .is_infinite_past()
    );
    assert!(RelStartBound::InfinitePast.is_infinite_past());
}

#[test]
fn finite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .finite(),
        Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()),
    );
    assert_eq!(RelStartBound::InfinitePast.finite(), None);
}

#[test]
fn opposite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .opposite(),
        Some(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound()
        ),
    );
    assert_eq!(RelStartBound::InfinitePast.opposite(), None);
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            RelStartBound::InfinitePast.cmp(&RelStartBound::InfinitePast),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() {
        assert_eq!(
            RelStartBound::InfinitePast
                .cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn finite_inf() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .cmp(&RelStartBound::InfinitePast),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_greater() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(2))
                .to_start_bound()
                .cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_less() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1))
                .to_start_bound()
                .cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_exclusive_bounds() {
        assert_eq!(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(
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
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(
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
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(
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
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(
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
        RelStartBound::from(RelFiniteBoundPos::new_with_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelStartBound::Finite(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_finite_start_bound()
        ),
    );
}

#[test]
fn from_opt_signed_duration() {
    assert_eq!(
        RelStartBound::from(Some(SignedDuration::from_hours(8))),
        RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound()
    );
    assert_eq!(RelStartBound::from(None::<SignedDuration>), RelStartBound::InfinitePast);
}

#[test]
fn from_opt_signed_duration_inclusivity() {
    assert_eq!(
        RelStartBound::from(Some((SignedDuration::from_hours(8), BoundInclusivity::Exclusive))),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_start_bound()
    );
    assert_eq!(
        RelStartBound::from(None::<(SignedDuration, BoundInclusivity)>),
        RelStartBound::InfinitePast
    );
}

#[test]
fn from_bound() {
    assert_eq!(
        RelStartBound::from(Bound::Included(SignedDuration::from_hours(1))),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        RelStartBound::from(Bound::Excluded(SignedDuration::from_hours(1))),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
            .to_start_bound(),
    );
    assert_eq!(RelStartBound::from(Bound::Unbounded), RelStartBound::InfinitePast);
}

#[test]
fn try_from_rel_bound() {
    assert_eq!(
        RelStartBound::try_from(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound()
                .to_bound()
        ),
        Ok(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound()
        )
    );
    assert_eq!(
        RelStartBound::try_from(RelStartBound::InfinitePast.to_bound()),
        Ok(RelStartBound::InfinitePast)
    );

    assert_eq!(
        RelStartBound::try_from(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_end_bound()
                .to_bound()
        ),
        Err(RelStartBoundTryFromRelBoundError)
    );
    assert_eq!(
        RelStartBound::try_from(RelEndBound::InfiniteFuture.to_bound()),
        Err(RelStartBoundTryFromRelBoundError)
    );
}

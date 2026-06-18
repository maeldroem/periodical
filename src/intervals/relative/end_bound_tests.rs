use std::cmp::Ordering;
use std::ops::Bound;

use jiff::SignedDuration;

use super::end_bound::*;
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::intervals::relative::{RelBound, RelFiniteBoundPos, RelStartBound};

#[test]
fn is_finite() {
    assert!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .is_finite()
    );
    assert!(!RelEndBound::InfiniteFuture.is_finite());
}

#[test]
fn is_infinite_future() {
    assert!(
        !RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .is_infinite_future()
    );
    assert!(RelEndBound::InfiniteFuture.is_infinite_future());
}

#[test]
fn opposite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .opposite(),
        Some(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
        ),
    );
    assert_eq!(RelEndBound::InfiniteFuture.opposite(), None);
}

#[test]
fn finite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .finite(),
        Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()),
    );
    assert_eq!(RelEndBound::InfiniteFuture.finite(), None,);
}

#[test]
fn to_bound() {
    let end_bound = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    assert_eq!(end_bound.to_bound(), RelBound::End(end_bound),);
}

#[test]
fn bound_extremality() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .bound_extremality(),
        BoundExtremality::End
    );
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            RelEndBound::InfiniteFuture.cmp(&RelEndBound::InfiniteFuture),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() {
        assert_eq!(
            RelEndBound::InfiniteFuture.cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn finite_inf() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1))
                .to_end_bound()
                .cmp(&RelEndBound::InfiniteFuture),
            Ordering::Less,
        );
    }

    #[test]
    fn different_times_greater() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(2))
                .to_end_bound()
                .cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_less() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1))
                .to_end_bound()
                .cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_exclusive_bounds() {
        assert_eq!(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                        .to_end_bound()
                ),
            Ordering::Equal,
        );
    }

    #[test]
    fn same_times_exclusive_inclusive_bounds() {
        assert_eq!(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                        .to_end_bound()
                ),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_inclusive_exclusive_bounds() {
        assert_eq!(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_end_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                        .to_end_bound()
                ),
            Ordering::Greater,
        );
    }

    #[test]
    fn same_times_inclusive_bounds() {
        assert_eq!(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_end_bound()
                .cmp(
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                        .to_end_bound()
                ),
            Ordering::Equal,
        );
    }
}

#[test]
fn from_relative_finite_end_bound() {
    assert_eq!(
        RelEndBound::from(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()),
        RelEndBound::Finite(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound())
    );
}

#[test]
fn from_relative_finite_bound_position() {
    assert_eq!(
        RelEndBound::from(RelFiniteBoundPos::new_with_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )),
        RelEndBound::Finite(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_finite_end_bound()
        ),
    );
}

#[test]
fn from_opt_signed_duration() {
    assert_eq!(
        RelEndBound::from(Some(SignedDuration::from_hours(8))),
        RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_end_bound()
    );
    assert_eq!(RelEndBound::from(None::<SignedDuration>), RelEndBound::InfiniteFuture);
}

#[test]
fn from_opt_signed_duration_inclusivity() {
    assert_eq!(
        RelEndBound::from(Some((SignedDuration::from_hours(8), BoundInclusivity::Exclusive))),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Exclusive).to_end_bound()
    );
    assert_eq!(
        RelEndBound::from(None::<(SignedDuration, BoundInclusivity)>),
        RelEndBound::InfiniteFuture
    );
}

#[test]
fn from_bound() {
    assert_eq!(
        RelEndBound::from(Bound::Included(SignedDuration::from_hours(1))),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,).to_end_bound(),
    );
    assert_eq!(
        RelEndBound::from(Bound::Excluded(SignedDuration::from_hours(1))),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,).to_end_bound(),
    );
    assert_eq!(RelEndBound::from(Bound::Unbounded), RelEndBound::InfiniteFuture);
}

#[test]
fn try_from_rel_bound() {
    assert_eq!(
        RelEndBound::try_from(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_end_bound()
                .to_bound()
        ),
        Ok(RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive).to_end_bound())
    );
    assert_eq!(
        RelEndBound::try_from(RelEndBound::InfiniteFuture.to_bound()),
        Ok(RelEndBound::InfiniteFuture)
    );

    assert_eq!(
        RelEndBound::try_from(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound()
                .to_bound()
        ),
        Err(RelEndBoundTryFromRelBoundError)
    );
    assert_eq!(
        RelEndBound::try_from(RelStartBound::InfinitePast.to_bound()),
        Err(RelEndBoundTryFromRelBoundError)
    );
}

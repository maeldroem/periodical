use std::cmp::Ordering;
use std::ops::Bound;

use jiff::Timestamp;

use super::end_bound::*;
use crate::intervals::absolute::{AbsBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::test_utils::{date_timestamp, datetime_timestamp};

#[test]
fn is_finite() {
    assert!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_end_bound()
            .is_finite()
    );
    assert!(!AbsEndBound::InfiniteFuture.is_finite());
}

#[test]
fn is_infinite_future() {
    assert!(
        !AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_end_bound()
            .is_infinite_future()
    );
    assert!(AbsEndBound::InfiniteFuture.is_infinite_future());
}

#[test]
fn opposite() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_end_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,).to_start_bound()
        ),
    );
    assert_eq!(AbsEndBound::InfiniteFuture.opposite(), None);
}

#[test]
fn finite() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_end_bound()
            .finite(),
        Some(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_finite_end_bound()),
    );
    assert_eq!(AbsEndBound::InfiniteFuture.finite(), None);
}

#[test]
fn to_bound() {
    let end_bound = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound();

    assert_eq!(end_bound.to_bound(), AbsBound::End(end_bound));
}

#[test]
fn bound_extremality() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
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
            AbsEndBound::InfiniteFuture.cmp(&AbsEndBound::InfiniteFuture),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() {
        assert_eq!(
            AbsEndBound::InfiniteFuture.cmp(&AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn finite_inf() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
                .to_end_bound()
                .cmp(&AbsEndBound::InfiniteFuture),
            Ordering::Less,
        );
    }

    #[test]
    fn different_times_greater() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2))
                .to_end_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_less() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
                .to_end_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_end_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_exclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_end_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                        .to_end_bound()
                ),
            Ordering::Equal,
        );
    }

    #[test]
    fn same_times_exclusive_inclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_end_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                        .to_end_bound()
                ),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_inclusive_exclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                .to_end_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                        .to_end_bound()
                ),
            Ordering::Greater,
        );
    }

    #[test]
    fn same_times_inclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                .to_end_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                        .to_end_bound()
                ),
            Ordering::Equal,
        );
    }
}

#[test]
fn from_absolute_finite_end_bound() {
    assert_eq!(
        AbsEndBound::from(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()),
        AbsEndBound::Finite(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound())
    );
}

#[test]
fn from_absolute_finite_bound_position() {
    assert_eq!(
        AbsEndBound::from(AbsFiniteBoundPos::new_with_incl(
            date_timestamp(2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsEndBound::Finite(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_finite_end_bound()
        ),
    );
}

#[test]
fn from_opt_timestamp() {
    assert_eq!(
        AbsEndBound::from(Some(datetime_timestamp(2026, 1, 1, 8, 0, 0))),
        AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 8, 0, 0)).to_end_bound()
    );
    assert_eq!(AbsEndBound::from(None::<Timestamp>), AbsEndBound::InfiniteFuture);
}

#[test]
fn from_opt_timestamp_inclusivity() {
    assert_eq!(
        AbsEndBound::from(Some((
            datetime_timestamp(2026, 1, 1, 8, 0, 0),
            BoundInclusivity::Exclusive
        ))),
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound()
    );
    assert_eq!(
        AbsEndBound::from(None::<(Timestamp, BoundInclusivity)>),
        AbsEndBound::InfiniteFuture
    );
}

#[test]
fn from_bound() {
    assert_eq!(
        AbsEndBound::from(Bound::Included(date_timestamp(2025, 1, 1))),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_end_bound(),
    );
    assert_eq!(
        AbsEndBound::from(Bound::Excluded(date_timestamp(2025, 1, 1))),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,).to_end_bound(),
    );
    assert_eq!(AbsEndBound::from(Bound::Unbounded), AbsEndBound::InfiniteFuture);
}

#[test]
fn try_from_abs_bound() {
    assert_eq!(
        AbsEndBound::try_from(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_end_bound()
                .to_bound()
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_end_bound())
    );
    assert_eq!(
        AbsEndBound::try_from(AbsEndBound::InfiniteFuture.to_bound()),
        Ok(AbsEndBound::InfiniteFuture)
    );

    assert_eq!(
        AbsEndBound::try_from(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_start_bound()
                .to_bound()
        ),
        Err(AbsEndBoundTryFromAbsBoundError)
    );
    assert_eq!(
        AbsEndBound::try_from(AbsStartBound::InfinitePast.to_bound()),
        Err(AbsEndBoundTryFromAbsBoundError)
    );
}

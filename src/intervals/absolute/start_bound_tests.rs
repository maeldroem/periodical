use std::cmp::Ordering;
use std::ops::Bound;

use jiff::Timestamp;

use super::start_bound::*;
use crate::intervals::absolute::{AbsBound, AbsEndBound, AbsFiniteBoundPos};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::test_data::date_timestamp;

#[test]
fn is_finite() {
    assert!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_start_bound()
            .is_finite()
    );
    assert!(!AbsStartBound::InfinitePast.is_finite());
}

#[test]
fn is_infinite_past() {
    assert!(
        !AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_start_bound()
            .is_infinite_past()
    );
    assert!(AbsStartBound::InfinitePast.is_infinite_past());
}

#[test]
fn opposite() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_start_bound()
            .opposite(),
        Some(AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,).to_end_bound()),
    );
    assert_eq!(AbsStartBound::InfinitePast.opposite(), None);
}

#[test]
fn finite() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_start_bound()
            .finite(),
        Some(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_finite_start_bound()),
    );
    assert_eq!(AbsStartBound::InfinitePast.finite(), None);
}

#[test]
fn to_bound() {
    let start_bound = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();

    assert_eq!(start_bound.to_bound(), AbsBound::Start(start_bound),);
}

#[test]
fn bound_extremality() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
            .to_start_bound()
            .bound_extremality(),
        BoundExtremality::Start
    );
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            AbsStartBound::InfinitePast.cmp(&AbsStartBound::InfinitePast),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() {
        assert_eq!(
            AbsStartBound::InfinitePast.cmp(&AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn finite_inf() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
                .to_start_bound()
                .cmp(&AbsStartBound::InfinitePast),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_greater() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2))
                .to_start_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound()),
            Ordering::Greater,
        );
    }

    #[test]
    fn different_times_less() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
                .to_start_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound()),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_exclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                        .to_start_bound()
                ),
            Ordering::Equal,
        );
    }

    #[test]
    fn same_times_exclusive_inclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                        .to_start_bound()
                ),
            Ordering::Greater,
        );
    }

    #[test]
    fn same_times_inclusive_exclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                        .to_start_bound()
                ),
            Ordering::Less,
        );
    }

    #[test]
    fn same_times_inclusive_bounds() {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                .to_start_bound()
                .cmp(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,)
                        .to_start_bound()
                ),
            Ordering::Equal,
        );
    }
}

#[test]
fn from_absolute_finite_start_bound() {
    assert_eq!(
        AbsStartBound::from(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()),
        AbsStartBound::Finite(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound())
    );
}

#[test]
fn from_absolute_finite_bound_position() {
    assert_eq!(
        AbsStartBound::from(AbsFiniteBoundPos::new_with_incl(
            date_timestamp(2025, 1, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsStartBound::Finite(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_finite_start_bound()
        ),
    );
}

#[test]
fn from_opt_timestamp() {
    assert_eq!(
        AbsStartBound::from(Some(date_timestamp(2026, 1, 1))),
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
    );
    assert_eq!(AbsStartBound::from(None::<Timestamp>), AbsStartBound::InfinitePast);
}

#[test]
fn from_opt_timestamp_inclusivity() {
    assert_eq!(
        AbsStartBound::from(Some((date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive))),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound()
    );
    assert_eq!(
        AbsStartBound::from(None::<(Timestamp, BoundInclusivity)>),
        AbsStartBound::InfinitePast
    );
}

#[test]
fn from_bound() {
    assert_eq!(
        AbsStartBound::from(Bound::Included(date_timestamp(2025, 1, 1))),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_start_bound(),
    );
    assert_eq!(
        AbsStartBound::from(Bound::Excluded(date_timestamp(2025, 1, 1))),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,).to_start_bound(),
    );
    assert_eq!(AbsStartBound::from(Bound::Unbounded), AbsStartBound::InfinitePast);
}

#[test]
fn try_from_abs_bound() {
    assert_eq!(
        AbsStartBound::try_from(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_start_bound()
                .to_bound()
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound())
    );
    assert_eq!(
        AbsStartBound::try_from(AbsStartBound::InfinitePast.to_bound()),
        Ok(AbsStartBound::InfinitePast)
    );

    assert_eq!(
        AbsStartBound::try_from(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_end_bound()
                .to_bound()
        ),
        Err(AbsStartBoundTryFromAbsBoundError)
    );
    assert_eq!(
        AbsStartBound::try_from(AbsEndBound::InfiniteFuture.to_bound()),
        Err(AbsStartBoundTryFromAbsBoundError)
    );
}

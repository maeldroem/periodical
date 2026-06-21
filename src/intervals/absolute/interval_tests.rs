use std::cmp::Ordering;
use std::ops::Bound;
use std::time::Duration;

use super::interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasIntervalType,
    HasIntervalTypeWithRel,
    HasOpenness,
    HasRelativity,
    IntervalType,
    IntervalTypeWithRel,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::special::UnboundedInterval;
use crate::test_utils::date_timestamp;

mod from_range {
    use super::*;

    #[test]
    fn included_included() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            AbsInterval::from_range(start..=end),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(start, end))
        );
    }

    #[test]
    fn included_excluded() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            AbsInterval::from_range(start..end),
            AbsInterval::Bounded(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Inclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn included_unbounded() {
        let start = date_timestamp(2026, 1, 1);

        assert_eq!(
            AbsInterval::from_range(start..),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(start, OpeningDirection::ToFuture))
        );
    }

    #[test]
    fn excluded_included() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            AbsInterval::from_range((Bound::Excluded(start), Bound::Included(end))),
            AbsInterval::Bounded(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Inclusive
            ))
        );
    }

    #[test]
    fn excluded_excluded() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            AbsInterval::from_range((Bound::Excluded(start), Bound::Excluded(end))),
            AbsInterval::Bounded(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn excluded_unbounded() {
        let start = date_timestamp(2026, 1, 1);

        assert_eq!(
            AbsInterval::from_range((Bound::Excluded(start), Bound::Unbounded)),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                start,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture
            ))
        );
    }

    #[test]
    fn unbounded_included() {
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            AbsInterval::from_range(..=end),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(end, OpeningDirection::ToPast))
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            AbsInterval::from_range(..end),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(AbsInterval::from_range(..), AbsInterval::Unbounded(UnboundedInterval));
    }
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 3)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 3)
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2),
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2),
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_unbounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Greater,
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsInterval::Bounded(
                BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2))
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn bounded() {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            date_timestamp(2026, 1, 1),
            date_timestamp(2026, 1, 2)
        ))
        .bounded(),
        Some(BoundedAbsInterval::from_times(
            date_timestamp(2026, 1, 1),
            date_timestamp(2026, 1, 2)
        ))
    );
    assert_eq!(
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            date_timestamp(2026, 1, 1),
            OpeningDirection::ToFuture
        ))
        .bounded(),
        None
    );
    assert_eq!(AbsInterval::Unbounded(UnboundedInterval).bounded(), None);
}

#[test]
fn half_bounded() {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            date_timestamp(2026, 1, 1),
            date_timestamp(2026, 1, 2)
        ))
        .half_bounded(),
        None
    );
    assert_eq!(
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            date_timestamp(2026, 1, 1),
            OpeningDirection::ToFuture
        ))
        .half_bounded(),
        Some(HalfBoundedAbsInterval::from_time(
            date_timestamp(2026, 1, 1),
            OpeningDirection::ToFuture
        ))
    );
    assert_eq!(AbsInterval::Unbounded(UnboundedInterval).half_bounded(), None);
}

#[test]
fn unbounded() {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            date_timestamp(2026, 1, 1),
            date_timestamp(2026, 1, 2)
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            date_timestamp(2026, 1, 1),
            OpeningDirection::ToFuture
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        AbsInterval::Unbounded(UnboundedInterval).unbounded(),
        Some(UnboundedInterval)
    );
}

#[test]
fn to_emptiable() {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            date_timestamp(2026, 1, 1),
            date_timestamp(2026, 1, 2)
        ))
        .to_emptiable(),
        EmptiableAbsInterval::Bound(AbsInterval::Bounded(BoundedAbsInterval::from_times(
            date_timestamp(2026, 1, 1),
            date_timestamp(2026, 1, 2)
        )))
    );
}

mod abs_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
            )
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
        );
    }
}

mod abs_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .abs_start(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .abs_start(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .abs_start(),
            AbsStartBound::InfinitePast
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).abs_start(),
            AbsStartBound::InfinitePast
        );
    }
}

mod abs_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .abs_end(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .abs_end(),
            AbsEndBound::InfiniteFuture
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .abs_end(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).abs_end(),
            AbsEndBound::InfiniteFuture
        );
    }
}

mod emptiable_abs_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .emptiable_abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
            )
            .to_emptiable()
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .emptiable_abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).emptiable_abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
        );
    }
}

mod partial_abs_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
    }
}

mod partial_abs_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound())
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .duration(),
            IntervalDuration::Finite(Duration::from_hours(24), Epsilon::None)
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).duration(),
            IntervalDuration::Infinite
        );
    }
}

mod relativity {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .relativity(),
            Relativity::Absolute
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .relativity(),
            Relativity::Absolute
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(AbsInterval::Unbounded(UnboundedInterval).relativity(), Relativity::Any);
    }
}

mod openness {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .openness(),
            Openness::Bounded
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .openness(),
            Openness::HalfBounded
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).openness(),
            Openness::Unbounded
        );
    }
}

mod ord {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 3)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 3)
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2),
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2),
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_unbounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .cmp(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Greater,
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast)
            )),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

mod is_empty {
    use super::*;

    #[test]
    fn bounded() {
        assert!(
            !AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .is_empty()
        );
    }

    #[test]
    fn half_bounded() {
        assert!(
            !AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .is_empty()
        );
    }

    #[test]
    fn unbounded() {
        assert!(!AbsInterval::Unbounded(UnboundedInterval).is_empty());
    }
}

mod interval_type {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2))
                .to_interval()
                .interval_type(),
            IntervalType::Bounded
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1))
                .to_interval()
                .interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1))
                .to_interval()
                .interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            UnboundedInterval.to_abs_interval().interval_type(),
            IntervalType::Unbounded
        );
    }
}

mod interval_type_with_rel {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2))
                .to_interval()
                .interval_type_with_rel(),
            IntervalTypeWithRel::AbsBounded
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1))
                .to_interval()
                .interval_type_with_rel(),
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1))
                .to_interval()
                .interval_type_with_rel(),
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            UnboundedInterval.to_abs_interval().interval_type_with_rel(),
            IntervalTypeWithRel::Unbounded
        );
    }
}

#[test]
fn from_bounded_interval() {
    let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
    assert_eq!(AbsInterval::from(bounded.clone()), AbsInterval::Bounded(bounded));
}

#[test]
fn from_half_bounded_interval() {
    let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);
    assert_eq!(
        AbsInterval::from(half_bounded.clone()),
        AbsInterval::HalfBounded(half_bounded)
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        AbsInterval::from(UnboundedInterval),
        AbsInterval::Unbounded(UnboundedInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
            )),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            )),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            )),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound()
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::Unbounded(UnboundedInterval)
        );
    }
}

mod try_from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))),
        );
    }

    #[test]
    fn bound_half_bounded_to_future() {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Ok(AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))),
        );
    }

    #[test]
    fn bound_half_bounded_to_past() {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            )))
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
            ),
            Ok(AbsInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            AbsInterval::try_from(EmptiableAbsBoundPair::Empty),
            Err(AbsIntervalTryFromEmptiableAbsBoundPairError)
        );
    }
}

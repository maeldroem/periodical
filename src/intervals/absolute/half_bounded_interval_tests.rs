use std::ops::Bound;

use super::half_bounded_interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    HasDuration,
    HasIntervalType,
    HasIntervalTypeWithRel,
    HasOpeningDirection,
    HasOpenness,
    HasRelativity,
    IntervalType,
    IntervalTypeWithRel,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::test_utils::date_timestamp;

mod new {
    use super::*;

    #[test]
    fn to_future() {
        let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        assert_eq!(
            HalfBoundedAbsInterval::new(pos, OpeningDirection::ToFuture),
            HalfBoundedToFutureAbsInterval::new(pos.to_finite_start_bound()).to_half_bounded_interval()
        );
    }

    #[test]
    fn to_past() {
        let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        assert_eq!(
            HalfBoundedAbsInterval::new(pos, OpeningDirection::ToPast),
            HalfBoundedToPastAbsInterval::new(pos.to_finite_end_bound()).to_half_bounded_interval()
        );
    }
}

mod from_time {
    use super::*;

    #[test]
    fn to_future() {
        let time = date_timestamp(2026, 1, 1);
        assert_eq!(
            HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToFuture),
            HalfBoundedToFutureAbsInterval::from_time(time).to_half_bounded_interval()
        );
    }

    #[test]
    fn to_past() {
        let time = date_timestamp(2026, 1, 1);
        assert_eq!(
            HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToPast),
            HalfBoundedToPastAbsInterval::from_time(time).to_half_bounded_interval()
        );
    }
}

mod from_time_incl {
    use super::*;

    #[test]
    fn to_future() {
        let time = date_timestamp(2026, 1, 1);
        assert_eq!(
            HalfBoundedAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive, OpeningDirection::ToFuture),
            HalfBoundedToFutureAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive)
                .to_half_bounded_interval()
        );
    }

    #[test]
    fn to_past() {
        let time = date_timestamp(2026, 1, 1);
        assert_eq!(
            HalfBoundedAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive, OpeningDirection::ToPast),
            HalfBoundedToPastAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive).to_half_bounded_interval()
        );
    }
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            HalfBoundedAbsInterval::try_from_range(start..=end),
            Err(HalfBoundedAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_excluded() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            HalfBoundedAbsInterval::try_from_range(start..end),
            Err(HalfBoundedAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_unbounded() {
        let start = date_timestamp(2026, 1, 1);

        assert_eq!(
            HalfBoundedAbsInterval::try_from_range(start..),
            Ok(HalfBoundedAbsInterval::from_time(start, OpeningDirection::ToFuture))
        );
    }

    #[test]
    fn excluded_included() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            HalfBoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Err(HalfBoundedAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_excluded() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            HalfBoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Err(HalfBoundedAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_unbounded() {
        let start = date_timestamp(2026, 1, 1);

        assert_eq!(
            HalfBoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Ok(HalfBoundedAbsInterval::from_time_incl(
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
            HalfBoundedAbsInterval::try_from_range(..=end),
            Ok(HalfBoundedAbsInterval::from_time(end, OpeningDirection::ToPast))
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            HalfBoundedAbsInterval::try_from_range(..end),
            Ok(HalfBoundedAbsInterval::from_time_incl(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from_range(..),
            Err(HalfBoundedAbsIntervalTryFromRangeError)
        );
    }
}

mod reference {
    use super::*;

    #[test]
    fn to_future() {
        let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        assert_eq!(
            HalfBoundedAbsInterval::new(pos, OpeningDirection::ToFuture).reference(),
            pos.to_finite_start_bound().to_finite_bound(),
        );
    }

    #[test]
    fn to_past() {
        let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        assert_eq!(
            HalfBoundedAbsInterval::new(pos, OpeningDirection::ToPast).reference(),
            pos.to_finite_end_bound().to_finite_bound(),
        );
    }
}

#[test]
fn reference_pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));

    assert_eq!(
        HalfBoundedAbsInterval::new(pos, OpeningDirection::ToFuture).reference_pos(),
        pos
    );
}

#[test]
fn reference_time() {
    let time = date_timestamp(2026, 1, 1);

    assert_eq!(
        HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToFuture).reference_time(),
        time
    );
}

#[test]
fn reference_inclusivity() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time_incl(
            date_timestamp(2026, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
        .reference_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

mod set_reference {
    use super::*;

    #[test]
    fn to_future_set_finite_bound_start() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

        let new_reference = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2))
            .to_finite_start_bound()
            .to_finite_bound();
        interval.set_reference(new_reference);

        assert_eq!(interval.reference(), new_reference);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_future_set_finite_bound_end() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

        let new_reference = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2))
            .to_finite_end_bound()
            .to_finite_bound();
        interval.set_reference(new_reference);

        assert_eq!(interval.reference(), new_reference);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }

    #[test]
    fn to_past_set_finite_bound_start() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast);

        let new_reference = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2))
            .to_finite_start_bound()
            .to_finite_bound();
        interval.set_reference(new_reference);

        assert_eq!(interval.reference(), new_reference);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past_set_finite_bound_end() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast);

        let new_reference = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2))
            .to_finite_end_bound()
            .to_finite_bound();
        interval.set_reference(new_reference);

        assert_eq!(interval.reference(), new_reference);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }
}

mod set_reference_pos {
    use super::*;

    #[test]
    fn to_future() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

        let new_pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2));
        interval.set_reference_pos(new_pos);

        assert_eq!(interval.reference_pos(), new_pos);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast);

        let new_pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2));
        interval.set_reference_pos(new_pos);

        assert_eq!(interval.reference_pos(), new_pos);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }
}

mod set_reference_time {
    use super::*;

    #[test]
    fn to_future() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

        let new_time = date_timestamp(2026, 1, 2);
        interval.set_reference_time(new_time);

        assert_eq!(interval.reference_time(), new_time);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past() {
        let mut interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast);

        let new_time = date_timestamp(2026, 1, 2);
        interval.set_reference_time(new_time);

        assert_eq!(interval.reference_time(), new_time);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }
}

mod set_reference_inclusivity {
    use super::*;

    #[test]
    fn to_future() {
        let time = date_timestamp(2026, 1, 1);
        let mut interval = HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToFuture);

        interval.set_reference_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.reference_time(), time);
        assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past() {
        let time = date_timestamp(2026, 1, 1);
        let mut interval = HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToPast);

        interval.set_reference_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.reference_time(), time);
        assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }
}

mod set_opening_direction {
    use super::*;

    mod from_to_future {
        use super::*;

        #[test]
        fn to_to_future() {
            let pos = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedAbsInterval::new(pos, OpeningDirection::ToFuture);

            interval.set_opening_direction(OpeningDirection::ToFuture);

            assert_eq!(interval.reference_pos(), pos);
            assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
        }

        #[test]
        fn to_to_past() {
            let pos = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedAbsInterval::new(pos, OpeningDirection::ToFuture);

            interval.set_opening_direction(OpeningDirection::ToPast);

            assert_eq!(interval.reference_pos(), pos);
            assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
        }
    }

    mod from_to_past {
        use super::*;

        #[test]
        fn to_to_future() {
            let pos = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedAbsInterval::new(pos, OpeningDirection::ToPast);

            interval.set_opening_direction(OpeningDirection::ToFuture);

            assert_eq!(interval.reference_pos(), pos);
            assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
        }

        #[test]
        fn to_to_past() {
            let pos = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedAbsInterval::new(pos, OpeningDirection::ToPast);

            interval.set_opening_direction(OpeningDirection::ToPast);

            assert_eq!(interval.reference_pos(), pos);
            assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
        }
    }
}

mod opposite {
    use super::*;

    #[test]
    fn from_to_future() {
        let time = date_timestamp(2026, 1, 1);
        assert_eq!(
            HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToFuture).opposite(),
            HalfBoundedAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive, OpeningDirection::ToPast)
        );
    }

    #[test]
    fn from_to_past() {
        let time = date_timestamp(2026, 1, 1);
        assert_eq!(
            HalfBoundedAbsInterval::from_time(time, OpeningDirection::ToPast).opposite(),
            HalfBoundedAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive, OpeningDirection::ToFuture)
        );
    }
}

#[test]
fn half_bounded_to_future() {
    let hb_to_future = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        hb_to_future.clone().to_half_bounded_interval().half_bounded_to_future(),
        Some(hb_to_future)
    );
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast)
            .half_bounded_to_future(),
        None
    );
}

#[test]
fn half_bounded_to_past() {
    let hb_to_past = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
            .half_bounded_to_past(),
        None
    );
    assert_eq!(
        hb_to_past.clone().to_half_bounded_interval().half_bounded_to_past(),
        Some(hb_to_past)
    );
}

#[test]
fn to_interval() {
    let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_interval(),
        AbsInterval::HalfBounded(half_bounded)
    );
}

#[test]
fn to_emptiable_interval() {
    let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_emptiable_interval(),
        EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(half_bounded))
    );
}

#[test]
fn opening_direction() {
    let to_future = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);
    let to_past = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast);

    assert_eq!(to_future.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(to_past.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn openness() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).openness(),
        Openness::HalfBounded
    );
}

#[test]
fn relativity() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).relativity(),
        Relativity::Absolute
    );
}

#[test]
fn duration() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).duration(),
        IntervalDuration::Infinite
    );
}

#[test]
fn abs_bound_pair() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
    );
}

#[test]
fn abs_start() {
    let reference = date_timestamp(2026, 1, 1);

    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToFuture).abs_start(),
        AbsFiniteBoundPos::new(reference).to_start_bound()
    );
    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToPast).abs_start(),
        AbsStartBound::InfinitePast
    );
}

#[test]
fn abs_end() {
    let reference = date_timestamp(2026, 1, 1);

    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToFuture).abs_end(),
        AbsEndBound::InfiniteFuture
    );
    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToPast).abs_end(),
        AbsFiniteBoundPos::new(reference).to_end_bound()
    );
}

#[test]
fn emptiable_abs_bound_pair() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
            .emptiable_abs_bound_pair(),
        EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture
        ))
    );
}

#[test]
fn partial_abs_start() {
    let reference = date_timestamp(2026, 1, 1);

    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToFuture).partial_abs_start(),
        Some(AbsFiniteBoundPos::new(reference).to_start_bound())
    );
    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToPast).partial_abs_start(),
        Some(AbsStartBound::InfinitePast)
    );
}

#[test]
fn partial_abs_end() {
    let reference = date_timestamp(2026, 1, 1);

    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToFuture).partial_abs_end(),
        Some(AbsEndBound::InfiniteFuture)
    );
    assert_eq!(
        HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToPast).partial_abs_end(),
        Some(AbsFiniteBoundPos::new(reference).to_end_bound())
    );
}

#[test]
fn is_empty() {
    assert!(!HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).is_empty());
    assert!(!HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast).is_empty());
}

#[test]
fn interval_type() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToFuture)
    );
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast).interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn interval_type_with_rel() {
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
            .interval_type_with_rel(),
        IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture)
    );
    assert_eq!(
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast)
            .interval_type_with_rel(),
        IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn from_timestamp_opening_direction_pair() {
    assert_eq!(
        HalfBoundedAbsInterval::from((date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)),
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_timestamp_inclusivity_opening_direction_triple() {
    assert_eq!(
        HalfBoundedAbsInterval::from((
            date_timestamp(2026, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast
        )),
        HalfBoundedAbsInterval::from_time_incl(
            date_timestamp(2026, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn from_finite_bound_pos_and_opening_direction() {
    let pos = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
    assert_eq!(
        HalfBoundedAbsInterval::from((pos, OpeningDirection::ToFuture)),
        HalfBoundedAbsInterval::new(pos, OpeningDirection::ToFuture)
    );
    assert_eq!(
        HalfBoundedAbsInterval::from((pos, OpeningDirection::ToPast)),
        HalfBoundedAbsInterval::new(pos, OpeningDirection::ToPast)
    );
}

#[test]
fn from_range_from() {
    assert_eq!(
        HalfBoundedAbsInterval::from(date_timestamp(2026, 1, 1)..),
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_range_to() {
    assert_eq!(
        HalfBoundedAbsInterval::from(..date_timestamp(2026, 1, 1)),
        HalfBoundedAbsInterval::from_time_incl(
            date_timestamp(2026, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn from_range_to_inclusive() {
    assert_eq!(
        HalfBoundedAbsInterval::from(..=date_timestamp(2026, 1, 1)),
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast),
    );
}

#[test]
fn from_half_bounded_to_future() {
    let hb_to_future = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        HalfBoundedAbsInterval::from(hb_to_future.clone()),
        HalfBoundedAbsInterval::ToFuture(hb_to_future)
    );
}

#[test]
fn from_half_bounded_to_past() {
    let hb_to_past = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        HalfBoundedAbsInterval::from(hb_to_past.clone()),
        HalfBoundedAbsInterval::ToPast(hb_to_past)
    );
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
            )),
            Err(HalfBoundedAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn finite_infinite() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            Ok(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
        );
    }

    #[test]
    fn infinite_finite() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
            )),
            Ok(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            Err(HalfBoundedAbsIntervalTryFromAbsBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));

        assert_eq!(
            HalfBoundedAbsInterval::try_from(bounded.to_interval()),
            Err(HalfBoundedAbsIntervalTryFromAbsIntervalError)
        );
    }

    #[test]
    fn half_bounded() {
        let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedAbsInterval::try_from(half_bounded.clone().to_interval()),
            Ok(half_bounded)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from(UnboundedInterval.to_abs_interval()),
            Err(HalfBoundedAbsIntervalTryFromAbsIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() {
        let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));

        assert_eq!(
            HalfBoundedAbsInterval::try_from(bounded.to_emptiable_interval()),
            Err(HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn bound_half_bounded() {
        let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedAbsInterval::try_from(half_bounded.clone().to_emptiable_interval()),
            Ok(half_bounded)
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from(UnboundedInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedAbsInterval::try_from(EmptyInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }
}

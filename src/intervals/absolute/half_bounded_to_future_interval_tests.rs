use std::ops::Bound;

use super::half_bounded_to_future_interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    BoundedAbsInterval,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
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
use crate::test_data::date_timestamp;

#[test]
fn new() {
    let _ =
        HalfBoundedToFutureAbsInterval::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound());
}

#[test]
fn from_time() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from_time(time);

    assert_eq!(interval.start_time(), time);
}

#[test]
fn from_time_incl() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);

    assert_eq!(interval.start_time(), time);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from_range(date_timestamp(2026, 1, 1)..=date_timestamp(2026, 1, 2)),
            Err(HalfBoundedToFutureAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_excluded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from_range(date_timestamp(2026, 1, 1)..date_timestamp(2026, 1, 2)),
            Err(HalfBoundedToFutureAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_unbounded() {
        let time = date_timestamp(2026, 1, 1);
        let interval = HalfBoundedToFutureAbsInterval::try_from_range(time..).unwrap();

        assert_eq!(interval.start_time(), time);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn excluded_included() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from_range((
                Bound::Excluded(date_timestamp(2026, 1, 1)),
                Bound::Included(date_timestamp(2026, 1, 2))
            )),
            Err(HalfBoundedToFutureAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_excluded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from_range((
                Bound::Excluded(date_timestamp(2026, 1, 1)),
                Bound::Excluded(date_timestamp(2026, 1, 2))
            )),
            Err(HalfBoundedToFutureAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_unbounded() {
        let time = date_timestamp(2026, 1, 1);
        let interval =
            HalfBoundedToFutureAbsInterval::try_from_range((Bound::Excluded(time), Bound::Unbounded)).unwrap();

        assert_eq!(interval.start_time(), time);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn unbounded_included() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from_range(..=date_timestamp(2026, 1, 1)),
            Err(HalfBoundedToFutureAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_excluded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from_range(..date_timestamp(2026, 1, 1)),
            Err(HalfBoundedToFutureAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from_range(..),
            Err(HalfBoundedToFutureAbsIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    assert_eq!(HalfBoundedToFutureAbsInterval::new(start).start(), start);
}

#[test]
fn end() {
    assert_eq!(
        HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1)).end(),
        AbsEndBound::InfiniteFuture
    );
}

#[test]
fn start_time() {
    let time = date_timestamp(2026, 1, 1);
    assert_eq!(HalfBoundedToFutureAbsInterval::from_time(time).start_time(), time);
}

#[test]
fn start_inclusivity() {
    assert_eq!(
        HalfBoundedToFutureAbsInterval::from_time_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .start_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn start_mut() {
    let mut interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    let _ = interval.start_mut();
}

#[test]
fn set_start() {
    let mut interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    let new_start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
        .to_finite_start_bound();
    interval.set_start(new_start);

    assert_eq!(interval.start(), new_start);
}

#[test]
fn set_start_time() {
    let mut interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    let new_start_time = date_timestamp(2026, 1, 2);
    interval.set_start_time(new_start_time);

    assert_eq!(interval.start_time(), new_start_time);
}

#[test]
fn set_start_inclusivity() {
    let mut interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    interval.set_start_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn opposite() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from_time(time);

    assert_eq!(
        interval.opposite(),
        HalfBoundedToPastAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive)
    );
}

#[test]
fn to_half_bounded_interval() {
    let hb_to_future = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        hb_to_future.clone().to_half_bounded_interval(),
        HalfBoundedAbsInterval::ToFuture(hb_to_future)
    );
}

#[test]
fn to_interval() {
    let hb_to_future = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        hb_to_future.clone().to_interval(),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::ToFuture(hb_to_future))
    );
}

#[test]
fn to_emptiable_interval() {
    let hb_to_future = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        hb_to_future.clone().to_emptiable_interval(),
        EmptiableAbsInterval::Bound(hb_to_future.to_interval())
    );
}

#[test]
fn openness() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.openness(), Openness::HalfBounded);
}

#[test]
fn relativity() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.relativity(), Relativity::Absolute);
}

#[test]
fn duration() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.duration(), IntervalDuration::Infinite);
}

#[test]
fn opening_direction() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn abs_bound_pair() {
    let start_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from_time(start_time);

    assert_eq!(
        interval.abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(start_time).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
    );
}

#[test]
fn abs_start() {
    let start_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from_time(start_time);

    assert_eq!(
        interval.abs_start(),
        AbsFiniteBoundPos::new(start_time).to_start_bound(),
    );
}

#[test]
fn abs_end() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.abs_end(), AbsEndBound::InfiniteFuture);
}

#[test]
fn emptiable_abs_bound_pair() {
    let start_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from_time(start_time);

    assert_eq!(
        interval.emptiable_abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(start_time).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

#[test]
fn partial_abs_start() {
    let start_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from_time(start_time);

    assert_eq!(
        interval.partial_abs_start(),
        Some(AbsFiniteBoundPos::new(start_time).to_start_bound()),
    );
}

#[test]
fn partial_abs_end() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.partial_abs_end(), Some(AbsEndBound::InfiniteFuture));
}

#[test]
fn is_empty() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert!(!interval.is_empty());
}

#[test]
fn interval_type() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(
        interval.interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToFuture)
    );
}

#[test]
fn interval_type_with_rel() {
    let interval = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(
        interval.interval_type_with_rel(),
        IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture)
    );
}

#[test]
fn from_timestamp() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from(time);

    assert_eq!(interval.start_time(), time);
}

#[test]
fn from_timestamp_and_bound_inclusivity() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToFutureAbsInterval::from((time, BoundInclusivity::Exclusive));

    assert_eq!(interval.start_time(), time);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_finite_bound_pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
    assert_eq!(
        HalfBoundedToFutureAbsInterval::from(pos),
        HalfBoundedToFutureAbsInterval::new(pos.to_finite_start_bound())
    );
}

#[test]
fn from_finite_start_bound() {
    let finite_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    assert_eq!(
        HalfBoundedToFutureAbsInterval::from(finite_start),
        HalfBoundedToFutureAbsInterval::new(finite_start)
    );
}

#[test]
fn from_range_from() {
    let time = date_timestamp(2026, 1, 1);
    assert_eq!(
        HalfBoundedToFutureAbsInterval::from(time..),
        HalfBoundedToFutureAbsInterval::from_time(time)
    );
}

mod try_from_bound_pair {
    use super::*;
    use crate::intervals::absolute::AbsStartBound;

    #[test]
    fn inclusive_inclusive() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();
        let bound_pair = AbsBoundPair::new(start, end);

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(bound_pair),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn inclusive_exclusive() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
        let end =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn inclusive_infinite() {
        let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        let start = pos.to_start_bound();
        let end = AbsEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Ok(HalfBoundedToFutureAbsInterval::new(pos.to_finite_start_bound()))
        );
    }

    #[test]
    fn exclusive_inclusive() {
        let start =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn exclusive_exclusive() {
        let start =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
        let end =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn exclusive_infinite() {
        let pos = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
        let start = pos.to_start_bound();
        let end = AbsEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Ok(HalfBoundedToFutureAbsInterval::new(pos.to_finite_start_bound()))
        );
    }

    #[test]
    fn infinite_inclusive() {
        let start = AbsStartBound::InfinitePast;
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn infinite_exclusive() {
        let start = AbsStartBound::InfinitePast;
        let end =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(
                BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2)).to_interval()
            ),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(hb_to_future.clone().to_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(
                HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1)).to_interval()
            ),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(UnboundedInterval.to_abs_interval()),
            Err(HalfBoundedToFutureAbsIntervalTryFromAbsIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(
                BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2))
                    .to_emptiable_interval()
            ),
            Err(HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1));

        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(hb_to_future.clone().to_emptiable_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(
                HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1)).to_emptiable_interval()
            ),
            Err(HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(UnboundedInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedToFutureAbsInterval::try_from(EmptyInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedToFutureAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }
}

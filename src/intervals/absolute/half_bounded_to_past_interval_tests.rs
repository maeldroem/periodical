use std::ops::Bound;

use super::half_bounded_to_past_interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
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
    let _ = HalfBoundedToPastAbsInterval::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound());
}

#[test]
fn from_time() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from_time(time);

    assert_eq!(interval.end_time(), time);
}

#[test]
fn from_time_incl() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive);

    assert_eq!(interval.end_time(), time);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from_range(date_timestamp(2026, 1, 1)..=date_timestamp(2026, 1, 2)),
            Err(HalfBoundedToPastAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_excluded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from_range(date_timestamp(2026, 1, 1)..date_timestamp(2026, 1, 2)),
            Err(HalfBoundedToPastAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_unbounded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from_range(date_timestamp(2026, 1, 1)..),
            Err(HalfBoundedToPastAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_included() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from_range((
                Bound::Excluded(date_timestamp(2026, 1, 1)),
                Bound::Included(date_timestamp(2026, 1, 2))
            )),
            Err(HalfBoundedToPastAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_excluded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from_range((
                Bound::Excluded(date_timestamp(2026, 1, 1)),
                Bound::Excluded(date_timestamp(2026, 1, 2))
            )),
            Err(HalfBoundedToPastAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_unbounded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from_range((
                Bound::Excluded(date_timestamp(2026, 1, 1)),
                Bound::Unbounded
            )),
            Err(HalfBoundedToPastAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_included() {
        let time = date_timestamp(2026, 1, 1);
        let interval = HalfBoundedToPastAbsInterval::try_from_range(..=time).unwrap();

        assert_eq!(interval.end_time(), time);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn unbounded_excluded() {
        let time = date_timestamp(2026, 1, 1);
        let interval = HalfBoundedToPastAbsInterval::try_from_range(..time).unwrap();

        assert_eq!(interval.end_time(), time);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from_range(..),
            Err(HalfBoundedToPastAbsIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() {
    assert_eq!(
        HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1)).start(),
        AbsStartBound::InfinitePast
    );
}

#[test]
fn end() {
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
    assert_eq!(HalfBoundedToPastAbsInterval::new(end).end(), end);
}

#[test]
fn end_time() {
    let time = date_timestamp(2026, 1, 1);
    assert_eq!(HalfBoundedToPastAbsInterval::from_time(time).end_time(), time);
}

#[test]
fn end_inclusivity() {
    assert_eq!(
        HalfBoundedToPastAbsInterval::from_time_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .end_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn end_mut() {
    let mut interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    let _ = interval.end_mut();
}

#[test]
fn set_end() {
    let mut interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    let new_end =
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_finite_end_bound();
    interval.set_end(new_end);

    assert_eq!(interval.end(), new_end);
}

#[test]
fn set_end_time() {
    let mut interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    let new_end_time = date_timestamp(2026, 1, 2);
    interval.set_end_time(new_end_time);

    assert_eq!(interval.end_time(), new_end_time);
}

#[test]
fn set_end_inclusivity() {
    let mut interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    interval.set_end_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn opposite() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from_time(time);

    assert_eq!(
        interval.opposite(),
        HalfBoundedToFutureAbsInterval::from_time_incl(time, BoundInclusivity::Exclusive)
    );
}

#[test]
fn to_half_bounded_interval() {
    let hb_to_past = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        hb_to_past.clone().to_half_bounded_interval(),
        HalfBoundedAbsInterval::ToPast(hb_to_past)
    );
}

#[test]
fn to_interval() {
    let hb_to_past = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        hb_to_past.clone().to_interval(),
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::ToPast(hb_to_past))
    );
}

#[test]
fn to_emptiable_interval() {
    let hb_to_future = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

    assert_eq!(
        hb_to_future.clone().to_emptiable_interval(),
        EmptiableAbsInterval::Bound(hb_to_future.to_interval())
    );
}

#[test]
fn openness() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.openness(), Openness::HalfBounded);
}

#[test]
fn relativity() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.relativity(), Relativity::Absolute);
}

#[test]
fn duration() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.duration(), IntervalDuration::Infinite);
}

#[test]
fn opening_direction() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn abs_bound_pair() {
    let end_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from_time(end_time);

    assert_eq!(
        interval.abs_bound_pair(),
        AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(end_time).to_end_bound(),
        )
    );
}

#[test]
fn abs_start() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.abs_start(), AbsStartBound::InfinitePast);
}

#[test]
fn abs_end() {
    let end_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from_time(end_time);

    assert_eq!(interval.abs_end(), AbsFiniteBoundPos::new(end_time).to_end_bound());
}

#[test]
fn emptiable_abs_bound_pair() {
    let end_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from_time(end_time);

    assert_eq!(
        interval.emptiable_abs_bound_pair(),
        AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(end_time).to_end_bound(),
        )
        .to_emptiable()
    );
}

#[test]
fn partial_abs_start() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(interval.partial_abs_start(), Some(AbsStartBound::InfinitePast));
}

#[test]
fn partial_abs_end() {
    let end_time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from_time(end_time);

    assert_eq!(
        interval.partial_abs_end(),
        Some(AbsFiniteBoundPos::new(end_time).to_end_bound()),
    );
}

#[test]
fn is_empty() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert!(!interval.is_empty());
}

#[test]
fn interval_type() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(
        interval.interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn interval_type_with_rel() {
    let interval = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));
    assert_eq!(
        interval.interval_type_with_rel(),
        IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn from_timestamp() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from(time);

    assert_eq!(interval.end_time(), time);
}

#[test]
fn from_timestamp_and_bound_inclusivity() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from((time, BoundInclusivity::Exclusive));

    assert_eq!(interval.end_time(), time);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_finite_bound_pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
    assert_eq!(
        HalfBoundedToPastAbsInterval::from(pos),
        HalfBoundedToPastAbsInterval::new(pos.to_finite_end_bound())
    );
}

#[test]
fn from_finite_end_bound() {
    let finite_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
    assert_eq!(
        HalfBoundedToPastAbsInterval::from(finite_end),
        HalfBoundedToPastAbsInterval::new(finite_end)
    );
}

#[test]
fn from_range_to() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from(..time);

    assert_eq!(interval.end_time(), time);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_range_to_inclusive() {
    let time = date_timestamp(2026, 1, 1);
    let interval = HalfBoundedToPastAbsInterval::from(..=time);

    assert_eq!(interval.end_time(), time);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn inclusive_inclusive() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();
        let bound_pair = AbsBoundPair::new(start, end);

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(bound_pair),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn inclusive_exclusive() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
        let end =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn inclusive_infinite() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
        let end = AbsEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn exclusive_inclusive() {
        let start =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn exclusive_exclusive() {
        let start =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
        let end =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn exclusive_infinite() {
        let start =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
        let end = AbsEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn infinite_inclusive() {
        let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        let start = AbsStartBound::InfinitePast;
        let end = pos.to_end_bound();

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Ok(HalfBoundedToPastAbsInterval::new(pos.to_finite_end_bound()))
        );
    }

    #[test]
    fn infinite_exclusive() {
        let pos = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
        let start = AbsStartBound::InfinitePast;
        let end = pos.to_end_bound();

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(start, end)),
            Ok(HalfBoundedToPastAbsInterval::new(pos.to_finite_end_bound()))
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(
                BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2)).to_interval()
            ),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(hb_to_future.clone().to_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(
                HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1)).to_interval()
            ),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(UnboundedInterval.to_abs_interval()),
            Err(HalfBoundedToPastAbsIntervalTryFromAbsIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(
                BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2))
                    .to_emptiable_interval()
            ),
            Err(HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToPastAbsInterval::from_time(date_timestamp(2026, 1, 1));

        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(hb_to_future.clone().to_emptiable_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(
                HalfBoundedToFutureAbsInterval::from_time(date_timestamp(2026, 1, 1)).to_emptiable_interval()
            ),
            Err(HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(UnboundedInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedToPastAbsInterval::try_from(EmptyInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedToPastAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }
}

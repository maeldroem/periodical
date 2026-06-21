use std::ops::Bound;

use jiff::SignedDuration;

use super::half_bounded_to_future_interval::*;
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
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HalfBoundedToPastRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn new() {
    let _ = HalfBoundedToFutureRelInterval::new(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
    );
}

#[test]
fn from_offset() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from_offset(offset);

    assert_eq!(interval.start_offset(), offset);
}

#[test]
fn from_offset_incl() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);

    assert_eq!(interval.start_offset(), offset);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from_range(
                SignedDuration::from_hours(1)..=SignedDuration::from_hours(2)
            ),
            Err(HalfBoundedToFutureRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_excluded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from_range(
                SignedDuration::from_hours(1)..SignedDuration::from_hours(2)
            ),
            Err(HalfBoundedToFutureRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_unbounded() {
        let offset = SignedDuration::from_hours(1);
        let interval = HalfBoundedToFutureRelInterval::try_from_range(offset..).unwrap();

        assert_eq!(interval.start_offset(), offset);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn excluded_included() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from_range((
                Bound::Excluded(SignedDuration::from_hours(1)),
                Bound::Included(SignedDuration::from_hours(2))
            )),
            Err(HalfBoundedToFutureRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_excluded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from_range((
                Bound::Excluded(SignedDuration::from_hours(1)),
                Bound::Excluded(SignedDuration::from_hours(2))
            )),
            Err(HalfBoundedToFutureRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_unbounded() {
        let offset = SignedDuration::from_hours(1);
        let interval =
            HalfBoundedToFutureRelInterval::try_from_range((Bound::Excluded(offset), Bound::Unbounded)).unwrap();

        assert_eq!(interval.start_offset(), offset);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn unbounded_included() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from_range(..=SignedDuration::from_hours(1)),
            Err(HalfBoundedToFutureRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_excluded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from_range(..SignedDuration::from_hours(1)),
            Err(HalfBoundedToFutureRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from_range(..),
            Err(HalfBoundedToFutureRelIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    assert_eq!(HalfBoundedToFutureRelInterval::new(start).start(), start);
}

#[test]
fn end() {
    assert_eq!(
        HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1)).end(),
        RelEndBound::InfiniteFuture
    );
}

#[test]
fn start_offset() {
    let offset = SignedDuration::from_hours(1);
    assert_eq!(
        HalfBoundedToFutureRelInterval::from_offset(offset).start_offset(),
        offset
    );
}

#[test]
fn start_inclusivity() {
    assert_eq!(
        HalfBoundedToFutureRelInterval::from_offset_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .start_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn start_mut() {
    let mut interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    let _ = interval.start_mut();
}

#[test]
fn set_start() {
    let mut interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    let new_start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
        .to_finite_start_bound();
    interval.set_start(new_start);

    assert_eq!(interval.start(), new_start);
}

#[test]
fn set_start_offset() {
    let mut interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    let new_start_offset = SignedDuration::from_hours(2);
    interval.set_start_offset(new_start_offset);

    assert_eq!(interval.start_offset(), new_start_offset);
}

#[test]
fn set_start_inclusivity() {
    let mut interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    interval.set_start_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn opposite() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from_offset(offset);

    assert_eq!(
        interval.opposite(),
        HalfBoundedToPastRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive)
    );
}

#[test]
fn to_half_bounded_interval() {
    let hb_to_future = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        hb_to_future.clone().to_half_bounded_interval(),
        HalfBoundedRelInterval::ToFuture(hb_to_future)
    );
}

#[test]
fn to_interval() {
    let hb_to_future = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        hb_to_future.clone().to_interval(),
        RelInterval::HalfBounded(HalfBoundedRelInterval::ToFuture(hb_to_future))
    );
}

#[test]
fn to_emptiable_interval() {
    let hb_to_future = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        hb_to_future.clone().to_emptiable_interval(),
        EmptiableRelInterval::Bound(hb_to_future.to_interval())
    );
}

#[test]
fn openness() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.openness(), Openness::HalfBounded);
}

#[test]
fn relativity() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.relativity(), Relativity::Relative);
}

#[test]
fn duration() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.duration(), IntervalDuration::Infinite);
}

#[test]
fn opening_direction() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn rel_bound_pair() {
    let start_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from_offset(start_offset);

    assert_eq!(
        interval.rel_bound_pair(),
        RelBoundPair::new(
            RelFiniteBoundPos::new(start_offset).to_start_bound(),
            RelEndBound::InfiniteFuture
        )
    );
}

#[test]
fn rel_start() {
    let start_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from_offset(start_offset);

    assert_eq!(
        interval.rel_start(),
        RelFiniteBoundPos::new(start_offset).to_start_bound(),
    );
}

#[test]
fn rel_end() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.rel_end(), RelEndBound::InfiniteFuture);
}

#[test]
fn emptiable_rel_bound_pair() {
    let start_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from_offset(start_offset);

    assert_eq!(
        interval.emptiable_rel_bound_pair(),
        RelBoundPair::new(
            RelFiniteBoundPos::new(start_offset).to_start_bound(),
            RelEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

#[test]
fn partial_rel_start() {
    let start_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from_offset(start_offset);

    assert_eq!(
        interval.partial_rel_start(),
        Some(RelFiniteBoundPos::new(start_offset).to_start_bound()),
    );
}

#[test]
fn partial_rel_end() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.partial_rel_end(), Some(RelEndBound::InfiniteFuture));
}

#[test]
fn is_empty() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert!(!interval.is_empty());
}

#[test]
fn interval_type() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(
        interval.interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToFuture)
    );
}

#[test]
fn interval_type_with_rel() {
    let interval = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(
        interval.interval_type_with_rel(),
        IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture)
    );
}

#[test]
fn from_impl_offset() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from(offset);

    assert_eq!(interval.start_offset(), offset);
}

#[test]
fn from_offset_and_bound_inclusivity() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToFutureRelInterval::from((offset, BoundInclusivity::Exclusive));

    assert_eq!(interval.start_offset(), offset);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_finite_bound_pos() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
    assert_eq!(
        HalfBoundedToFutureRelInterval::from(pos),
        HalfBoundedToFutureRelInterval::new(pos.to_finite_start_bound())
    );
}

#[test]
fn from_finite_start_bound() {
    let finite_start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    assert_eq!(
        HalfBoundedToFutureRelInterval::from(finite_start),
        HalfBoundedToFutureRelInterval::new(finite_start)
    );
}

#[test]
fn from_range_from() {
    let offset = SignedDuration::from_hours(1);
    assert_eq!(
        HalfBoundedToFutureRelInterval::from(offset..),
        HalfBoundedToFutureRelInterval::from_offset(offset)
    );
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn inclusive_inclusive() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();
        let bound_pair = RelBoundPair::new(start, end);

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(bound_pair),
            Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn inclusive_exclusive() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
        let end =
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn inclusive_infinite() {
        let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        let start = pos.to_start_bound();
        let end = RelEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(start, end)),
            Ok(HalfBoundedToFutureRelInterval::new(pos.to_finite_start_bound()))
        );
    }

    #[test]
    fn exclusive_inclusive() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn exclusive_exclusive() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
        let end =
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn exclusive_infinite() {
        let pos = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
        let start = pos.to_start_bound();
        let end = RelEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(start, end)),
            Ok(HalfBoundedToFutureRelInterval::new(pos.to_finite_start_bound()))
        );
    }

    #[test]
    fn infinite_inclusive() {
        let start = RelStartBound::InfinitePast;
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn infinite_exclusive() {
        let start = RelStartBound::InfinitePast;
        let end =
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelEndBound::InfiniteFuture
            )),
            Err(HalfBoundedToFutureRelIntervalTryFromRelBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(
                BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2))
                    .to_interval()
            ),
            Err(HalfBoundedToFutureRelIntervalTryFromRelIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(hb_to_future.clone().to_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(
                HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1)).to_interval()
            ),
            Err(HalfBoundedToFutureRelIntervalTryFromRelIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(UnboundedInterval.to_rel_interval()),
            Err(HalfBoundedToFutureRelIntervalTryFromRelIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(
                BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2))
                    .to_emptiable_interval()
            ),
            Err(HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(hb_to_future.clone().to_emptiable_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(
                HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1)).to_emptiable_interval()
            ),
            Err(HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(UnboundedInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedToFutureRelInterval::try_from(EmptyInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedToFutureRelIntervalTryFromEmptiableRelIntervalError)
        );
    }
}

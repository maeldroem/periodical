use std::ops::Bound;

use jiff::SignedDuration;

use super::half_bounded_to_past_interval::*;
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
    HalfBoundedToFutureRelInterval,
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
    let _ =
        HalfBoundedToPastRelInterval::new(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound());
}

#[test]
fn from_offset() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from_offset(offset);

    assert_eq!(interval.end_offset(), offset);
}

#[test]
fn from_offset_incl() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive);

    assert_eq!(interval.end_offset(), offset);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from_range(SignedDuration::from_hours(1)..=SignedDuration::from_hours(2)),
            Err(HalfBoundedToPastRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_excluded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from_range(SignedDuration::from_hours(1)..SignedDuration::from_hours(2)),
            Err(HalfBoundedToPastRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_unbounded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from_range(SignedDuration::from_hours(1)..),
            Err(HalfBoundedToPastRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_included() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from_range((
                Bound::Excluded(SignedDuration::from_hours(1)),
                Bound::Included(SignedDuration::from_hours(2))
            )),
            Err(HalfBoundedToPastRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_excluded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from_range((
                Bound::Excluded(SignedDuration::from_hours(1)),
                Bound::Excluded(SignedDuration::from_hours(2))
            )),
            Err(HalfBoundedToPastRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_unbounded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from_range((
                Bound::Excluded(SignedDuration::from_hours(1)),
                Bound::Unbounded
            )),
            Err(HalfBoundedToPastRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_included() {
        let offset = SignedDuration::from_hours(1);
        let interval = HalfBoundedToPastRelInterval::try_from_range(..=offset).unwrap();

        assert_eq!(interval.end_offset(), offset);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn unbounded_excluded() {
        let offset = SignedDuration::from_hours(1);
        let interval = HalfBoundedToPastRelInterval::try_from_range(..offset).unwrap();

        assert_eq!(interval.end_offset(), offset);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from_range(..),
            Err(HalfBoundedToPastRelIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() {
    assert_eq!(
        HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1)).start(),
        RelStartBound::InfinitePast
    );
}

#[test]
fn end() {
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
    assert_eq!(HalfBoundedToPastRelInterval::new(end).end(), end);
}

#[test]
fn end_offset() {
    let offset = SignedDuration::from_hours(1);
    assert_eq!(HalfBoundedToPastRelInterval::from_offset(offset).end_offset(), offset);
}

#[test]
fn end_inclusivity() {
    assert_eq!(
        HalfBoundedToPastRelInterval::from_offset_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .end_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn end_mut() {
    let mut interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    let _ = interval.end_mut();
}

#[test]
fn set_end() {
    let mut interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    let new_end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
        .to_finite_end_bound();
    interval.set_end(new_end);

    assert_eq!(interval.end(), new_end);
}

#[test]
fn set_end_offset() {
    let mut interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    let new_end_offset = SignedDuration::from_hours(2);
    interval.set_end_offset(new_end_offset);

    assert_eq!(interval.end_offset(), new_end_offset);
}

#[test]
fn set_end_inclusivity() {
    let mut interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    interval.set_end_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn opposite() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from_offset(offset);

    assert_eq!(
        interval.opposite(),
        HalfBoundedToFutureRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive)
    );
}

#[test]
fn to_half_bounded_interval() {
    let hb_to_past = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        hb_to_past.clone().to_half_bounded_interval(),
        HalfBoundedRelInterval::ToPast(hb_to_past)
    );
}

#[test]
fn to_interval() {
    let hb_to_past = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        hb_to_past.clone().to_interval(),
        RelInterval::HalfBounded(HalfBoundedRelInterval::ToPast(hb_to_past))
    );
}

#[test]
fn to_emptiable_interval() {
    let hb_to_future = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        hb_to_future.clone().to_emptiable_interval(),
        EmptiableRelInterval::Bound(hb_to_future.to_interval())
    );
}

#[test]
fn openness() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.openness(), Openness::HalfBounded);
}

#[test]
fn relativity() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.relativity(), Relativity::Relative);
}

#[test]
fn duration() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.duration(), IntervalDuration::Infinite);
}

#[test]
fn opening_direction() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn rel_bound_pair() {
    let end_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from_offset(end_offset);

    assert_eq!(
        interval.rel_bound_pair(),
        RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(end_offset).to_end_bound(),
        )
    );
}

#[test]
fn rel_start() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.rel_start(), RelStartBound::InfinitePast);
}

#[test]
fn rel_end() {
    let end_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from_offset(end_offset);

    assert_eq!(interval.rel_end(), RelFiniteBoundPos::new(end_offset).to_end_bound());
}

#[test]
fn emptiable_rel_bound_pair() {
    let end_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from_offset(end_offset);

    assert_eq!(
        interval.emptiable_rel_bound_pair(),
        RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(end_offset).to_end_bound(),
        )
        .to_emptiable()
    );
}

#[test]
fn partial_rel_start() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(interval.partial_rel_start(), Some(RelStartBound::InfinitePast));
}

#[test]
fn partial_rel_end() {
    let end_offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from_offset(end_offset);

    assert_eq!(
        interval.partial_rel_end(),
        Some(RelFiniteBoundPos::new(end_offset).to_end_bound()),
    );
}

#[test]
fn is_empty() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert!(!interval.is_empty());
}

#[test]
fn interval_type() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(
        interval.interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn interval_type_with_rel() {
    let interval = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));
    assert_eq!(
        interval.interval_type_with_rel(),
        IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn from_impl_offset() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from(offset);

    assert_eq!(interval.end_offset(), offset);
}

#[test]
fn from_offset_and_bound_inclusivity() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from((offset, BoundInclusivity::Exclusive));

    assert_eq!(interval.end_offset(), offset);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_finite_bound_pos() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
    assert_eq!(
        HalfBoundedToPastRelInterval::from(pos),
        HalfBoundedToPastRelInterval::new(pos.to_finite_end_bound())
    );
}

#[test]
fn from_finite_end_bound() {
    let finite_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
    assert_eq!(
        HalfBoundedToPastRelInterval::from(finite_end),
        HalfBoundedToPastRelInterval::new(finite_end)
    );
}

#[test]
fn from_range_to() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from(..offset);

    assert_eq!(interval.end_offset(), offset);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_range_to_inclusive() {
    let offset = SignedDuration::from_hours(1);
    let interval = HalfBoundedToPastRelInterval::from(..=offset);

    assert_eq!(interval.end_offset(), offset);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn inclusive_inclusive() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();
        let bound_pair = RelBoundPair::new(start, end);

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(bound_pair),
            Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn inclusive_exclusive() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
        let end =
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn inclusive_infinite() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
        let end = RelEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn exclusive_inclusive() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn exclusive_exclusive() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
        let end =
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound();

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn exclusive_infinite() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
        let end = RelEndBound::InfiniteFuture;

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(start, end)),
            Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn infinite_inclusive() {
        let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        let start = RelStartBound::InfinitePast;
        let end = pos.to_end_bound();

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(start, end)),
            Ok(HalfBoundedToPastRelInterval::new(pos.to_finite_end_bound()))
        );
    }

    #[test]
    fn infinite_exclusive() {
        let pos = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
        let start = RelStartBound::InfinitePast;
        let end = pos.to_end_bound();

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(start, end)),
            Ok(HalfBoundedToPastRelInterval::new(pos.to_finite_end_bound()))
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelEndBound::InfiniteFuture
            )),
            Err(HalfBoundedToPastRelIntervalTryFromRelBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(
                BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2))
                    .to_interval()
            ),
            Err(HalfBoundedToPastRelIntervalTryFromRelIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(hb_to_future.clone().to_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(
                HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1)).to_interval()
            ),
            Err(HalfBoundedToPastRelIntervalTryFromRelIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(UnboundedInterval.to_rel_interval()),
            Err(HalfBoundedToPastRelIntervalTryFromRelIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(
                BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2))
                    .to_emptiable_interval()
            ),
            Err(HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        let hb_to_future = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(hb_to_future.clone().to_emptiable_interval()),
            Ok(hb_to_future)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(
                HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1)).to_emptiable_interval()
            ),
            Err(HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(UnboundedInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedToPastRelInterval::try_from(EmptyInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedToPastRelIntervalTryFromEmptiableRelIntervalError)
        );
    }
}

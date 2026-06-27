use std::ops::Bound;

use jiff::SignedDuration;

use super::half_bounded_interval::*;
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
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedToFutureRelInterval,
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

mod new {
    use super::*;

    #[test]
    fn to_future() {
        let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        assert_eq!(
            HalfBoundedRelInterval::new(pos, OpeningDirection::ToFuture),
            HalfBoundedToFutureRelInterval::new(pos.to_finite_start_bound()).to_half_bounded_interval()
        );
    }

    #[test]
    fn to_past() {
        let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        assert_eq!(
            HalfBoundedRelInterval::new(pos, OpeningDirection::ToPast),
            HalfBoundedToPastRelInterval::new(pos.to_finite_end_bound()).to_half_bounded_interval()
        );
    }
}

mod from_offset {
    use super::*;

    #[test]
    fn to_future() {
        let offset = SignedDuration::from_hours(1);
        assert_eq!(
            HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToFuture),
            HalfBoundedToFutureRelInterval::from_offset(offset).to_half_bounded_interval()
        );
    }

    #[test]
    fn to_past() {
        let offset = SignedDuration::from_hours(1);
        assert_eq!(
            HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToPast),
            HalfBoundedToPastRelInterval::from_offset(offset).to_half_bounded_interval()
        );
    }
}

mod from_offset_incl {
    use super::*;

    #[test]
    fn to_future() {
        let offset = SignedDuration::from_hours(1);
        assert_eq!(
            HalfBoundedRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive, OpeningDirection::ToFuture),
            HalfBoundedToFutureRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive)
                .to_half_bounded_interval()
        );
    }

    #[test]
    fn to_past() {
        let offset = SignedDuration::from_hours(1);
        assert_eq!(
            HalfBoundedRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive, OpeningDirection::ToPast),
            HalfBoundedToPastRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive)
                .to_half_bounded_interval()
        );
    }
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range(start..=end),
            Err(HalfBoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range(start..end),
            Err(HalfBoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range(start..),
            Ok(HalfBoundedRelInterval::from_offset(start, OpeningDirection::ToFuture))
        );
    }

    #[test]
    fn excluded_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Err(HalfBoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Err(HalfBoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Ok(HalfBoundedRelInterval::from_offset_incl(
                start,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture
            ))
        );
    }

    #[test]
    fn unbounded_included() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range(..=end),
            Ok(HalfBoundedRelInterval::from_offset(end, OpeningDirection::ToPast))
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range(..end),
            Ok(HalfBoundedRelInterval::from_offset_incl(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            HalfBoundedRelInterval::try_from_range(..),
            Err(HalfBoundedRelIntervalTryFromRangeError)
        );
    }
}

mod reference {
    use super::*;

    #[test]
    fn to_future() {
        let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        assert_eq!(
            HalfBoundedRelInterval::new(pos, OpeningDirection::ToFuture).reference(),
            pos.to_finite_start_bound().to_finite_bound(),
        );
    }

    #[test]
    fn to_past() {
        let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        assert_eq!(
            HalfBoundedRelInterval::new(pos, OpeningDirection::ToPast).reference(),
            pos.to_finite_end_bound().to_finite_bound(),
        );
    }
}

#[test]
fn reference_pos() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    assert_eq!(
        HalfBoundedRelInterval::new(pos, OpeningDirection::ToFuture).reference_pos(),
        pos
    );
}

#[test]
fn reference_offset() {
    let offset = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToFuture).reference_offset(),
        offset
    );
}

#[test]
fn reference_inclusivity() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset_incl(
            SignedDuration::from_hours(1),
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
        let mut interval =
            HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        let new_reference = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
            .to_finite_start_bound()
            .to_finite_bound();
        interval.set_reference(new_reference);

        assert_eq!(interval.reference(), new_reference);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_future_set_finite_bound_end() {
        let mut interval =
            HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        let new_reference = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
            .to_finite_end_bound()
            .to_finite_bound();
        interval.set_reference(new_reference);

        assert_eq!(interval.reference(), new_reference);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }

    #[test]
    fn to_past_set_finite_bound_start() {
        let mut interval = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast);

        let new_reference = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
            .to_finite_start_bound()
            .to_finite_bound();
        interval.set_reference(new_reference);

        assert_eq!(interval.reference(), new_reference);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past_set_finite_bound_end() {
        let mut interval = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast);

        let new_reference = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
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
        let mut interval =
            HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        let new_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(2));
        interval.set_reference_pos(new_pos);

        assert_eq!(interval.reference_pos(), new_pos);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past() {
        let mut interval = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast);

        let new_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(2));
        interval.set_reference_pos(new_pos);

        assert_eq!(interval.reference_pos(), new_pos);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }
}

mod set_reference_offset {
    use super::*;

    #[test]
    fn to_future() {
        let mut interval =
            HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        let new_offset = SignedDuration::from_hours(2);
        interval.set_reference_offset(new_offset);

        assert_eq!(interval.reference_offset(), new_offset);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past() {
        let mut interval = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast);

        let new_offset = SignedDuration::from_hours(2);
        interval.set_reference_offset(new_offset);

        assert_eq!(interval.reference_offset(), new_offset);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    }
}

mod set_reference_inclusivity {
    use super::*;

    #[test]
    fn to_future() {
        let offset = SignedDuration::from_hours(1);
        let mut interval = HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToFuture);

        interval.set_reference_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.reference_offset(), offset);
        assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    }

    #[test]
    fn to_past() {
        let offset = SignedDuration::from_hours(1);
        let mut interval = HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToPast);

        interval.set_reference_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.reference_offset(), offset);
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
            let pos = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedRelInterval::new(pos, OpeningDirection::ToFuture);

            interval.set_opening_direction(OpeningDirection::ToFuture);

            assert_eq!(interval.reference_pos(), pos);
            assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
        }

        #[test]
        fn to_to_past() {
            let pos = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedRelInterval::new(pos, OpeningDirection::ToFuture);

            interval.set_opening_direction(OpeningDirection::ToPast);

            assert_eq!(interval.reference_pos(), pos);
            assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
        }
    }

    mod from_to_past {
        use super::*;

        #[test]
        fn to_to_future() {
            let pos = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedRelInterval::new(pos, OpeningDirection::ToPast);

            interval.set_opening_direction(OpeningDirection::ToFuture);

            assert_eq!(interval.reference_pos(), pos);
            assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
        }

        #[test]
        fn to_to_past() {
            let pos = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
            let mut interval = HalfBoundedRelInterval::new(pos, OpeningDirection::ToPast);

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
        let offset = SignedDuration::from_hours(1);
        assert_eq!(
            HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToFuture).opposite(),
            HalfBoundedRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive, OpeningDirection::ToPast)
        );
    }

    #[test]
    fn from_to_past() {
        let offset = SignedDuration::from_hours(1);
        assert_eq!(
            HalfBoundedRelInterval::from_offset(offset, OpeningDirection::ToPast).opposite(),
            HalfBoundedRelInterval::from_offset_incl(offset, BoundInclusivity::Exclusive, OpeningDirection::ToFuture)
        );
    }
}

#[test]
fn half_bounded_to_future() {
    let hb_to_future = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        hb_to_future.clone().to_half_bounded_interval().half_bounded_to_future(),
        Some(hb_to_future)
    );
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            .half_bounded_to_future(),
        None
    );
}

#[test]
fn half_bounded_to_past() {
    let hb_to_past = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
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
    let half_bounded = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_interval(),
        RelInterval::HalfBounded(half_bounded)
    );
}

#[test]
fn to_emptiable_interval() {
    let half_bounded = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_emptiable_interval(),
        EmptiableRelInterval::Bound(RelInterval::HalfBounded(half_bounded))
    );
}

#[test]
fn opening_direction() {
    let to_future = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);
    let to_past = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast);

    assert_eq!(to_future.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(to_past.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn openness() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).openness(),
        Openness::HalfBounded
    );
}

#[test]
fn relativity() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).relativity(),
        Relativity::Relative
    );
}

#[test]
fn duration() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).duration(),
        IntervalDuration::Infinite
    );
}

#[test]
fn rel_bound_pair() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).rel_bound_pair(),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture
        )
    );
}

#[test]
fn rel_start() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToFuture).rel_start(),
        RelFiniteBoundPos::new(reference).to_start_bound()
    );
    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToPast).rel_start(),
        RelStartBound::InfinitePast
    );
}

#[test]
fn rel_end() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToFuture).rel_end(),
        RelEndBound::InfiniteFuture
    );
    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToPast).rel_end(),
        RelFiniteBoundPos::new(reference).to_end_bound()
    );
}

#[test]
fn emptiable_rel_bound_pair() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            .emptiable_rel_bound_pair(),
        EmptiableRelBoundPair::Bound(RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture
        ))
    );
}

#[test]
fn partial_rel_start() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToFuture).partial_rel_start(),
        Some(RelFiniteBoundPos::new(reference).to_start_bound())
    );
    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToPast).partial_rel_start(),
        Some(RelStartBound::InfinitePast)
    );
}

#[test]
fn partial_rel_end() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToFuture).partial_rel_end(),
        Some(RelEndBound::InfiniteFuture)
    );
    assert_eq!(
        HalfBoundedRelInterval::from_offset(reference, OpeningDirection::ToPast).partial_rel_end(),
        Some(RelFiniteBoundPos::new(reference).to_end_bound())
    );
}

#[test]
fn is_empty() {
    assert!(!HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).is_empty());
    assert!(!HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast).is_empty());
}

#[test]
fn interval_type() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToFuture)
    );
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast).interval_type(),
        IntervalType::HalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn interval_type_with_rel() {
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            .interval_type_with_rel(),
        IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture)
    );
    assert_eq!(
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            .interval_type_with_rel(),
        IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast)
    );
}

#[test]
fn from_offset_opening_direction_pair() {
    assert_eq!(
        HalfBoundedRelInterval::from((SignedDuration::from_hours(1), OpeningDirection::ToFuture)),
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_offset_inclusivity_opening_direction_triple() {
    assert_eq!(
        HalfBoundedRelInterval::from((
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast
        )),
        HalfBoundedRelInterval::from_offset_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn from_finite_bound_pos_and_opening_direction() {
    let pos = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
    assert_eq!(
        HalfBoundedRelInterval::from((pos, OpeningDirection::ToFuture)),
        HalfBoundedRelInterval::new(pos, OpeningDirection::ToFuture)
    );
    assert_eq!(
        HalfBoundedRelInterval::from((pos, OpeningDirection::ToPast)),
        HalfBoundedRelInterval::new(pos, OpeningDirection::ToPast)
    );
}

#[test]
fn from_range_from() {
    assert_eq!(
        HalfBoundedRelInterval::from(SignedDuration::from_hours(1)..),
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_range_to() {
    assert_eq!(
        HalfBoundedRelInterval::from(..SignedDuration::from_hours(1)),
        HalfBoundedRelInterval::from_offset_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn from_range_to_inclusive() {
    assert_eq!(
        HalfBoundedRelInterval::from(..=SignedDuration::from_hours(1)),
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast),
    );
}

#[test]
fn from_half_bounded_to_future() {
    let hb_to_future = HalfBoundedToFutureRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        HalfBoundedRelInterval::from(hb_to_future.clone()),
        HalfBoundedRelInterval::ToFuture(hb_to_future)
    );
}

#[test]
fn from_half_bounded_to_past() {
    let hb_to_past = HalfBoundedToPastRelInterval::from_offset(SignedDuration::from_hours(1));

    assert_eq!(
        HalfBoundedRelInterval::from(hb_to_past.clone()),
        HalfBoundedRelInterval::ToPast(hb_to_past)
    );
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() {
        assert_eq!(
            HalfBoundedRelInterval::try_from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            Err(HalfBoundedRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn finite_infinite() {
        assert_eq!(
            HalfBoundedRelInterval::try_from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture
            )),
            Ok(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
        );
    }

    #[test]
    fn infinite_finite() {
        assert_eq!(
            HalfBoundedRelInterval::try_from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            Ok(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedRelInterval::try_from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelEndBound::InfiniteFuture
            )),
            Err(HalfBoundedRelIntervalTryFromRelBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            HalfBoundedRelInterval::try_from(bounded.to_interval()),
            Err(HalfBoundedRelIntervalTryFromRelIntervalError)
        );
    }

    #[test]
    fn half_bounded() {
        let half_bounded =
            HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedRelInterval::try_from(half_bounded.clone().to_interval()),
            Ok(half_bounded)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedRelInterval::try_from(UnboundedInterval.to_rel_interval()),
            Err(HalfBoundedRelIntervalTryFromRelIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() {
        let bounded = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            HalfBoundedRelInterval::try_from(bounded.to_emptiable_interval()),
            Err(HalfBoundedRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn bound_half_bounded() {
        let half_bounded =
            HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedRelInterval::try_from(half_bounded.clone().to_emptiable_interval()),
            Ok(half_bounded)
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            HalfBoundedRelInterval::try_from(UnboundedInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedRelInterval::try_from(EmptyInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedRelIntervalTryFromEmptiableRelIntervalError)
        );
    }
}

use std::ops::Bound;

use jiff::SignedDuration;

use super::half_bounded_interval::*;
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    HasDuration,
    HasOpeningDirection,
    HasOpenness,
    HasRelativity,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
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
    let interval = HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(interval.reference_offset(), SignedDuration::from_hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let interval = HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.reference_offset(), SignedDuration::from_hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
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
            Ok(HalfBoundedRelInterval::new_from_offset(
                start,
                OpeningDirection::ToFuture
            ))
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
            Ok(HalfBoundedRelInterval::new_from_offset_and_inclusivity(
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
            Ok(HalfBoundedRelInterval::new_from_offset(end, OpeningDirection::ToPast))
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelInterval::try_from_range(..end),
            Ok(HalfBoundedRelInterval::new_from_offset_and_inclusivity(
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

#[test]
fn reference() {
    let reference = SignedDuration::from_hours(1);
    let interval = HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToFuture);

    assert_eq!(interval.reference_offset(), reference);
}

#[test]
fn opening_direction() {
    let to_future = HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);
    let to_past = HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast);

    assert_eq!(to_future.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(to_past.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn reference_inclusivity() {
    let interval = HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn set_reference() {
    let mut interval = HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_offset(SignedDuration::from_hours(2));

    assert_eq!(
        interval,
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn set_reference_inclusivity() {
    let mut interval = HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn set_opening_direction() {
    let mut interval = HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );
}

#[test]
fn to_interval() {
    let half_bounded =
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_interval(),
        RelInterval::HalfBounded(half_bounded)
    );
}

#[test]
fn to_emptiable_interval() {
    let half_bounded =
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_emptiable_interval(),
        EmptiableRelInterval::Bound(RelInterval::HalfBounded(half_bounded))
    );
}

#[test]
fn openness() {
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).openness(),
        Openness::HalfBounded
    );
}

#[test]
fn relativity() {
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).relativity(),
        Relativity::Rel
    );
}

#[test]
fn duration() {
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).duration(),
        IntervalDuration::Infinite
    );
}

#[test]
fn rel_bound_pair() {
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            .rel_bound_pair(),
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
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToFuture).rel_start(),
        RelFiniteBoundPos::new(reference).to_start_bound()
    );
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToPast).rel_start(),
        RelStartBound::InfinitePast
    );
}

#[test]
fn rel_end() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToFuture).rel_end(),
        RelEndBound::InfiniteFuture
    );
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToPast).rel_end(),
        RelFiniteBoundPos::new(reference).to_end_bound()
    );
}

#[test]
fn emptiable_rel_bound_pair() {
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
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
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToFuture).partial_rel_start(),
        Some(RelFiniteBoundPos::new(reference).to_start_bound())
    );
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToPast).partial_rel_start(),
        Some(RelStartBound::InfinitePast)
    );
}

#[test]
fn partial_rel_end() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToFuture).partial_rel_end(),
        Some(RelEndBound::InfiniteFuture)
    );
    assert_eq!(
        HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToPast).partial_rel_end(),
        Some(RelFiniteBoundPos::new(reference).to_end_bound())
    );
}

#[test]
fn is_empty() {
    assert!(
        !HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture).is_empty()
    );
}

#[test]
fn from_timestamp_opening_direction_pair() {
    assert_eq!(
        HalfBoundedRelInterval::from((SignedDuration::from_hours(1), OpeningDirection::ToFuture)),
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_timestamp_inclusivity_opening_direction_triple() {
    assert_eq!(
        HalfBoundedRelInterval::from((
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast
        )),
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn from_range_from() {
    assert_eq!(
        HalfBoundedRelInterval::from(SignedDuration::from_hours(1)..),
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_range_to() {
    assert_eq!(
        HalfBoundedRelInterval::from(..SignedDuration::from_hours(1)),
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
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
        HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast),
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
            Ok(HalfBoundedRelInterval::new_from_offset(
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
            Ok(HalfBoundedRelInterval::new_from_offset(
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
            HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

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
            HalfBoundedRelInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

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

use std::ops::Bound;

use jiff::SignedDuration;

use super::half_bounded_interval::*;
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    HasDuration,
    HasOpenness,
    HasRelativity,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn new() {
    let interval = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(interval.reference(), SignedDuration::from_hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.reference(), SignedDuration::from_hours(1));
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
            HalfBoundedRelativeInterval::try_from_range(start..=end),
            Err(HalfBoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from_range(start..end),
            Err(HalfBoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn included_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from_range(start..),
            Ok(HalfBoundedRelativeInterval::new(start, OpeningDirection::ToFuture))
        );
    }

    #[test]
    fn excluded_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Err(HalfBoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Err(HalfBoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
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
            HalfBoundedRelativeInterval::try_from_range(..=end),
            Ok(HalfBoundedRelativeInterval::new(end, OpeningDirection::ToPast))
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from_range(..end),
            Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from_range(..),
            Err(HalfBoundedRelativeIntervalTryFromRangeError)
        );
    }
}

#[test]
fn reference() {
    let reference = SignedDuration::from_hours(1);
    let interval = HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToFuture);

    assert_eq!(interval.reference(), reference);
}

#[test]
fn opening_direction() {
    let to_future = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);
    let to_past = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast);

    assert_eq!(to_future.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(to_past.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn reference_inclusivity() {
    let interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn set_reference() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference(SignedDuration::from_hours(2));

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn set_reference_inclusivity() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn set_opening_direction() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );
}

#[test]
fn to_interval() {
    let half_bounded = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_interval(),
        RelativeInterval::HalfBounded(half_bounded)
    );
}

#[test]
fn to_emptiable_interval() {
    let half_bounded = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_emptiable_interval(),
        EmptiableRelativeInterval::Bound(RelativeInterval::HalfBounded(half_bounded))
    );
}

#[test]
fn openness() {
    assert_eq!(
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture).openness(),
        Openness::HalfBounded
    );
}

#[test]
fn relativity() {
    assert_eq!(
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture).relativity(),
        Relativity::Relative
    );
}

#[test]
fn duration() {
    assert_eq!(
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture).duration(),
        IntervalDuration::Infinite
    );
}

#[test]
fn rel_bound_pair() {
    assert_eq!(
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture).rel_bound_pair(),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture
        )
    );
}

#[test]
fn rel_start() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToFuture).rel_start(),
        RelativeFiniteBoundPosition::new(reference).to_start_bound()
    );
    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToPast).rel_start(),
        RelativeStartBound::InfinitePast
    );
}

#[test]
fn rel_end() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToFuture).rel_end(),
        RelativeEndBound::InfiniteFuture
    );
    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToPast).rel_end(),
        RelativeFiniteBoundPosition::new(reference).to_end_bound()
    );
}

#[test]
fn emptiable_rel_bound_pair() {
    assert_eq!(
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            .emptiable_rel_bound_pair(),
        EmptiableRelativeBoundPair::Bound(RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture
        ))
    );
}

#[test]
fn partial_rel_start() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToFuture).partial_rel_start(),
        Some(RelativeFiniteBoundPosition::new(reference).to_start_bound())
    );
    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToPast).partial_rel_start(),
        Some(RelativeStartBound::InfinitePast)
    );
}

#[test]
fn partial_rel_end() {
    let reference = SignedDuration::from_hours(1);

    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToFuture).partial_rel_end(),
        Some(RelativeEndBound::InfiniteFuture)
    );
    assert_eq!(
        HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToPast).partial_rel_end(),
        Some(RelativeFiniteBoundPosition::new(reference).to_end_bound())
    );
}

#[test]
fn is_empty() {
    assert!(!HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture).is_empty());
}

#[test]
fn from_timestamp_opening_direction_pair() {
    assert_eq!(
        HalfBoundedRelativeInterval::from((SignedDuration::from_hours(1), OpeningDirection::ToFuture)),
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_timestamp_inclusivity_opening_direction_triple() {
    assert_eq!(
        HalfBoundedRelativeInterval::from((
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast
        )),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn from_range_from() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(SignedDuration::from_hours(1)..),
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn from_range_to() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(..SignedDuration::from_hours(1)),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn from_range_to_inclusive() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(..=SignedDuration::from_hours(1)),
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast),
    );
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            Err(HalfBoundedRelativeIntervalTryFromRelativeBoundPairError)
        );
    }

    #[test]
    fn finite_infinite() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )),
            Ok(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
        );
    }

    #[test]
    fn infinite_finite() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            Ok(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::InfiniteFuture
            )),
            Err(HalfBoundedRelativeIntervalTryFromRelativeBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            HalfBoundedRelativeInterval::try_from(bounded.to_interval()),
            Err(HalfBoundedRelativeIntervalTryFromRelativeIntervalError)
        );
    }

    #[test]
    fn half_bounded() {
        let half_bounded = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from(half_bounded.clone().to_interval()),
            Ok(half_bounded)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from(UnboundedInterval.to_rel_interval()),
            Err(HalfBoundedRelativeIntervalTryFromRelativeIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() {
        let bounded = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            HalfBoundedRelativeInterval::try_from(bounded.to_emptiable_interval()),
            Err(HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)
        );
    }

    #[test]
    fn bound_half_bounded() {
        let half_bounded = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedRelativeInterval::try_from(half_bounded.clone().to_emptiable_interval()),
            Ok(half_bounded)
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from(UnboundedInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedRelativeInterval::try_from(EmptyInterval.to_emptiable_rel_interval()),
            Err(HalfBoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)
        );
    }
}

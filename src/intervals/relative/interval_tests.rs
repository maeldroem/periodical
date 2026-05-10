use std::cmp::Ordering;
use std::ops::Bound;
use std::time::Duration;

use jiff::SignedDuration;

use super::interval::*;
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
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
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::UnboundedInterval;

mod from_range {
    use super::*;

    #[test]
    fn included_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelativeInterval::from_range(start..=end),
            RelativeInterval::Bounded(BoundedRelativeInterval::new(start, end))
        );
    }

    #[test]
    fn included_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelativeInterval::from_range(start..end),
            RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Inclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn included_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            RelativeInterval::from_range(start..),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(start, OpeningDirection::ToFuture))
        );
    }

    #[test]
    fn excluded_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelativeInterval::from_range((Bound::Excluded(start), Bound::Included(end))),
            RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Inclusive
            ))
        );
    }

    #[test]
    fn excluded_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelativeInterval::from_range((Bound::Excluded(start), Bound::Excluded(end))),
            RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn excluded_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            RelativeInterval::from_range((Bound::Excluded(start), Bound::Unbounded)),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
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
            RelativeInterval::from_range(..=end),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(end, OpeningDirection::ToPast))
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelativeInterval::from_range(..end),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            RelativeInterval::from_range(..),
            RelativeInterval::Unbounded(UnboundedInterval)
        );
    }
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(2), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_half_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            )),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture,)
            )),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            )),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_unbounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater,
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(2), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture,)
            )),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            )),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            )),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            )),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&RelativeInterval::Bounded(
                BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2))
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval)
                .ord_by_start_and_inv_length(&RelativeInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn bounded() {
    assert_eq!(
        RelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .bounded(),
        Some(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
    );
    assert_eq!(
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
        .bounded(),
        None
    );
    assert_eq!(RelativeInterval::Unbounded(UnboundedInterval).bounded(), None);
}

#[test]
fn half_bounded() {
    assert_eq!(
        RelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .half_bounded(),
        None
    );
    assert_eq!(
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
        .half_bounded(),
        Some(HalfBoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
    );
    assert_eq!(RelativeInterval::Unbounded(UnboundedInterval).half_bounded(), None);
}

#[test]
fn unbounded() {
    assert_eq!(
        RelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        RelativeInterval::Unbounded(UnboundedInterval).unbounded(),
        Some(UnboundedInterval)
    );
}

#[test]
fn to_emptiable() {
    assert_eq!(
        RelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .to_emptiable(),
        EmptiableRelativeInterval::Bound(RelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        )))
    );
}

mod rel_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .rel_bound_pair(),
            RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
            )
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .rel_bound_pair(),
            RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).rel_bound_pair(),
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
        );
    }
}

mod rel_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .rel_start(),
            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .rel_start(),
            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .rel_start(),
            RelativeStartBound::InfinitePast
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).rel_start(),
            RelativeStartBound::InfinitePast
        );
    }
}

mod rel_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .rel_end(),
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .rel_end(),
            RelativeEndBound::InfiniteFuture
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .rel_end(),
            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).rel_end(),
            RelativeEndBound::InfiniteFuture
        );
    }
}

mod emptiable_rel_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .emptiable_rel_bound_pair(),
            RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
            )
            .to_emptiable()
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .emptiable_rel_bound_pair(),
            RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).emptiable_rel_bound_pair(),
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable()
        );
    }
}

mod partial_rel_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .partial_rel_start(),
            Some(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .partial_rel_start(),
            Some(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .partial_rel_start(),
            Some(RelativeStartBound::InfinitePast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).partial_rel_start(),
            Some(RelativeStartBound::InfinitePast)
        );
    }
}

mod partial_rel_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .partial_rel_end(),
            Some(RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .partial_rel_end(),
            Some(RelativeEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .partial_rel_end(),
            Some(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound())
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).partial_rel_end(),
            Some(RelativeEndBound::InfiniteFuture)
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .duration(),
            IntervalDuration::Finite(Duration::from_hours(1), Epsilon::None)
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).duration(),
            IntervalDuration::Infinite
        );
    }
}

mod relativity {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .relativity(),
            Relativity::Relative
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .relativity(),
            Relativity::Relative
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).relativity(),
            Relativity::Any
        );
    }
}

mod openness {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .openness(),
            Openness::Bounded
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .openness(),
            Openness::HalfBounded
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).openness(),
            Openness::Unbounded
        );
    }
}

mod ord {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_half_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_unbounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelativeInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater,
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).cmp(&RelativeInterval::Bounded(
                BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2))
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).cmp(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            )),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).cmp(&RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).cmp(&RelativeInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

mod is_empty {
    use super::*;

    #[test]
    fn bounded() {
        assert!(
            !RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .is_empty()
        );
    }

    #[test]
    fn half_bounded() {
        assert!(
            !RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .is_empty()
        );
    }

    #[test]
    fn unbounded() {
        assert!(!RelativeInterval::Unbounded(UnboundedInterval).is_empty());
    }
}

#[test]
fn from_bounded_interval() {
    let bounded = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
    assert_eq!(
        RelativeInterval::from(bounded.clone()),
        RelativeInterval::Bounded(bounded)
    );
}

#[test]
fn from_half_bounded_interval() {
    let half_bounded = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);
    assert_eq!(
        RelativeInterval::from(half_bounded.clone()),
        RelativeInterval::HalfBounded(half_bounded)
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        RelativeInterval::from(UnboundedInterval),
        RelativeInterval::Unbounded(UnboundedInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::from(RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            )),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::from(RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            )),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
            )),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::InfiniteFuture
            )),
            RelativeInterval::Unbounded(UnboundedInterval)
        );
    }
}

mod try_from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() {
        assert_eq!(
            RelativeInterval::try_from(
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
        );
    }

    #[test]
    fn bound_half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::try_from(
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Ok(RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
        );
    }

    #[test]
    fn bound_half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::try_from(
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            )))
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            RelativeInterval::try_from(
                RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Ok(RelativeInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            RelativeInterval::try_from(EmptiableRelativeBoundPair::Empty),
            Err(RelativeIntervalFromEmptiableRelativeBoundPairError)
        );
    }
}

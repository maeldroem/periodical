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
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelStartBound,
};
use crate::intervals::special::UnboundedInterval;

mod from_range {
    use super::*;

    #[test]
    fn included_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelInterval::from_range(start..=end),
            RelInterval::Bounded(BoundedRelInterval::from_offsets(start, end))
        );
    }

    #[test]
    fn included_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelInterval::from_range(start..end),
            RelInterval::Bounded(BoundedRelInterval::from_offsets_incl(
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
            RelInterval::from_range(start..),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(start, OpeningDirection::ToFuture))
        );
    }

    #[test]
    fn excluded_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelInterval::from_range((Bound::Excluded(start), Bound::Included(end))),
            RelInterval::Bounded(BoundedRelInterval::from_offsets_incl(
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
            RelInterval::from_range((Bound::Excluded(start), Bound::Excluded(end))),
            RelInterval::Bounded(BoundedRelInterval::from_offsets_incl(
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
            RelInterval::from_range((Bound::Excluded(start), Bound::Unbounded)),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset_incl(
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
            RelInterval::from_range(..=end),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(end, OpeningDirection::ToPast))
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            RelInterval::from_range(..end),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset_incl(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(RelInterval::from_range(..), RelInterval::Unbounded(UnboundedInterval));
    }
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_unbounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .ord_by_start_and_inv_length(&RelInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater,
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&RelInterval::Bounded(
                BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2))
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&RelInterval::HalfBounded(
                HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&RelInterval::HalfBounded(
                HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .ord_by_start_and_inv_length(&RelInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn bounded() {
    assert_eq!(
        RelInterval::Bounded(BoundedRelInterval::from_offsets(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .bounded(),
        Some(BoundedRelInterval::from_offsets(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
    );
    assert_eq!(
        RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
        .bounded(),
        None
    );
    assert_eq!(RelInterval::Unbounded(UnboundedInterval).bounded(), None);
}

#[test]
fn half_bounded() {
    assert_eq!(
        RelInterval::Bounded(BoundedRelInterval::from_offsets(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .half_bounded(),
        None
    );
    assert_eq!(
        RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
        .half_bounded(),
        Some(HalfBoundedRelInterval::from_offset(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
    );
    assert_eq!(RelInterval::Unbounded(UnboundedInterval).half_bounded(), None);
}

#[test]
fn unbounded() {
    assert_eq!(
        RelInterval::Bounded(BoundedRelInterval::from_offsets(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        RelInterval::Unbounded(UnboundedInterval).unbounded(),
        Some(UnboundedInterval)
    );
}

#[test]
fn to_emptiable() {
    assert_eq!(
        RelInterval::Bounded(BoundedRelInterval::from_offsets(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        ))
        .to_emptiable(),
        EmptiableRelInterval::Bound(RelInterval::Bounded(BoundedRelInterval::from_offsets(
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
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .rel_bound_pair(),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            )
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .rel_bound_pair(),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture
            )
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).rel_bound_pair(),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture)
        );
    }
}

mod rel_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .rel_start(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .rel_start(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .rel_start(),
            RelStartBound::InfinitePast
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).rel_start(),
            RelStartBound::InfinitePast
        );
    }
}

mod rel_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .rel_end(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .rel_end(),
            RelEndBound::InfiniteFuture
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .rel_end(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).rel_end(),
            RelEndBound::InfiniteFuture
        );
    }
}

mod emptiable_rel_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .emptiable_rel_bound_pair(),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            )
            .to_emptiable()
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .emptiable_rel_bound_pair(),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).emptiable_rel_bound_pair(),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
        );
    }
}

mod partial_rel_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .partial_rel_start(),
            Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .partial_rel_start(),
            Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .partial_rel_start(),
            Some(RelStartBound::InfinitePast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).partial_rel_start(),
            Some(RelStartBound::InfinitePast)
        );
    }
}

mod partial_rel_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .partial_rel_end(),
            Some(RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .partial_rel_end(),
            Some(RelEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .partial_rel_end(),
            Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound())
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).partial_rel_end(),
            Some(RelEndBound::InfiniteFuture)
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
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
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
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
            RelInterval::Unbounded(UnboundedInterval).duration(),
            IntervalDuration::Infinite
        );
    }
}

mod relativity {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .relativity(),
            Relativity::Rel
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .relativity(),
            Relativity::Rel
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(RelInterval::Unbounded(UnboundedInterval).relativity(), Relativity::Any);
    }
}

mod openness {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
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
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
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
            RelInterval::Unbounded(UnboundedInterval).openness(),
            Openness::Unbounded
        );
    }
}

mod ord {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_unbounded() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .cmp(&RelInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Greater,
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .cmp(&RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).cmp(&RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).cmp(&RelInterval::HalfBounded(
                HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToPast)
            )),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).cmp(&RelInterval::HalfBounded(
                HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            )),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).cmp(&RelInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

mod is_empty {
    use super::*;

    #[test]
    fn bounded() {
        assert!(
            !RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .is_empty()
        );
    }

    #[test]
    fn half_bounded() {
        assert!(
            !RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .is_empty()
        );
    }

    #[test]
    fn unbounded() {
        assert!(!RelInterval::Unbounded(UnboundedInterval).is_empty());
    }
}

#[test]
fn from_bounded_interval() {
    let bounded = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
    assert_eq!(RelInterval::from(bounded.clone()), RelInterval::Bounded(bounded));
}

#[test]
fn from_half_bounded_interval() {
    let half_bounded = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);
    assert_eq!(
        RelInterval::from(half_bounded.clone()),
        RelInterval::HalfBounded(half_bounded)
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        RelInterval::from(UnboundedInterval),
        RelInterval::Unbounded(UnboundedInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelInterval::from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            )),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelInterval::from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture
            )),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            )),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelInterval::from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
            )),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelEndBound::InfiniteFuture
            )),
            RelInterval::Unbounded(UnboundedInterval)
        );
    }
}

mod try_from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() {
        assert_eq!(
            RelInterval::try_from(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))),
        );
    }

    #[test]
    fn bound_half_bounded_to_future() {
        assert_eq!(
            RelInterval::try_from(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Ok(RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))),
        );
    }

    #[test]
    fn bound_half_bounded_to_past() {
        assert_eq!(
            RelInterval::try_from(
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            )))
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            RelInterval::try_from(
                RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
            ),
            Ok(RelInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            RelInterval::try_from(EmptiableRelBoundPair::Empty),
            Err(RelIntervalFromEmptiableRelBoundPairError)
        );
    }
}

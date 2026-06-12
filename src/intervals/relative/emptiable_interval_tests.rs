use std::cmp::Ordering;
use std::time::Duration;

use jiff::SignedDuration;

use super::emptiable_interval::*;
use crate::intervals::meta::{
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
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn from_range() {
    let start = SignedDuration::from_hours(1);

    assert_eq!(
        EmptiableRelInterval::from_range(start..),
        HalfBoundedRelInterval::from_offset(start, OpeningDirection::ToFuture).to_emptiable_interval()
    );
}

#[test]
fn bound() {
    let interval = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        interval.clone().to_emptiable_interval().bound(),
        Some(interval.to_interval())
    );
    assert_eq!(EmptiableRelInterval::Empty(EmptyInterval).bound(), None);
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(2),
                    SignedDuration::from_hours(3)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(3)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2),
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(2),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(&RelInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_empty() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableRelInterval::Empty(EmptyInterval)),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(2),
                    SignedDuration::from_hours(3)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(2),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_empty() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableRelInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                        SignedDuration::from_hours(1),
                        SignedDuration::from_hours(2)
                    ))
                    .to_emptiable()
                ),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                        SignedDuration::from_hours(1),
                        OpeningDirection::ToPast
                    ))
                    .to_emptiable()
                ),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                        SignedDuration::from_hours(1),
                        OpeningDirection::ToFuture
                    ))
                    .to_emptiable()
                ),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&RelInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&EmptiableRelInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn empty_half_bounded() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&RelInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&EmptiableRelInterval::Empty(EmptyInterval)),
            Ordering::Equal
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
            .to_emptiable()
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
            .to_emptiable()
            .duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).to_emptiable().duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).duration(),
            IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
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
            .to_emptiable()
            .relativity(),
            Relativity::Relative
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .relativity(),
            Relativity::Relative
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).to_emptiable().relativity(),
            Relativity::Any
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableRelInterval::Empty(EmptyInterval).relativity(), Relativity::Any);
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
            .to_emptiable()
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
            .to_emptiable()
            .openness(),
            Openness::HalfBounded
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).to_emptiable().openness(),
            Openness::Unbounded
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableRelInterval::Empty(EmptyInterval).openness(), Openness::Empty);
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
            .to_emptiable()
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
            .to_emptiable()
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
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .emptiable_rel_bound_pair(),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).emptiable_rel_bound_pair(),
            EmptiableRelBoundPair::Empty
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
            .to_emptiable()
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
            .to_emptiable()
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
            .to_emptiable()
            .partial_rel_start(),
            Some(RelStartBound::InfinitePast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_rel_start(),
            Some(RelStartBound::InfinitePast)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableRelInterval::Empty(EmptyInterval).partial_rel_start(), None);
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
            .to_emptiable()
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
            .to_emptiable()
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
            .to_emptiable()
            .partial_rel_end(),
            Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound())
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_rel_end(),
            Some(RelEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableRelInterval::Empty(EmptyInterval).partial_rel_end(), None);
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
            .to_emptiable()
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
            .to_emptiable()
            .is_empty()
        );
    }

    #[test]
    fn unbounded() {
        assert!(!RelInterval::Unbounded(UnboundedInterval).to_emptiable().is_empty());
    }

    #[test]
    fn empty() {
        assert!(EmptiableRelInterval::Empty(EmptyInterval).is_empty());
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(2),
                    SignedDuration::from_hours(3)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(3)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2),
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(2),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(&RelInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_empty() {
        assert_eq!(
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(&EmptiableRelInterval::Empty(EmptyInterval)),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(2),
                    SignedDuration::from_hours(3)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(2),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
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
            .to_emptiable()
            .cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_empty() {
        assert_eq!(
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(&EmptiableRelInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_half_bounded_start_greater() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&RelInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            RelInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&EmptiableRelInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).cmp(
                &RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(1),
                    SignedDuration::from_hours(2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn empty_half_bounded() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).cmp(
                &RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                    SignedDuration::from_hours(1),
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).cmp(&RelInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableRelInterval::Empty(EmptyInterval).cmp(&EmptiableRelInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn from_bounded_interval() {
    let bounded = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
    assert_eq!(
        EmptiableRelInterval::from(bounded.clone()),
        RelInterval::Bounded(bounded).to_emptiable()
    );
}

#[test]
fn from_half_bounded_interval() {
    let half_bounded =
        HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);
    assert_eq!(
        EmptiableRelInterval::from(half_bounded.clone()),
        RelInterval::HalfBounded(half_bounded).to_emptiable()
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableRelInterval::from(UnboundedInterval),
        RelInterval::Unbounded(UnboundedInterval).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(
        EmptiableRelInterval::from(EmptyInterval),
        EmptiableRelInterval::Empty(EmptyInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            EmptiableRelInterval::from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            EmptiableRelInterval::from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture
            )),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            EmptiableRelInterval::from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
            )),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            EmptiableRelInterval::from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelEndBound::InfiniteFuture
            )),
            RelInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }
}

mod from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() {
        assert_eq!(
            EmptiableRelInterval::from(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
                )
                .to_emptiable()
            ),
            RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn bound_half_bounded_to_future() {
        assert_eq!(
            EmptiableRelInterval::from(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn bound_half_bounded_to_past() {
        assert_eq!(
            EmptiableRelInterval::from(
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
                )
                .to_emptiable()
            ),
            RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            EmptiableRelInterval::from(
                RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
            ),
            RelInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelInterval::from(EmptiableRelBoundPair::Empty),
            EmptiableRelInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn from_interval() {
    let interval = HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
        .to_interval();

    assert_eq!(
        EmptiableRelInterval::from(interval.clone()),
        EmptiableRelInterval::Bound(interval)
    );
}

#[test]
fn from_unit_val() {
    assert_eq!(
        EmptiableRelInterval::from(()),
        EmptiableRelInterval::Empty(EmptyInterval)
    );
}

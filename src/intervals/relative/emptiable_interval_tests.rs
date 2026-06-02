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
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn from_range() {
    let start = SignedDuration::from_hours(1);

    assert_eq!(
        EmptiableRelativeInterval::from_range(start..),
        HalfBoundedRelativeInterval::new_from_offset(start, OpeningDirection::ToFuture).to_emptiable_interval()
    );
}

#[test]
fn bound() {
    let interval =
        HalfBoundedRelativeInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(
        interval.clone().to_emptiable_interval().bound(),
        Some(interval.to_interval())
    );
    assert_eq!(EmptiableRelativeInterval::Empty(EmptyInterval).bound(), None);
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_empty() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            EmptiableRelativeInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            EmptiableRelativeInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable().duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).duration(),
            IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
        );
    }
}

mod relativity {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .relativity(),
            Relativity::Any
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).relativity(),
            Relativity::Any
        );
    }
}

mod openness {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable().openness(),
            Openness::Unbounded
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).openness(),
            Openness::Empty
        );
    }
}

mod emptiable_rel_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .emptiable_rel_bound_pair(),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
            )
            .to_emptiable()
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .emptiable_rel_bound_pair(),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .emptiable_rel_bound_pair(),
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).emptiable_rel_bound_pair(),
            EmptiableRelativeBoundPair::Empty
        );
    }
}

mod partial_rel_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .partial_rel_start(),
            Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_rel_start(),
            Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_rel_start(),
            Some(RelativeStartBound::InfinitePast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_rel_start(),
            Some(RelativeStartBound::InfinitePast)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).partial_rel_start(),
            None
        );
    }
}

mod partial_rel_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .partial_rel_end(),
            Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_rel_end(),
            Some(RelativeEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_rel_end(),
            Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound())
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_rel_end(),
            Some(RelativeEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableRelativeInterval::Empty(EmptyInterval).partial_rel_end(), None);
    }
}

mod is_empty {
    use super::*;

    #[test]
    fn bounded() {
        assert!(
            !RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            !RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .is_empty()
        );
    }

    #[test]
    fn unbounded() {
        assert!(!RelativeInterval::Unbounded(UnboundedInterval).to_emptiable().is_empty());
    }

    #[test]
    fn empty() {
        assert!(EmptiableRelativeInterval::Empty(EmptyInterval).is_empty());
    }
}

mod ord {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(3)
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(2),
                SignedDuration::from_hours(3),
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2),
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(&RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_empty() {
        assert_eq!(
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable()
            .cmp(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            RelativeInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).cmp(
                &RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
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
            EmptiableRelativeInterval::Empty(EmptyInterval).cmp(
                &RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
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
            EmptiableRelativeInterval::Empty(EmptyInterval)
                .cmp(&RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableRelativeInterval::Empty(EmptyInterval).cmp(&EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn from_bounded_interval() {
    let bounded = BoundedRelativeInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
    assert_eq!(
        EmptiableRelativeInterval::from(bounded.clone()),
        RelativeInterval::Bounded(bounded).to_emptiable()
    );
}

#[test]
fn from_half_bounded_interval() {
    let half_bounded =
        HalfBoundedRelativeInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture);
    assert_eq!(
        EmptiableRelativeInterval::from(half_bounded.clone()),
        RelativeInterval::HalfBounded(half_bounded).to_emptiable()
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableRelativeInterval::from(UnboundedInterval),
        RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(
        EmptiableRelativeInterval::from(EmptyInterval),
        EmptiableRelativeInterval::Empty(EmptyInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            EmptiableRelativeInterval::from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
            )),
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            EmptiableRelativeInterval::from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            EmptiableRelativeInterval::from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound()
            )),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            EmptiableRelativeInterval::from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::InfiniteFuture
            )),
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }
}

mod from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() {
        assert_eq!(
            EmptiableRelativeInterval::from(
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
                )
                .to_emptiable()
            ),
            RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(2)
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn bound_half_bounded_to_future() {
        assert_eq!(
            EmptiableRelativeInterval::from(
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn bound_half_bounded_to_past() {
        assert_eq!(
            EmptiableRelativeInterval::from(
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound()
                )
                .to_emptiable()
            ),
            RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_from_offset(
                SignedDuration::from_hours(1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            EmptiableRelativeInterval::from(
                RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelativeInterval::from(EmptiableRelativeBoundPair::Empty),
            EmptiableRelativeInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn from_interval() {
    let interval =
        HalfBoundedRelativeInterval::new_from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
            .to_interval();

    assert_eq!(
        EmptiableRelativeInterval::from(interval.clone()),
        EmptiableRelativeInterval::Bound(interval)
    );
}

#[test]
fn from_unit_val() {
    assert_eq!(
        EmptiableRelativeInterval::from(()),
        EmptiableRelativeInterval::Empty(EmptyInterval)
    );
}

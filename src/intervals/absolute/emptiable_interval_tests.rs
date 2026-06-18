use std::cmp::Ordering;
use std::time::Duration;

use super::emptiable_interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasIntervalType,
    HasIntervalTypeWithRel,
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
fn from_range() {
    let start = date_timestamp(2026, 1, 1);

    assert_eq!(
        EmptiableAbsInterval::from_range(start..),
        HalfBoundedAbsInterval::from_time(start, OpeningDirection::ToFuture).to_emptiable_interval()
    );
}

#[test]
fn bound() {
    let interval = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);

    assert_eq!(
        interval.clone().to_emptiable_interval().bound(),
        Some(interval.to_interval())
    );
    assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).bound(), None);
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 2),
                    date_timestamp(2026, 1, 3)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 3)
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 3)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2),
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 2),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2),
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_empty() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 2),
                    date_timestamp(2026, 1, 3)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Greater,
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 2),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                        date_timestamp(2026, 1, 1),
                        date_timestamp(2026, 1, 2)
                    ))
                    .to_emptiable()
                ),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                        date_timestamp(2026, 1, 1),
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
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                        date_timestamp(2026, 1, 1),
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
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn empty_half_bounded() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            EmptiableAbsInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .duration(),
            IntervalDuration::Finite(Duration::from_hours(24), Epsilon::None)
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
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
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).duration(),
            IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
        );
    }
}

mod relativity {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .relativity(),
            Relativity::Absolute
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .relativity(),
            Relativity::Absolute
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().relativity(),
            Relativity::Any
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).relativity(), Relativity::Any);
    }
}

mod openness {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .openness(),
            Openness::Bounded
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
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
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().openness(),
            Openness::Unbounded
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).openness(), Openness::Empty);
    }
}

mod emptiable_abs_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .emptiable_abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
            )
            .to_emptiable()
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .emptiable_abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .emptiable_abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).emptiable_abs_bound_pair(),
            EmptiableAbsBoundPair::Empty
        );
    }
}

mod partial_abs_start {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).partial_abs_start(), None);
    }
}

mod partial_abs_end {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),)
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound())
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).partial_abs_end(), None);
    }
}

mod is_empty {
    use super::*;

    #[test]
    fn bounded() {
        assert!(
            !AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .is_empty()
        );
    }

    #[test]
    fn half_bounded() {
        assert!(
            !AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .is_empty()
        );
    }

    #[test]
    fn unbounded() {
        assert!(!AbsInterval::Unbounded(UnboundedInterval).to_emptiable().is_empty());
    }

    #[test]
    fn empty() {
        assert!(EmptiableAbsInterval::Empty(EmptyInterval).is_empty());
    }
}

mod interval_type {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 1))
            .to_emptiable_interval();

        assert_eq!(bounded.interval_type(), IntervalType::Bounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
            .to_emptiable_interval();

        assert_eq!(
            half_bounded.interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast)
            .to_emptiable_interval();

        assert_eq!(
            half_bounded.interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = UnboundedInterval.to_emptiable_abs_interval();

        assert_eq!(unbounded.interval_type(), IntervalType::Unbounded);
    }

    #[test]
    fn empty() {
        let empty = EmptyInterval.to_emptiable_abs_interval();

        assert_eq!(empty.interval_type(), IntervalType::Empty);
    }
}

mod interval_type_with_rel {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 1))
            .to_emptiable_interval();

        assert_eq!(bounded.interval_type_with_rel(), IntervalTypeWithRel::AbsBounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
            .to_emptiable_interval();

        assert_eq!(
            half_bounded.interval_type_with_rel(),
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToPast)
            .to_emptiable_interval();

        assert_eq!(
            half_bounded.interval_type_with_rel(),
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = UnboundedInterval.to_emptiable_abs_interval();

        assert_eq!(unbounded.interval_type_with_rel(), IntervalTypeWithRel::Unbounded);
    }

    #[test]
    fn empty() {
        let empty = EmptyInterval.to_emptiable_abs_interval();

        assert_eq!(empty.interval_type_with_rel(), IntervalTypeWithRel::Empty);
    }
}

mod ord {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 2),
                    date_timestamp(2026, 1, 3)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 3)
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 3)
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2),
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 2),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 2),
                date_timestamp(2026, 1, 3),
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2),
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .cmp(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
    }

    #[test]
    fn bounded_empty() {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable()
            .cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 2),
                    date_timestamp(2026, 1, 3)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn half_bounded_bounded_start_equal() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
    }

    #[test]
    fn half_bounded_bounded_start_greater() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn half_bounded_half_bounded_start_less() {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 2),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 2),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn unbounded_bounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn unbounded_half_bounded_start_equal() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    date_timestamp(2026, 1, 1),
                    date_timestamp(2026, 1, 2)
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
    }

    #[test]
    fn empty_half_bounded() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                    date_timestamp(2026, 1, 1),
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
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn from_bounded_interval() {
    let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
    assert_eq!(
        EmptiableAbsInterval::from(bounded.clone()),
        AbsInterval::Bounded(bounded).to_emptiable()
    );
}

#[test]
fn from_half_bounded_to_future_interval() {
    let half_bounded =
        HalfBoundedToFutureAbsInterval::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound());

    assert_eq!(
        EmptiableAbsInterval::from(half_bounded.clone()),
        EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(HalfBoundedAbsInterval::ToFuture(half_bounded)))
    );
}

#[test]
fn from_half_bounded_to_past_interval() {
    let half_bounded =
        HalfBoundedToPastAbsInterval::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound());

    assert_eq!(
        EmptiableAbsInterval::from(half_bounded.clone()),
        EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(HalfBoundedAbsInterval::ToPast(half_bounded)))
    );
}

#[test]
fn from_half_bounded_interval() {
    let half_bounded = HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture);
    assert_eq!(
        EmptiableAbsInterval::from(half_bounded.clone()),
        AbsInterval::HalfBounded(half_bounded).to_emptiable()
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableAbsInterval::from(UnboundedInterval),
        AbsInterval::Unbounded(UnboundedInterval).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(
        EmptiableAbsInterval::from(EmptyInterval),
        EmptiableAbsInterval::Empty(EmptyInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() {
        assert_eq!(
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
            )),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn half_bounded_to_future() {
        assert_eq!(
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn half_bounded_to_past() {
        assert_eq!(
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound()
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }
}

mod from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() {
        assert_eq!(
            EmptiableAbsInterval::from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
                )
                .to_emptiable()
            ),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                date_timestamp(2026, 1, 1),
                date_timestamp(2026, 1, 2)
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn bound_half_bounded_to_future() {
        assert_eq!(
            EmptiableAbsInterval::from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
    }

    #[test]
    fn bound_half_bounded_to_past() {
        assert_eq!(
            EmptiableAbsInterval::from(
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound()
                )
                .to_emptiable()
            ),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                date_timestamp(2026, 1, 1),
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            EmptiableAbsInterval::from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
            ),
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsInterval::from(EmptiableAbsBoundPair::Empty),
            EmptiableAbsInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn from_interval() {
    let interval =
        HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).to_interval();

    assert_eq!(
        EmptiableAbsInterval::from(interval.clone()),
        EmptiableAbsInterval::Bound(interval)
    );
}

#[test]
fn from_unit_val() {
    assert_eq!(
        EmptiableAbsInterval::from(()),
        EmptiableAbsInterval::Empty(EmptyInterval)
    );
}

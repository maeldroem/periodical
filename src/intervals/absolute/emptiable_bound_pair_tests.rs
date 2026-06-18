use std::cmp::Ordering;
use std::time::Duration;

use jiff::Timestamp;

use super::emptiable_bound_pair::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
};
use crate::intervals::meta::{
    BoundInclusivity,
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
        EmptiableAbsBoundPair::from_range(start..),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(start).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bound_bound_less_start() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_less_start_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_less_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_equal_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableAbsBoundPair::Empty;

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn unbound_bound() {
        let bound_pair1 = EmptiableAbsBoundPair::Empty;
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.ord_by_start_and_inv_length(&EmptiableAbsBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn bound() {
    let bound_pair = AbsBoundPair::new(
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
    );
    let emptiable_bound_pair = bound_pair.clone().to_emptiable();

    assert_eq!(emptiable_bound_pair.bound(), Some(bound_pair));
    assert_eq!(EmptiableAbsBoundPair::Empty.bound(), None);
}

mod to_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();

        assert_eq!(
            AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableAbsInterval::Bound(AbsInterval::Bounded(BoundedAbsInterval::new(start, end)))
        );
    }

    #[test]
    fn half_bounded() {
        let reference = date_timestamp(2026, 1, 1);

        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(reference).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )
            .to_emptiable()
            .to_emptiable_interval(),
            EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                reference,
                OpeningDirection::ToFuture
            )))
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableAbsInterval::Bound(AbsInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.to_emptiable_interval(),
            EmptiableAbsInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn emptiable_abs_bound_pair() {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
        .emptiable_abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
    );
}

#[test]
fn partial_abs_start() {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
        .partial_abs_start(),
        Some(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound()
        )
    );
    assert_eq!(EmptiableAbsBoundPair::Empty.partial_abs_start(), None);
}

#[test]
fn partial_abs_end() {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
        .partial_abs_end(),
        Some(AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound())
    );
    assert_eq!(EmptiableAbsBoundPair::Empty.partial_abs_end(), None);
}

#[test]
fn is_empty() {
    assert!(
        !AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
            .to_emptiable()
            .is_empty()
    );
    assert!(EmptiableAbsBoundPair::Empty.is_empty());
}

#[test]
fn duration() {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
        )
        .to_emptiable()
        .duration(),
        IntervalDuration::Finite(Duration::from_hours(24), Epsilon::None)
    );
    assert_eq!(
        EmptiableAbsBoundPair::Empty.duration(),
        IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
    );
}

#[test]
fn openness() {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
        )
        .to_emptiable()
        .openness(),
        Openness::Bounded
    );
    assert_eq!(EmptiableAbsBoundPair::Empty.openness(), Openness::Empty);
}

#[test]
fn relativity() {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
    )
    .to_emptiable();
    let half_bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
        AbsEndBound::InfiniteFuture,
    )
    .to_emptiable();
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

    assert_eq!(bounded.relativity(), Relativity::Absolute);
    assert_eq!(half_bounded.relativity(), Relativity::Absolute);
    assert_eq!(unbounded.relativity(), Relativity::Any);
    assert_eq!(EmptiableAbsBoundPair::Empty.relativity(), Relativity::Any);
}

mod interval_type {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bounded.interval_type(), IntervalType::Bounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        let half_bounded = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(unbounded.interval_type(), IntervalType::Unbounded);
    }

    #[test]
    fn empty() {
        let empty = EmptiableAbsBoundPair::Empty;

        assert_eq!(empty.interval_type(), IntervalType::Empty);
    }
}

mod interval_type_with_rel {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bounded.interval_type_with_rel(), IntervalTypeWithRel::AbsBounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type_with_rel(),
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        let half_bounded = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type_with_rel(),
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(unbounded.interval_type_with_rel(), IntervalTypeWithRel::Unbounded);
    }

    #[test]
    fn empty() {
        let empty = EmptiableAbsBoundPair::Empty;

        assert_eq!(empty.interval_type_with_rel(), IntervalTypeWithRel::Empty);
    }
}

mod ord {
    use super::*;

    #[test]
    fn bound_bound_equal_start_less_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_less_start_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_equal_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableAbsBoundPair::Empty;

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn unbound_bound() {
        let bound_pair1 = EmptiableAbsBoundPair::Empty;
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.cmp(&EmptiableAbsBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn from_opt_start_end() {
    assert_eq!(
        EmptiableAbsBoundPair::from(Some((AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture))),
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(None::<(AbsStartBound, AbsEndBound)>),
        EmptiableAbsBoundPair::Empty
    );
}

#[test]
fn from_opt_start_opt_end_opt() {
    assert_eq!(
        EmptiableAbsBoundPair::from(Some((
            Some(date_timestamp(2026, 1, 1)),
            Some(date_timestamp(2026, 1, 2))
        ))),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(None::<(Option<Timestamp>, Option<Timestamp>)>),
        EmptiableAbsBoundPair::Empty
    );
}

#[test]
fn from_opt_start_incl_opt_end_incl_opt() {
    assert_eq!(
        EmptiableAbsBoundPair::from(Some((
            Some((date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)),
            Some((date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive))
        ))),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(
            None::<(
                Option<(Timestamp, BoundInclusivity)>,
                Option<(Timestamp, BoundInclusivity)>
            )>
        ),
        EmptiableAbsBoundPair::Empty
    );
}

#[test]
fn from_bound_pair() {
    assert_eq!(
        EmptiableAbsBoundPair::from(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
        EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn from_bounded_interval() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();

    assert_eq!(
        EmptiableAbsBoundPair::from(BoundedAbsInterval::new(start, end,)),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound()).to_emptiable()
    );
}

#[test]
fn from_half_bounded_interval() {
    assert_eq!(
        EmptiableAbsBoundPair::from(HalfBoundedAbsInterval::from_time(
            date_timestamp(2026, 1, 1),
            OpeningDirection::ToFuture,
        )),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

#[test]
fn from_interval() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();

    assert_eq!(
        EmptiableAbsBoundPair::from(AbsInterval::Bounded(BoundedAbsInterval::new(start, end,))),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),).to_emptiable()
    );
}

#[test]
fn from_emptiable_interval() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
    assert_eq!(
        EmptiableAbsBoundPair::from(EmptiableAbsInterval::Bound(AbsInterval::Bounded(
            BoundedAbsInterval::new(start, end,)
        ))),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),).to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(EmptiableAbsInterval::Empty(EmptyInterval)),
        EmptiableAbsBoundPair::Empty
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableAbsBoundPair::from(UnboundedInterval),
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(EmptiableAbsBoundPair::from(EmptyInterval), EmptiableAbsBoundPair::Empty);
}

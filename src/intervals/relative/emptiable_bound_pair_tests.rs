use std::cmp::Ordering;
use std::time::Duration;

use jiff::SignedDuration;

use super::emptiable_bound_pair::*;
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
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
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
        EmptiableRelBoundPair::from_range(start..),
        RelBoundPair::new(
            RelFiniteBoundPos::new(start).to_start_bound(),
            RelEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bound_bound_less_start() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_less_start_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_less_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_equal_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() {
        let bound_pair1 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableRelBoundPair::Empty;

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn unbound_bound() {
        let bound_pair1 = EmptiableRelBoundPair::Empty;
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableRelBoundPair::Empty.ord_by_start_and_inv_length(&EmptiableRelBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn bound() {
    let bound_pair = RelBoundPair::new(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
    );
    let emptiable_bound_pair = bound_pair.clone().to_emptiable();

    assert_eq!(emptiable_bound_pair.bound(), Some(bound_pair));
    assert_eq!(EmptiableRelBoundPair::Empty.bound(), None);
}

mod to_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();

        assert_eq!(
            RelBoundPair::new(start.to_start_bound(), end.to_end_bound(),)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableRelInterval::Bound(RelInterval::Bounded(BoundedRelInterval::new(start, end)))
        );
    }

    #[test]
    fn half_bounded() {
        let reference = SignedDuration::from_hours(1);

        assert_eq!(
            RelBoundPair::new(
                RelFiniteBoundPos::new(reference).to_start_bound(),
                RelEndBound::InfiniteFuture
            )
            .to_emptiable()
            .to_emptiable_interval(),
            EmptiableRelInterval::Bound(RelInterval::HalfBounded(HalfBoundedRelInterval::from_offset(
                reference,
                OpeningDirection::ToFuture
            )))
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableRelInterval::Bound(RelInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelBoundPair::Empty.to_emptiable_interval(),
            EmptiableRelInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn emptiable_rel_bound_pair() {
    assert_eq!(
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
        .emptiable_rel_bound_pair(),
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
    );
}

#[test]
fn partial_rel_start() {
    assert_eq!(
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
        .partial_rel_start(),
        Some(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_start_bound()
        )
    );
    assert_eq!(EmptiableRelBoundPair::Empty.partial_rel_start(), None);
}

#[test]
fn partial_rel_end() {
    assert_eq!(
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound(),
        )
        .to_emptiable()
        .partial_rel_end(),
        Some(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound()
        )
    );
    assert_eq!(EmptiableRelBoundPair::Empty.partial_rel_end(), None);
}

#[test]
fn is_empty() {
    assert!(
        !RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture)
            .to_emptiable()
            .is_empty()
    );
    assert!(EmptiableRelBoundPair::Empty.is_empty());
}

#[test]
fn duration() {
    assert_eq!(
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
        .duration(),
        IntervalDuration::Finite(Duration::from_hours(1), Epsilon::None)
    );
    assert_eq!(
        EmptiableRelBoundPair::Empty.duration(),
        IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
    );
}

#[test]
fn openness() {
    assert_eq!(
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
        .openness(),
        Openness::Bounded
    );
    assert_eq!(EmptiableRelBoundPair::Empty.openness(), Openness::Empty);
}

#[test]
fn relativity() {
    let bounded = RelBoundPair::new(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
    )
    .to_emptiable();
    let half_bounded = RelBoundPair::new(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelEndBound::InfiniteFuture,
    )
    .to_emptiable();
    let unbounded = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();

    assert_eq!(bounded.relativity(), Relativity::Relative);
    assert_eq!(half_bounded.relativity(), Relativity::Relative);
    assert_eq!(unbounded.relativity(), Relativity::Any);
    assert_eq!(EmptiableRelBoundPair::Empty.relativity(), Relativity::Any);
}

mod interval_type {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bounded.interval_type(), IntervalType::Bounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        let half_bounded = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(unbounded.interval_type(), IntervalType::Unbounded);
    }

    #[test]
    fn empty() {
        let empty = EmptiableRelBoundPair::Empty;

        assert_eq!(empty.interval_type(), IntervalType::Empty);
    }
}

mod interval_type_with_rel {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bounded.interval_type_with_rel(), IntervalTypeWithRel::RelBounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type_with_rel(),
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture)
        );
    }

    #[test]
    fn half_bounded_to_past() {
        let half_bounded = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(
            half_bounded.interval_type_with_rel(),
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(unbounded.interval_type_with_rel(), IntervalTypeWithRel::Unbounded);
    }

    #[test]
    fn empty() {
        let empty = EmptiableRelBoundPair::Empty;

        assert_eq!(empty.interval_type_with_rel(), IntervalTypeWithRel::Empty);
    }
}

mod ord {
    use super::*;

    #[test]
    fn bound_bound_equal_start_less_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_less_start_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_equal_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() {
        let bound_pair1 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableRelBoundPair::Empty;

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn unbound_bound() {
        let bound_pair1 = EmptiableRelBoundPair::Empty;
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableRelBoundPair::Empty.cmp(&EmptiableRelBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn from_opt_start_end() {
    assert_eq!(
        EmptiableRelBoundPair::from(Some((RelStartBound::InfinitePast, RelEndBound::InfiniteFuture))),
        RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
    );
    assert_eq!(
        EmptiableRelBoundPair::from(None::<(RelStartBound, RelEndBound)>),
        EmptiableRelBoundPair::Empty
    );
}

#[test]
fn from_opt_start_opt_end_opt() {
    assert_eq!(
        EmptiableRelBoundPair::from(Some((
            Some(SignedDuration::from_hours(1)),
            Some(SignedDuration::from_hours(2))
        ))),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableRelBoundPair::from(None::<(Option<SignedDuration>, Option<SignedDuration>)>),
        EmptiableRelBoundPair::Empty
    );
}

#[test]
fn from_opt_start_incl_opt_end_incl_opt() {
    assert_eq!(
        EmptiableRelBoundPair::from(Some((
            Some((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
            Some((SignedDuration::from_hours(2), BoundInclusivity::Exclusive))
        ))),
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive).to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableRelBoundPair::from(
            None::<(
                Option<(SignedDuration, BoundInclusivity)>,
                Option<(SignedDuration, BoundInclusivity)>
            )>
        ),
        EmptiableRelBoundPair::Empty
    );
}

#[test]
fn from_bound_pair() {
    assert_eq!(
        EmptiableRelBoundPair::from(RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelEndBound::InfiniteFuture,
        )),
        EmptiableRelBoundPair::Bound(RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn from_bounded_interval() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();

    assert_eq!(
        EmptiableRelBoundPair::from(BoundedRelInterval::new(start, end,)),
        RelBoundPair::new(start.to_start_bound(), end.to_end_bound()).to_emptiable()
    );
}

#[test]
fn from_half_bounded_interval() {
    assert_eq!(
        EmptiableRelBoundPair::from(HalfBoundedRelInterval::from_offset(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture,
        )),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

#[test]
fn from_interval() {
    assert_eq!(
        EmptiableRelBoundPair::from(RelInterval::Bounded(BoundedRelInterval::from_offsets(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2),
        ))),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable()
    );
}

#[test]
fn from_emptiable_interval() {
    assert_eq!(
        EmptiableRelBoundPair::from(EmptiableRelInterval::Bound(RelInterval::Bounded(
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2),)
        ))),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableRelBoundPair::from(EmptiableRelInterval::Empty(EmptyInterval)),
        EmptiableRelBoundPair::Empty
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableRelBoundPair::from(UnboundedInterval),
        RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(EmptiableRelBoundPair::from(EmptyInterval), EmptiableRelBoundPair::Empty);
}

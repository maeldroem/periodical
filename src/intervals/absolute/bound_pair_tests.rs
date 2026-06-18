use std::cmp::Ordering;
use std::time::Duration;

use super::bound_pair::*;
use crate::intervals::absolute::{
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
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
use crate::intervals::special::UnboundedInterval;
use crate::test_data::{date_timestamp, datetime_timestamp};

#[test]
fn unchecked_new() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound();

    let abs_bounds = AbsBoundPair::unchecked_new(start, end);

    assert_eq!(abs_bounds.abs_start(), start);
    assert_eq!(abs_bounds.abs_end(), end);
}

#[test]
fn new_should_swap() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_bounds() {
    let start =
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
    let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_exclusive_bounds() {
    let start =
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound();
    let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_inclusive_bounds() {
    let start =
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
    let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_bounds() {
    let start =
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound();
    let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,).to_end_bound(),
    );
}

#[test]
fn from_range() {
    let start = date_timestamp(2026, 1, 1);
    let range = start..;

    let bound_pair = AbsBoundPair::from_range(range);

    assert_eq!(bound_pair.start(), AbsFiniteBoundPos::new(start).to_start_bound());
    assert_eq!(bound_pair.end(), AbsEndBound::InfiniteFuture);
}

#[test]
fn start_end() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
    let end = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 8, 0, 0)).to_end_bound();

    let bound_pair = AbsBoundPair::new(start, end);

    assert_eq!(bound_pair.start(), start);
    assert_eq!(bound_pair.end(), end);
}

#[test]
fn unchecked_set_start() {
    let mut bounds = AbsBoundPair::new(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_end_bound(),
    );

    let new_start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 3)).to_start_bound();

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.abs_start(), new_start);
}

#[test]
fn unchecked_set_end() {
    let mut bounds = AbsBoundPair::new(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound(),
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 3)).to_end_bound(),
    );

    let new_end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound();

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.abs_end(), new_end);
}

#[test]
fn set_start_chronological() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_end_bound();
    let new_start = AbsFiniteBoundPos::new(datetime_timestamp(2025, 1, 1, 8, 0, 0)).to_start_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(bounds.set_start(new_start));

    assert_eq!(bounds.abs_start(), new_start);
    assert_eq!(bounds.abs_end(), end);
}

#[test]
fn set_start_unchronological() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_end_bound();
    let new_start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 3)).to_start_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(!bounds.set_start(new_start));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
}

#[test]
fn set_end_chronological() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 3)).to_end_bound();
    let new_end = AbsFiniteBoundPos::new(datetime_timestamp(2025, 1, 2, 8, 0, 0)).to_end_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(bounds.set_end(new_end));

    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), new_end);
}

#[test]
fn set_end_unchronological() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 3)).to_end_bound();
    let new_end = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(!bounds.set_end(new_end));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn less_start() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn greater_start() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn less_start_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn greater_start_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_less_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_equal_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn equal_start_greater_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_less_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_greater_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn equal_start_inf_less_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_inf_greater_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_inf_equal_end() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn equal_start_inf_less_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_inf_greater_end_inf() {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_inf_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }
}

#[test]
fn to_interval() {
    let start = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 8, 0, 0)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 2, 8, 0, 0)).to_finite_end_bound();

    let bound_pair = AbsBoundPair::new(start.to_start_bound(), end.to_end_bound());

    assert_eq!(
        bound_pair.to_interval(),
        AbsInterval::Bounded(BoundedAbsInterval::new(start, end))
    );
}

#[test]
fn to_emptiable_interval() {
    let start = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 8, 0, 0)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 2, 8, 0, 0)).to_finite_end_bound();

    let bound_pair = AbsBoundPair::new(start.to_start_bound(), end.to_end_bound());

    assert_eq!(
        bound_pair.to_emptiable_interval(),
        EmptiableAbsInterval::Bound(AbsInterval::Bounded(BoundedAbsInterval::new(start, end)))
    );
}

#[test]
fn to_emptiable() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();

    assert_eq!(
        AbsBoundPair::new(start, end).to_emptiable(),
        EmptiableAbsBoundPair::Bound(AbsBoundPair::new(start, end)),
    );
}

#[test]
fn abs_start() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();

    assert_eq!(AbsBoundPair::new(start, end).abs_start(), start);
}

#[test]
fn abs_end() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();

    assert_eq!(AbsBoundPair::new(start, end).abs_end(), end);
}

#[test]
fn abs_bound_pair() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();

    assert_eq!(
        AbsBoundPair::new(start, end).abs_bound_pair(),
        AbsBoundPair::new(start, end)
    );
}

#[test]
fn duration() {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Inclusive)
            .to_start_bound(),
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 16, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert_eq!(
        bounded.duration(),
        IntervalDuration::Finite(Duration::from_hours(8), Epsilon::End)
    );
    assert_eq!(half_bounded.duration(), IntervalDuration::Infinite);
    assert_eq!(unbounded.duration(), IntervalDuration::Infinite);
}

#[test]
fn openness() {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Inclusive)
            .to_start_bound(),
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 16, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded_to_past = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded_to_future = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Exclusive)
            .to_start_bound(),
        AbsEndBound::InfiniteFuture,
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert_eq!(bounded.openness(), Openness::Bounded);
    assert_eq!(half_bounded_to_past.openness(), Openness::HalfBounded);
    assert_eq!(half_bounded_to_future.openness(), Openness::HalfBounded);
    assert_eq!(unbounded.openness(), Openness::Unbounded);
}

#[test]
fn relativity() {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Inclusive)
            .to_start_bound(),
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 16, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert_eq!(bounded.relativity(), Relativity::Absolute);
    assert_eq!(half_bounded.relativity(), Relativity::Absolute);
    assert_eq!(unbounded.relativity(), Relativity::Any);
}

mod ord {
    use super::*;

    #[test]
    fn unbounded_unbounded() {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_half_bounded_to_future() {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn unbounded_half_bounded_to_past() {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_bounded() {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_unbounded() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_after_first() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_to_future_before_first() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_inclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_exclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn half_bounded_to_future_to_past_before_first() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_after_first() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_inclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_exclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_bounds() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_before_first() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 3)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_after_first() {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 2)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 3)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2025, 1, 4)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }
}

#[test]
fn is_empty() {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Inclusive)
            .to_start_bound(),
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 16, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_incl(datetime_timestamp(2026, 1, 1, 8, 0, 0), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert!(!bounded.is_empty());
    assert!(!half_bounded.is_empty());
    assert!(!unbounded.is_empty());
}

mod interval_type {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bounded.interval_type(), IntervalType::Bounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

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
        );

        assert_eq!(
            half_bounded.interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(unbounded.interval_type(), IntervalType::Unbounded);
    }
}

mod interval_type_with_rel {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
        );

        assert_eq!(bounded.interval_type_with_rel(), IntervalTypeWithRel::AbsBounded);
    }

    #[test]
    fn half_bounded_to_future() {
        let half_bounded = AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

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
        );

        assert_eq!(
            half_bounded.interval_type_with_rel(),
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)
        );
    }

    #[test]
    fn unbounded() {
        let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(unbounded.interval_type_with_rel(), IntervalTypeWithRel::Unbounded);
    }
}

#[test]
fn from_opt_timestamp_pair() {
    let start = date_timestamp(2026, 1, 1);

    assert_eq!(
        AbsBoundPair::from((Some(start), None)),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(start).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
    );
}

#[test]
fn from_opt_timestamp_inclusivity_pair() {
    let start = datetime_timestamp(2026, 1, 1, 8, 0, 0);
    let end = datetime_timestamp(2026, 1, 1, 16, 0, 0);

    assert_eq!(
        AbsBoundPair::from((
            Some((start, BoundInclusivity::Inclusive)),
            Some((end, BoundInclusivity::Exclusive))
        )),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(start, BoundInclusivity::Inclusive).to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(end, BoundInclusivity::Exclusive).to_end_bound(),
        )
    );
}

#[test]
fn from_bounded_absolute_interval() {
    let start = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 8, 0, 0)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 16, 0, 0)).to_finite_end_bound();

    let bounded = BoundedAbsInterval::new(start, end);

    assert_eq!(
        AbsBoundPair::from(bounded),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),),
    );
}

#[test]
fn from_half_bounded_absolute_interval() {
    let reference = datetime_timestamp(2026, 1, 1, 8, 0, 0);

    let half_bounded = HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToFuture);

    assert_eq!(
        AbsBoundPair::from(half_bounded),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(reference).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
    );
}

mod from_abs_interval {
    use super::*;

    #[test]
    fn from_abs_interval_bounded() {
        let start = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 8, 0, 0)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 16, 0, 0)).to_finite_end_bound();

        let interval = BoundedAbsInterval::new(start, end).to_interval();

        assert_eq!(
            AbsBoundPair::from(interval),
            AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),)
        );
    }

    #[test]
    fn from_abs_interval_half_bounded() {
        let reference = datetime_timestamp(2026, 1, 1, 8, 0, 0);

        let interval = HalfBoundedAbsInterval::from_time(reference, OpeningDirection::ToFuture).to_interval();

        assert_eq!(
            AbsBoundPair::from(interval),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(reference).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            )
        );
    }

    #[test]
    fn from_abs_interval_unbounded() {
        let interval = UnboundedInterval.to_abs_interval();

        assert_eq!(
            AbsBoundPair::from(interval),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
        );
    }
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        AbsBoundPair::from(UnboundedInterval),
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
    );
}

#[test]
fn try_from_emptiable_abs_bound_pair() {
    assert_eq!(
        AbsBoundPair::try_from(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        ))),
        Ok(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
    );
    assert_eq!(
        AbsBoundPair::try_from(EmptiableAbsBoundPair::Empty),
        Err(AbsBoundPairTryFromEmptiableAbsBoundPairError),
    );
}

mod try_from_emptiable_abs_interval {
    use super::*;
    use crate::prelude::EmptyInterval;

    #[test]
    fn not_empty() {
        let start = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 8, 0, 0)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 16, 0, 0)).to_finite_end_bound();

        let interval = BoundedAbsInterval::new(start, end).to_emptiable_interval();

        assert_eq!(
            AbsBoundPair::try_from(interval),
            Ok(AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            AbsBoundPair::try_from(EmptiableAbsInterval::Empty(EmptyInterval)),
            Err(AbsBoundPairTryFromEmptiableAbsIntervalError)
        );
    }
}

use std::cmp::Ordering;
use std::time::Duration;

use jiff::SignedDuration;

use super::bound_pair::*;
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
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};

#[test]
fn unchecked_new() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let rel_bounds = RelativeBoundPair::unchecked_new(start, end);

    assert_eq!(rel_bounds.rel_start(), start);
    assert_eq!(rel_bounds.rel_end(), end);
}

#[test]
fn new_should_swap() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_exclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_inclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_bounds() {
    let start = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_start_bound();
    let end = RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_end_bound();

    let rel_bounds = RelativeBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn from_range() {
    let start = SignedDuration::from_hours(1);
    let range = start..;

    let bound_pair = RelativeBoundPair::from_range(range);

    assert_eq!(bound_pair.start(), RelativeFiniteBound::new(start).to_start_bound());
    assert_eq!(bound_pair.end(), RelativeEndBound::InfiniteFuture);
}

#[test]
fn start_end() {
    let start = RelativeFiniteBound::new(SignedDuration::ZERO).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_end_bound();

    let bound_pair = RelativeBoundPair::new(start, end);

    assert_eq!(bound_pair.start(), start);
    assert_eq!(bound_pair.end(), end);
}

#[test]
fn unchecked_set_start() {
    let mut bounds = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
    );

    let new_start = RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound();

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.rel_start(), new_start);
}

#[test]
fn unchecked_set_end() {
    let mut bounds = RelativeBoundPair::new(
        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
    );

    let new_end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.rel_end(), new_end);
}

#[test]
fn set_start_chronological() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound();
    let new_start = RelativeFiniteBound::new(SignedDuration::from_hours(-1)).to_start_bound();

    let mut bounds = RelativeBoundPair::new(start, end);

    assert!(bounds.set_start(new_start));

    assert_eq!(bounds.rel_start(), new_start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn set_start_unchronological() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound();
    let new_start = RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound();

    let mut bounds = RelativeBoundPair::new(start, end);

    assert!(!bounds.set_start(new_start));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn set_end_chronological() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound();
    let new_end = RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound();

    let mut bounds = RelativeBoundPair::new(start, end);

    assert!(bounds.set_end(new_end));

    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), new_end);
}

#[test]
fn set_end_unchronological() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound();
    let new_end = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound();

    let mut bounds = RelativeBoundPair::new(start, end);

    assert!(!bounds.set_end(new_end));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn less() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::ZERO).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_end_bound(),
        );
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(10)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn greater() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(12)).to_end_bound(),
        );
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(14)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_less() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(10)).to_end_bound(),
        );
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(5)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_equal() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(10)).to_end_bound(),
        );
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(10)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn equal_greater() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(5)).to_end_bound(),
        );
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(10)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }
}

#[test]
fn to_interval() {
    let start = SignedDuration::from_hours(8);
    let end = SignedDuration::from_hours(16);

    let bound_pair = RelativeBoundPair::new(
        RelativeFiniteBound::new(start).to_start_bound(),
        RelativeFiniteBound::new(end).to_end_bound(),
    );

    assert_eq!(
        bound_pair.to_interval(),
        RelativeInterval::Bounded(BoundedRelativeInterval::new(start, end))
    );
}

#[test]
fn to_emptiable_interval() {
    let start = SignedDuration::from_hours(8);
    let end = SignedDuration::from_hours(16);

    let bound_pair = RelativeBoundPair::new(
        RelativeFiniteBound::new(start).to_start_bound(),
        RelativeFiniteBound::new(end).to_end_bound(),
    );

    assert_eq!(
        bound_pair.to_emptiable_interval(),
        EmptiableRelativeInterval::Bound(RelativeInterval::Bounded(BoundedRelativeInterval::new(start, end)))
    );
}

#[test]
fn to_emptiable() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(5)).to_end_bound();

    assert_eq!(
        RelativeBoundPair::new(start, end).to_emptiable(),
        EmptiableRelativeBoundPair::Bound(RelativeBoundPair::new(start, end)),
    );
}

#[test]
fn rel_start() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound();

    assert_eq!(RelativeBoundPair::new(start, end).rel_start(), start);
}

#[test]
fn rel_end() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound();

    assert_eq!(RelativeBoundPair::new(start, end).rel_end(), end);
}

#[test]
fn rel_bound_pair() {
    let start = RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound();
    let end = RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound();

    assert_eq!(
        RelativeBoundPair::new(start, end).rel_bound_pair(),
        RelativeBoundPair::new(start, end)
    );
}

#[test]
fn duration() {
    let bounded = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert_eq!(
        bounded.duration(),
        IntervalDuration::Finite(Duration::from_hours(8), Epsilon::End)
    );
    assert_eq!(half_bounded.duration(), IntervalDuration::Infinite);
    assert_eq!(unbounded.duration(), IntervalDuration::Infinite);
}

#[test]
fn openness() {
    let bounded = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded_to_past = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded_to_future = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    );
    let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert_eq!(bounded.openness(), Openness::Bounded);
    assert_eq!(half_bounded_to_past.openness(), Openness::HalfBounded);
    assert_eq!(half_bounded_to_future.openness(), Openness::HalfBounded);
    assert_eq!(unbounded.openness(), Openness::Unbounded);
}

#[test]
fn relativity() {
    let bounded = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert_eq!(bounded.relativity(), Relativity::Relative);
    assert_eq!(half_bounded.relativity(), Relativity::Relative);
    assert_eq!(unbounded.relativity(), Relativity::Relative);
}

mod cmp {
    use super::*;

    #[test]
    fn unbounded_unbounded() {
        let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
        let b = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_half_bounded_to_future() {
        let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::ZERO).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn unbounded_half_bounded_to_past() {
        let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
        let b = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::ZERO).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_bounded() {
        let a = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_unbounded() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::ZERO).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_after_first() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_to_future_before_first() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_inclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_exclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn half_bounded_to_future_to_past_before_first() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_after_first() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_inclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_exclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Exclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_bounds() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::ZERO, BoundInclusivity::Inclusive).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_before_first() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(24)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_after_first() {
        let a = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        );
        let b = RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(24)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(32)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }
}

#[test]
fn is_empty() {
    let bounded = RelativeBoundPair::new(
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = RelativeBoundPair::new(
        RelativeStartBound::InfinitePast,
        RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

    assert!(!bounded.is_empty());
    assert!(!half_bounded.is_empty());
    assert!(!unbounded.is_empty());
}

#[test]
fn from_opt_timestamp_pair() {
    let start = SignedDuration::ZERO;

    assert_eq!(
        RelativeBoundPair::from((Some(start), None)),
        RelativeBoundPair::new(
            RelativeFiniteBound::new(start).to_start_bound(),
            RelativeEndBound::InfiniteFuture
        )
    );
}

#[test]
fn from_opt_timestamp_inclusivity_pair() {
    let start = SignedDuration::from_hours(8);
    let end = SignedDuration::from_hours(16);

    assert_eq!(
        RelativeBoundPair::from((
            Some((start, BoundInclusivity::Inclusive)),
            Some((end, BoundInclusivity::Exclusive))
        )),
        RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(start, BoundInclusivity::Inclusive).to_start_bound(),
            RelativeFiniteBound::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound(),
        )
    );
}

#[test]
fn from_bounded_relative_interval() {
    let start = SignedDuration::from_hours(8);
    let end = SignedDuration::from_hours(16);

    let bounded = BoundedRelativeInterval::new(start, end);

    assert_eq!(
        RelativeBoundPair::from(bounded),
        RelativeBoundPair::new(
            RelativeFiniteBound::new(start).to_start_bound(),
            RelativeFiniteBound::new(end).to_end_bound(),
        ),
    );
}

#[test]
fn from_half_bounded_relative_interval() {
    let reference = SignedDuration::from_hours(8);

    let half_bounded = HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToFuture);

    assert_eq!(
        RelativeBoundPair::from(half_bounded),
        RelativeBoundPair::new(
            RelativeFiniteBound::new(reference).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
    );
}

mod from_rel_interval {
    use super::*;
    use crate::prelude::UnboundedInterval;

    #[test]
    fn from_rel_interval_bounded() {
        let start = SignedDuration::from_hours(8);
        let end = SignedDuration::from_hours(16);

        let interval = BoundedRelativeInterval::new(start, end).to_interval();

        assert_eq!(
            RelativeBoundPair::from(interval),
            RelativeBoundPair::new(
                RelativeFiniteBound::new(start).to_start_bound(),
                RelativeFiniteBound::new(end).to_end_bound(),
            )
        );
    }

    #[test]
    fn from_rel_interval_half_bounded() {
        let reference = SignedDuration::from_hours(8);

        let interval = HalfBoundedRelativeInterval::new(reference, OpeningDirection::ToFuture).to_interval();

        assert_eq!(
            RelativeBoundPair::from(interval),
            RelativeBoundPair::new(
                RelativeFiniteBound::new(reference).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            )
        );
    }

    #[test]
    fn from_rel_interval_unbounded() {
        let interval = UnboundedInterval.to_rel_interval();

        assert_eq!(
            RelativeBoundPair::from(interval),
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
        );
    }
}

#[test]
fn try_from_emptiable_rel_bound_pair() {
    assert_eq!(
        RelativeBoundPair::try_from(EmptiableRelativeBoundPair::Bound(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        ))),
        Ok(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
    );
    assert_eq!(
        RelativeBoundPair::try_from(EmptiableRelativeBoundPair::Empty),
        Err(RelativeBoundPairTryFromEmptiableRelativeBoundPairError),
    );
}

mod try_from_emptiable_rel_interval {
    use super::*;
    use crate::prelude::EmptyInterval;

    #[test]
    fn not_empty() {
        let start = SignedDuration::from_hours(8);
        let end = SignedDuration::from_hours(16);

        let interval = BoundedRelativeInterval::new(start, end).to_emptiable_interval();

        assert_eq!(
            RelativeBoundPair::try_from(interval),
            Ok(RelativeBoundPair::new(
                RelativeFiniteBound::new(start).to_start_bound(),
                RelativeFiniteBound::new(end).to_end_bound(),
            ))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            RelativeBoundPair::try_from(EmptiableRelativeInterval::Empty(EmptyInterval)),
            Err(RelativeBoundPairTryFromEmptiableRelativeIntervalError)
        );
    }
}

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
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};

#[test]
fn unchecked_new() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    let rel_bounds = RelBoundPair::unchecked_new(start, end);

    assert_eq!(rel_bounds.rel_start(), start);
    assert_eq!(rel_bounds.rel_end(), end);
}

#[test]
fn new_should_swap() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    let rel_bounds = RelBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_bounds() {
    let start =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
    let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    let rel_bounds = RelBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_exclusive_bounds() {
    let start =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound();
    let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_end_bound();

    let rel_bounds = RelBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_exclusive_inclusive_bounds() {
    let start =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
    let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_end_bound();

    let rel_bounds = RelBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn new_from_same_times_inclusive_bounds() {
    let start =
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_start_bound();
    let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
        .to_end_bound();

    let rel_bounds = RelBoundPair::new(start, end);

    assert_eq!(
        rel_bounds.rel_start(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_start_bound(),
    );
    assert_eq!(
        rel_bounds.rel_end(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
            .to_end_bound(),
    );
}

#[test]
fn from_range() {
    let start = SignedDuration::from_hours(1);
    let range = start..;

    let bound_pair = RelBoundPair::from_range(range);

    assert_eq!(bound_pair.start(), RelFiniteBoundPos::new(start).to_start_bound());
    assert_eq!(bound_pair.end(), RelEndBound::InfiniteFuture);
}

#[test]
fn start_end() {
    let start = RelFiniteBoundPos::new(SignedDuration::ZERO).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_end_bound();

    let bound_pair = RelBoundPair::new(start, end);

    assert_eq!(bound_pair.start(), start);
    assert_eq!(bound_pair.end(), end);
}

#[test]
fn unchecked_set_start() {
    let mut bounds = RelBoundPair::new(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
    );

    let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound();

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.rel_start(), new_start);
}

#[test]
fn unchecked_set_end() {
    let mut bounds = RelBoundPair::new(
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
    );

    let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.rel_end(), new_end);
}

#[test]
fn set_start_chronological() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();
    let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(-1)).to_start_bound();

    let mut bounds = RelBoundPair::new(start, end);

    assert!(bounds.set_start(new_start));

    assert_eq!(bounds.rel_start(), new_start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn set_start_unchronological() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();
    let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound();

    let mut bounds = RelBoundPair::new(start, end);

    assert!(!bounds.set_start(new_start));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

#[test]
fn set_end_chronological() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound();
    let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound();

    let mut bounds = RelBoundPair::new(start, end);

    assert!(bounds.set_end(new_end));

    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), new_end);
}

#[test]
fn set_end_unchronological() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound();
    let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

    let mut bounds = RelBoundPair::new(start, end);

    assert!(!bounds.set_end(new_end));

    // Bounds should remain unchanged
    assert_eq!(bounds.rel_start(), start);
    assert_eq!(bounds.rel_end(), end);
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn less_start() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn greater_start() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn less_start_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn greater_start_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_less_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_equal_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn equal_start_greater_end() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_less_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_greater_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_equal_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let bound_pair2 = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn equal_start_inf_less_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_inf_greater_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_inf_equal_end() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn equal_start_inf_less_end_inf() {
        let bound_pair1 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);
        let bound_pair2 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn equal_start_inf_greater_end_inf() {
        let bound_pair1 = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        );
        let bound_pair2 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn equal_start_inf_equal_end_inf() {
        let bound_pair1 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);
        let bound_pair2 = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }
}

#[test]
fn to_interval() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_end_bound();

    let bound_pair = RelBoundPair::new(start.to_start_bound(), end.to_end_bound());

    assert_eq!(
        bound_pair.to_interval(),
        RelInterval::Bounded(BoundedRelInterval::new(start, end))
    );
}

#[test]
fn to_emptiable_interval() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_end_bound();

    let bound_pair = RelBoundPair::new(start.to_start_bound(), end.to_end_bound());

    assert_eq!(
        bound_pair.to_emptiable_interval(),
        EmptiableRelInterval::Bound(RelInterval::Bounded(BoundedRelInterval::new(start, end)))
    );
}

#[test]
fn to_emptiable() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(5)).to_end_bound();

    assert_eq!(
        RelBoundPair::new(start, end).to_emptiable(),
        EmptiableRelBoundPair::Bound(RelBoundPair::new(start, end)),
    );
}

#[test]
fn rel_start() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound();

    assert_eq!(RelBoundPair::new(start, end).rel_start(), start);
}

#[test]
fn rel_end() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound();

    assert_eq!(RelBoundPair::new(start, end).rel_end(), end);
}

#[test]
fn rel_bound_pair() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound();

    assert_eq!(
        RelBoundPair::new(start, end).rel_bound_pair(),
        RelBoundPair::new(start, end)
    );
}

#[test]
fn duration() {
    let bounded = RelBoundPair::new(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = RelBoundPair::new(
        RelStartBound::InfinitePast,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

    assert_eq!(
        bounded.duration(),
        IntervalDuration::Finite(Duration::from_hours(8), Epsilon::End)
    );
    assert_eq!(half_bounded.duration(), IntervalDuration::Infinite);
    assert_eq!(unbounded.duration(), IntervalDuration::Infinite);
}

#[test]
fn openness() {
    let bounded = RelBoundPair::new(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded_to_past = RelBoundPair::new(
        RelStartBound::InfinitePast,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded_to_future = RelBoundPair::new(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_start_bound(),
        RelEndBound::InfiniteFuture,
    );
    let unbounded = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

    assert_eq!(bounded.openness(), Openness::Bounded);
    assert_eq!(half_bounded_to_past.openness(), Openness::HalfBounded);
    assert_eq!(half_bounded_to_future.openness(), Openness::HalfBounded);
    assert_eq!(unbounded.openness(), Openness::Unbounded);
}

#[test]
fn relativity() {
    let bounded = RelBoundPair::new(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = RelBoundPair::new(
        RelStartBound::InfinitePast,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

    assert_eq!(bounded.relativity(), Relativity::Rel);
    assert_eq!(half_bounded.relativity(), Relativity::Rel);
    assert_eq!(unbounded.relativity(), Relativity::Any);
}

mod ord {
    use super::*;

    #[test]
    fn unbounded_unbounded() {
        let a = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);
        let b = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_half_bounded_to_future() {
        let a = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::ZERO).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn unbounded_half_bounded_to_past() {
        let a = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);
        let b = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::ZERO).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_bounded() {
        let a = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_unbounded() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::ZERO).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_after_first() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_to_future_before_first() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_inclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_exclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn half_bounded_to_future_to_past_before_first() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_after_first() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_inclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_exclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Exclusive)
                .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_bounds() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new_with_incl(SignedDuration::ZERO, BoundInclusivity::Inclusive)
                .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_before_first() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(24)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_after_first() {
        let a = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        );
        let b = RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(24)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(32)).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
    }
}

#[test]
fn is_empty() {
    let bounded = RelBoundPair::new(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Inclusive)
            .to_start_bound(),
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(16), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let half_bounded = RelBoundPair::new(
        RelStartBound::InfinitePast,
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(8), BoundInclusivity::Exclusive)
            .to_end_bound(),
    );
    let unbounded = RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture);

    assert!(!bounded.is_empty());
    assert!(!half_bounded.is_empty());
    assert!(!unbounded.is_empty());
}

#[test]
fn from_opt_signed_duration_pair() {
    let start = SignedDuration::ZERO;

    assert_eq!(
        RelBoundPair::from((Some(start), None)),
        RelBoundPair::new(
            RelFiniteBoundPos::new(start).to_start_bound(),
            RelEndBound::InfiniteFuture
        )
    );
}

#[test]
fn from_opt_signed_duration_inclusivity_pair() {
    let start = SignedDuration::from_hours(8);
    let end = SignedDuration::from_hours(16);

    assert_eq!(
        RelBoundPair::from((
            Some((start, BoundInclusivity::Inclusive)),
            Some((end, BoundInclusivity::Exclusive))
        )),
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_incl(start, BoundInclusivity::Inclusive).to_start_bound(),
            RelFiniteBoundPos::new_with_incl(end, BoundInclusivity::Exclusive).to_end_bound(),
        )
    );
}

#[test]
fn from_bounded_relative_interval() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_end_bound();

    let bounded = BoundedRelInterval::new(start, end);

    assert_eq!(
        RelBoundPair::from(bounded),
        RelBoundPair::new(start.to_start_bound(), end.to_end_bound(),),
    );
}

#[test]
fn from_half_bounded_relative_interval() {
    let reference = SignedDuration::from_hours(8);

    let half_bounded = HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToFuture);

    assert_eq!(
        RelBoundPair::from(half_bounded),
        RelBoundPair::new(
            RelFiniteBoundPos::new(reference).to_start_bound(),
            RelEndBound::InfiniteFuture,
        )
    );
}

mod from_rel_interval {
    use super::*;
    use crate::prelude::UnboundedInterval;

    #[test]
    fn from_rel_interval_bounded() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_end_bound();

        let interval = BoundedRelInterval::new(start, end).to_interval();

        assert_eq!(
            RelBoundPair::from(interval),
            RelBoundPair::new(start.to_start_bound(), end.to_end_bound(),)
        );
    }

    #[test]
    fn from_rel_interval_half_bounded() {
        let reference = SignedDuration::from_hours(8);

        let interval = HalfBoundedRelInterval::new_from_offset(reference, OpeningDirection::ToFuture).to_interval();

        assert_eq!(
            RelBoundPair::from(interval),
            RelBoundPair::new(
                RelFiniteBoundPos::new(reference).to_start_bound(),
                RelEndBound::InfiniteFuture,
            )
        );
    }

    #[test]
    fn from_rel_interval_unbounded() {
        let interval = UnboundedInterval.to_rel_interval();

        assert_eq!(
            RelBoundPair::from(interval),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture)
        );
    }
}

#[test]
fn try_from_emptiable_rel_bound_pair() {
    assert_eq!(
        RelBoundPair::try_from(EmptiableRelBoundPair::Bound(RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelEndBound::InfiniteFuture,
        ))),
        Ok(RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelEndBound::InfiniteFuture,
        )),
    );
    assert_eq!(
        RelBoundPair::try_from(EmptiableRelBoundPair::Empty),
        Err(RelBoundPairTryFromEmptiableRelBoundPairError),
    );
}

mod try_from_emptiable_rel_interval {
    use super::*;
    use crate::prelude::EmptyInterval;

    #[test]
    fn not_empty() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_end_bound();

        let interval = BoundedRelInterval::new(start, end).to_emptiable_interval();

        assert_eq!(
            RelBoundPair::try_from(interval),
            Ok(RelBoundPair::new(start.to_start_bound(), end.to_end_bound(),))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            RelBoundPair::try_from(EmptiableRelInterval::Empty(EmptyInterval)),
            Err(RelBoundPairTryFromEmptiableRelIntervalError)
        );
    }
}

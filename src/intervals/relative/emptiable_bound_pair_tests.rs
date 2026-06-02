use std::cmp::Ordering;
use std::time::Duration;

use jiff::SignedDuration;

use super::emptiable_bound_pair::*;
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
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
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
        EmptiableRelativeBoundPair::from_range(start..),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(start).to_start_bound(),
            RelativeEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bound_bound_less_start() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_less_start_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_less_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_equal_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() {
        let bound_pair1 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableRelativeBoundPair::Empty;

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn unbound_bound() {
        let bound_pair1 = EmptiableRelativeBoundPair::Empty;
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableRelativeBoundPair::Empty.ord_by_start_and_inv_length(&EmptiableRelativeBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn bound() {
    let bound_pair = RelativeBoundPair::new(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
    );
    let emptiable_bound_pair = bound_pair.clone().to_emptiable();

    assert_eq!(emptiable_bound_pair.bound(), Some(bound_pair));
    assert_eq!(EmptiableRelativeBoundPair::Empty.bound(), None);
}

mod to_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() {
        let start = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_finite_end_bound();

        assert_eq!(
            RelativeBoundPair::new(start.to_start_bound(), end.to_end_bound(),)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableRelativeInterval::Bound(RelativeInterval::Bounded(BoundedRelativeInterval::new(start, end)))
        );
    }

    #[test]
    fn half_bounded() {
        let reference = SignedDuration::from_hours(1);

        assert_eq!(
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(reference).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )
            .to_emptiable()
            .to_emptiable_interval(),
            EmptiableRelativeInterval::Bound(RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_from_offset(reference, OpeningDirection::ToFuture)
            ))
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableRelativeInterval::Bound(RelativeInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableRelativeBoundPair::Empty.to_emptiable_interval(),
            EmptiableRelativeInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn emptiable_rel_bound_pair() {
    assert_eq!(
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(2),
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
        .emptiable_rel_bound_pair(),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(2),
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
    );
}

#[test]
fn partial_rel_start() {
    assert_eq!(
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(2),
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
        .partial_rel_start(),
        Some(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive
            )
            .to_start_bound()
        )
    );
    assert_eq!(EmptiableRelativeBoundPair::Empty.partial_rel_start(), None);
}

#[test]
fn partial_rel_end() {
    assert_eq!(
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(2),
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
        .partial_rel_end(),
        Some(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(2),
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
        )
    );
    assert_eq!(EmptiableRelativeBoundPair::Empty.partial_rel_end(), None);
}

#[test]
fn is_empty() {
    assert!(
        !RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
            .to_emptiable()
            .is_empty()
    );
    assert!(EmptiableRelativeBoundPair::Empty.is_empty());
}

#[test]
fn duration() {
    assert_eq!(
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
        .duration(),
        IntervalDuration::Finite(Duration::from_hours(1), Epsilon::None)
    );
    assert_eq!(
        EmptiableRelativeBoundPair::Empty.duration(),
        IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
    );
}

#[test]
fn openness() {
    assert_eq!(
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
        .openness(),
        Openness::Bounded
    );
    assert_eq!(EmptiableRelativeBoundPair::Empty.openness(), Openness::Empty);
}

#[test]
fn relativity() {
    let bounded = RelativeBoundPair::new(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
    )
    .to_emptiable();
    let half_bounded = RelativeBoundPair::new(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
        RelativeEndBound::InfiniteFuture,
    )
    .to_emptiable();
    let unbounded =
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();

    assert_eq!(bounded.relativity(), Relativity::Relative);
    assert_eq!(half_bounded.relativity(), Relativity::Relative);
    assert_eq!(unbounded.relativity(), Relativity::Any);
    assert_eq!(EmptiableRelativeBoundPair::Empty.relativity(), Relativity::Any);
}

mod ord {
    use super::*;

    #[test]
    fn bound_bound_equal_start_less_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_less_start_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn bound_bound_greater_start_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn bound_bound_equal_start_equal_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() {
        let bound_pair1 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 =
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() {
        let bound_pair1 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableRelativeBoundPair::Empty;

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
    }

    #[test]
    fn unbound_bound() {
        let bound_pair1 = EmptiableRelativeBoundPair::Empty;
        let bound_pair2 = RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableRelativeBoundPair::Empty.cmp(&EmptiableRelativeBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn from_opt_start_end() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(Some((
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture
        ))),
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable()
    );
    assert_eq!(
        EmptiableRelativeBoundPair::from(None::<(RelativeStartBound, RelativeEndBound)>),
        EmptiableRelativeBoundPair::Empty
    );
}

#[test]
fn from_opt_start_opt_end_opt() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(Some((
            Some(SignedDuration::from_hours(1)),
            Some(SignedDuration::from_hours(2))
        ))),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableRelativeBoundPair::from(None::<(Option<SignedDuration>, Option<SignedDuration>)>),
        EmptiableRelativeBoundPair::Empty
    );
}

#[test]
fn from_opt_start_incl_opt_end_incl_opt() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(Some((
            Some((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
            Some((SignedDuration::from_hours(2), BoundInclusivity::Exclusive))
        ))),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(2),
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableRelativeBoundPair::from(
            None::<(
                Option<(SignedDuration, BoundInclusivity)>,
                Option<(SignedDuration, BoundInclusivity)>
            )>
        ),
        EmptiableRelativeBoundPair::Empty
    );
}

#[test]
fn from_bound_pair() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
        EmptiableRelativeBoundPair::Bound(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn from_bounded_interval() {
    let start = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    let end = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_finite_end_bound();

    assert_eq!(
        EmptiableRelativeBoundPair::from(BoundedRelativeInterval::new(start, end,)),
        RelativeBoundPair::new(start.to_start_bound(), end.to_end_bound()).to_emptiable()
    );
}

#[test]
fn from_half_bounded_interval() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(HalfBoundedRelativeInterval::new_from_offset(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture,
        )),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
}

#[test]
fn from_interval() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(RelativeInterval::Bounded(BoundedRelativeInterval::from_offsets(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2),
        ))),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable()
    );
}

#[test]
fn from_emptiable_interval() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(EmptiableRelativeInterval::Bound(RelativeInterval::Bounded(
            BoundedRelativeInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2),)
        ))),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableRelativeBoundPair::from(EmptiableRelativeInterval::Empty(EmptyInterval)),
        EmptiableRelativeBoundPair::Empty
    );
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(UnboundedInterval),
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(
        EmptiableRelativeBoundPair::from(EmptyInterval),
        EmptiableRelativeBoundPair::Empty
    );
}

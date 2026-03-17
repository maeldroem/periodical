use jiff::SignedDuration;

use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::relative::{BoundedRelativeInterval, RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeInterval, RelativeStartBound};
use crate::intervals::special::UnboundedInterval;

use super::half_bounded_interval::*;

#[test]
fn interval_new() {
    let interval = HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture);

    assert_eq!(interval.reference(), SignedDuration::from_hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn interval_new_with_inclusivity() {
    let interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.reference(), SignedDuration::from_hours(1));
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn interval_set_reference_time() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference(SignedDuration::from_hours(2));

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn interval_set_reference_time_inclusivity() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );
}

#[test]
fn interval_set_opening_direction() {
    let mut interval = HalfBoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );
}

#[test]
fn interval_from_datetime_opening_direction_pair() {
    assert_eq!(
        HalfBoundedRelativeInterval::from((SignedDuration::from_hours(1), OpeningDirection::ToFuture)),
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn interval_from_pair_of_datetime_bound_inclusivity_pair_and_opening_direction() {
    assert_eq!(
        HalfBoundedRelativeInterval::from((
            (SignedDuration::from_hours(1), BoundInclusivity::Exclusive),
            OpeningDirection::ToPast
        )),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn interval_from_range_from() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(SignedDuration::from_hours(1)..),
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture),
    );
}

#[test]
fn interval_from_range_to() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(..SignedDuration::from_hours(1)),
        HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );
}

#[test]
fn interval_from_range_to_inclusive() {
    assert_eq!(
        HalfBoundedRelativeInterval::from(..=SignedDuration::from_hours(1)),
        HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToPast),
    );
}

#[test]
fn interval_try_from_relative_bounds_correct() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        )),
        Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )),
        )),
        Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn interval_try_from_relative_bounds_wrong() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
        Err(HalfBoundedRelativeIntervalFromRelativeBoundPairError::NotHalfBoundedInterval),
    );
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(2))),
        )),
        Err(HalfBoundedRelativeIntervalFromRelativeBoundPairError::NotHalfBoundedInterval),
    );
}

#[test]
fn interval_try_from_relative_interval_correct() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeInterval::HalfBounded(
            HalfBoundedRelativeInterval::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
        Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn interval_try_from_relative_interval_wrong() {
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeInterval::Unbounded(UnboundedInterval)),
        Err(HalfBoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfBoundedRelativeInterval::try_from(RelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2),
        ))),
        Err(HalfBoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
}

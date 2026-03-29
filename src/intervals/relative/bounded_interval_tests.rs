use std::error::Error;

use jiff::SignedDuration;

use super::bounded_interval::*;
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::relative::{
    HalfBoundedRelativeInterval,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::UnboundedInterval;

#[test]
fn unchecked_new_negative_len() {
    let interval =
        BoundedRelativeInterval::unchecked_new(SignedDuration::from_hours(1), SignedDuration::from_hours(-5));

    assert_eq!(interval.start(), SignedDuration::from_hours(1));
    assert_eq!(interval.end(), SignedDuration::from_hours(-5));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new() {
    let interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

    assert_eq!(interval.start(), SignedDuration::from_hours(1));
    assert_eq!(interval.end(), SignedDuration::from_hours(2));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn unchecked_new_with_inclusivity() {
    let interval = BoundedRelativeInterval::unchecked_new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Inclusive,
        SignedDuration::ZERO,
        BoundInclusivity::Exclusive,
    );

    assert_eq!(interval.start(), SignedDuration::from_hours(1));
    assert_eq!(interval.end(), SignedDuration::ZERO);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn new_with_inclusivity_zero_len() {
    let interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(5),
        BoundInclusivity::Inclusive,
        SignedDuration::from_hours(5),
        BoundInclusivity::Exclusive,
    );

    assert_eq!(interval.start(), SignedDuration::from_hours(5));
    assert_eq!(interval.end(), SignedDuration::from_hours(5),);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(2),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.start(), SignedDuration::from_hours(1));
    assert_eq!(interval.end(), SignedDuration::from_hours(2));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn bounded_relative_set_start() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(2),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(
        interval.set_start(SignedDuration::from_hours(3)),
        Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation),
    );
}

#[test]
fn bounded_relative_set_end() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(2),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(3),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(
        interval.set_end(SignedDuration::from_hours(1)),
        Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation),
    );
}

#[test]
fn bounded_relative_set_start_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(2),
        BoundInclusivity::Inclusive,
    );

    interval.set_start_inclusivity(BoundInclusivity::Inclusive)?;

    assert_eq!(interval.start(), SignedDuration::from_hours(1));
    assert_eq!(interval.end(), SignedDuration::from_hours(2));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn bounded_relative_set_end_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(2),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(3),
        BoundInclusivity::Inclusive,
    );

    interval.set_end_inclusivity(BoundInclusivity::Exclusive)?;

    assert_eq!(interval.start(), SignedDuration::from_hours(2));
    assert_eq!(interval.end(), SignedDuration::from_hours(3));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_datetime_pair() {
    assert_eq!(
        BoundedRelativeInterval::from((SignedDuration::from_hours(2), SignedDuration::from_hours(1))),
        BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ),
    );
}

#[test]
fn from_pair_of_datetime_inclusivity_pairs() {
    assert_eq!(
        BoundedRelativeInterval::from((
            (SignedDuration::from_hours(2), BoundInclusivity::Exclusive),
            (SignedDuration::from_hours(1), BoundInclusivity::Inclusive),
        )),
        BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ),
    );
}

#[test]
fn from_range() {
    assert_eq!(
        BoundedRelativeInterval::from(SignedDuration::from_hours(1)..SignedDuration::from_hours(2)),
        BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn from_range_inclusive() {
    assert_eq!(
        BoundedRelativeInterval::from(SignedDuration::from_hours(1)..=SignedDuration::from_hours(2)),
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2)),
    );
}

#[test]
fn try_from_relative_bounds_correct() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(2),
                BoundInclusivity::Inclusive,
            )),
        )),
        Ok(BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        )),
    );
}

#[test]
fn try_from_relative_bounds_wrong() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
        )),
        Err(BoundedRelativeIntervalFromRelativeBoundPairError::NotBoundedInterval),
    );
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            RelativeEndBound::InfiniteFuture,
        )),
        Err(BoundedRelativeIntervalFromRelativeBoundPairError::NotBoundedInterval),
    );
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::InfiniteFuture,
        )),
        Err(BoundedRelativeIntervalFromRelativeBoundPairError::NotBoundedInterval),
    );
}

#[test]
fn try_from_relative_interval_correct() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2),
        ))),
        Ok(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2),
        )),
    );
}

#[test]
fn try_from_relative_interval_wrong() {
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeInterval::Unbounded(UnboundedInterval)),
        Err(BoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
    assert_eq!(
        BoundedRelativeInterval::try_from(RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            OpeningDirection::ToFuture,
        ))),
        Err(BoundedRelativeIntervalFromRelativeIntervalError::WrongVariant),
    );
}

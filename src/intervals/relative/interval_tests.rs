use jiff::SignedDuration;

use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::relative::{BoundedRelativeInterval, HalfBoundedRelativeInterval, RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::intervals::special::UnboundedInterval;

use super::interval::*;

#[test]
fn relative_interval_from_relative_bounds() {
    assert_eq!(
        RelativeInterval::from(RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        )),
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn relative_interval_from_opt_datetime_pair_unbounded() {
    assert_eq!(
        <RelativeInterval as From<(Option<SignedDuration>, Option<SignedDuration>)>>::from((None, None)),
        RelativeInterval::Unbounded(UnboundedInterval),
    );
}

#[test]
fn relative_interval_from_opt_datetime_pair_half_bounded() {
    assert_eq!(
        RelativeInterval::from((None, Some(SignedDuration::from_hours(1)))),
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn relative_interval_from_opt_datetime_bound_inclusivity_pairs() {
    assert_eq!(
        RelativeInterval::from((
            Some((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
            Some((SignedDuration::from_hours(2), BoundInclusivity::Exclusive)),
        )),
        RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        )),
    );
}

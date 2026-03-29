use jiff::SignedDuration;

use super::emptiable_interval::*;
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    HalfBoundedRelativeInterval,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn relative_interval_from_relative_bounds() {
    assert_eq!(
        EmptiableRelativeInterval::from(RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        )),
        EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn relative_interval_from_emptiable_relative_bounds() {
    assert_eq!(
        EmptiableRelativeInterval::from(EmptiableRelativeBoundPair::Bound(RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::InfiniteFuture,
        ))),
        EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
}

#[test]
fn relative_interval_from_opt_datetime_pair_unbounded() {
    assert_eq!(
        <EmptiableRelativeInterval as From<(Option<SignedDuration>, Option<SignedDuration>)>>::from((None, None)),
        EmptiableRelativeInterval::Unbounded(UnboundedInterval),
    );
}

#[test]
fn relative_interval_from_opt_datetime_pair_half_bounded() {
    assert_eq!(
        EmptiableRelativeInterval::from((None, Some(SignedDuration::from_hours(1)))),
        EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            OpeningDirection::ToPast,
        )),
    );
}

#[test]
fn relative_interval_from_opt_datetime_bound_inclusivity_pairs() {
    assert_eq!(
        EmptiableRelativeInterval::from((
            Some((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
            Some((SignedDuration::from_hours(2), BoundInclusivity::Exclusive)),
        )),
        EmptiableRelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_empty() {
    assert_eq!(
        <EmptiableRelativeInterval as From<(bool, Option<SignedDuration>, Option<SignedDuration>)>>::from((
            true, None, None,
        )),
        EmptiableRelativeInterval::Empty(EmptyInterval),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime() {
    assert_eq!(
        EmptiableRelativeInterval::from((
            false,
            Some(SignedDuration::from_hours(1)),
            Some(SignedDuration::from_hours(2)),
        )),
        EmptiableRelativeInterval::Bounded(BoundedRelativeInterval::new(
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(2)
        )),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_bound_inclusivity_empty() {
    assert_eq!(
        <EmptiableRelativeInterval as From<(
            bool,
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>
        )>>::from((true, None, None,)),
        EmptiableRelativeInterval::Empty(EmptyInterval),
    );
}

#[test]
fn relative_interval_from_bool_and_two_opt_datetime_bound_inclusivity() {
    assert_eq!(
        EmptiableRelativeInterval::from((
            false,
            Some((SignedDuration::from_hours(1), BoundInclusivity::Exclusive)),
            Some((SignedDuration::from_hours(2), BoundInclusivity::Exclusive)),
        )),
        EmptiableRelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        )),
    );
}

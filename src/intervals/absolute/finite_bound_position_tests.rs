use std::ops::Bound;

use super::finite_bound_position::*;
use crate::intervals::absolute::{AbsEndBound, AbsStartBound};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::test_data::date_timestamp;

#[test]
fn new() {
    let time = date_timestamp(2025, 1, 1);
    let abs_finite_bound_position = AbsFiniteBoundPos::new(time);

    assert_eq!(abs_finite_bound_position.time(), time);
    assert_eq!(abs_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn new_with_inclusivity() {
    let time = date_timestamp(2025, 1, 1);
    let abs_finite_bound_position = AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive);

    assert_eq!(abs_finite_bound_position.time(), time);
    assert_eq!(abs_finite_bound_position.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn time() {
    let time = date_timestamp(2026, 1, 1);
    let interval = AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive);

    assert_eq!(interval.time(), time);
}

#[test]
fn set_time() {
    let mut abs_finite_bound_position = AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1));
    let new_time = date_timestamp(2025, 5, 1);

    abs_finite_bound_position.set_time(new_time);

    assert_eq!(abs_finite_bound_position.time(), new_time);
}

#[test]
fn set_inclusivity() {
    let mut abs_finite_bound_position =
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive);

    abs_finite_bound_position.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(abs_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn to_start_bound() {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound(),
        AbsStartBound::Finite(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_finite_start_bound()
        )
    );
}

#[test]
fn to_end_bound() {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_end_bound(),
        AbsEndBound::Finite(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_finite_end_bound()
        )
    );
}

#[test]
fn inclusivity() {
    let inclusive = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive);
    let exclusive = AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive);

    assert_eq!(inclusive.inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(exclusive.inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn from_timestamp() {
    assert_eq!(
        AbsFiniteBoundPos::from(date_timestamp(2025, 1, 1)),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Inclusive,),
    );
}

#[test]
fn from_timestamp_inclusivity_pair() {
    assert_eq!(
        AbsFiniteBoundPos::from((date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive)),
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,),
    );
}

#[test]
fn try_from_bound() {
    assert_eq!(
        AbsFiniteBoundPos::try_from(Bound::Included(date_timestamp(2025, 1, 1))),
        Ok(AbsFiniteBoundPos::new_with_incl(
            date_timestamp(2025, 1, 1),
            BoundInclusivity::Inclusive
        )),
    );
    assert_eq!(
        AbsFiniteBoundPos::try_from(Bound::Excluded(date_timestamp(2025, 1, 1))),
        Ok(AbsFiniteBoundPos::new_with_incl(
            date_timestamp(2025, 1, 1),
            BoundInclusivity::Exclusive
        )),
    );
    assert_eq!(
        AbsFiniteBoundPos::try_from(Bound::Unbounded),
        Err(AbsFiniteBoundPosTryFromBoundError),
    );
}

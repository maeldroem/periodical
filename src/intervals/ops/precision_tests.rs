use chrono::{Duration, Utc};

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::Precision;
use crate::test_utils::{date, datetime};

use super::precision::*;

#[test]
fn precise_finite_bound() {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(datetime(&Utc, 2025, 1, 1, 10, 42, 31), BoundInclusivity::Exclusive,)
            .precise_bound(Precision::ToNearest(Duration::minutes(5))),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 10, 45, 0),
            BoundInclusivity::Exclusive,
        )),
    );
}

#[test]
fn precise_start_infinite() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.precise_bound(Precision::ToFuture(Duration::minutes(5))),
        Ok(AbsoluteStartBound::InfinitePast),
    );
}

#[test]
fn precise_start_common_precision() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 2, 23, 44),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound(Precision::ToFuture(Duration::minutes(5))),
        Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 2, 25, 0),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn precise_start_uncommon_precision_with_base() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 2, 23, 44),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound_with_base_time(
            Precision::ToFuture(Duration::minutes(7) + Duration::seconds(31)),
            date(&Utc, 2025, 1, 1),
        ),
        Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 2, 30, 20),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn precise_end_infinite() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.precise_bound(Precision::ToFuture(Duration::minutes(5))),
        Ok(AbsoluteEndBound::InfiniteFuture),
    );
}

#[test]
fn precise_end_common_precision() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 9, 56, 21),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound(Precision::ToFuture(Duration::minutes(5))),
        Ok(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 10, 0, 0),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn precise_end_uncommon_precision_with_base() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 9, 56, 21),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound_with_base_time(
            Precision::ToFuture(Duration::minutes(7) + Duration::seconds(31)),
            date(&Utc, 2025, 1, 1),
        ),
        Ok(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            datetime(&Utc, 2025, 1, 1, 10, 1, 20),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn precise_abs_bounds_same_precision() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 2, 23, 44),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 9, 56, 21),
                BoundInclusivity::Exclusive,
            )),
        )
        .precise_interval(Precision::ToFuture(Duration::minutes(5))),
        Ok(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 2, 25, 0),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 10, 0, 0),
                BoundInclusivity::Exclusive,
            )),
        )),
    );
}

#[test]
fn precise_abs_bounds_different_precisions() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 2, 23, 44),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 9, 56, 21),
                BoundInclusivity::Exclusive,
            )),
        )
        .precise_interval_with_different_precisions(
            Precision::ToFuture(Duration::minutes(5)),
            Precision::ToPast(Duration::minutes(5)),
        ),
        Ok(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 2, 25, 0),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                datetime(&Utc, 2025, 1, 1, 9, 55, 0),
                BoundInclusivity::Exclusive,
            )),
        )),
    );
}

#[test]
fn precise_start_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.precise_interval(Precision::ToFuture(Duration::minutes(5))),
        Ok(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn precise_end_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.precise_interval(Precision::ToFuture(Duration::minutes(5))),
        Ok(EmptiableAbsoluteBounds::Empty),
    );
}

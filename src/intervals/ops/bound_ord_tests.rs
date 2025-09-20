use chrono::{Duration, Utc};

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::prelude::BoundOverlapAmbiguity;
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::test_utils::date;

use super::bound_ord::*;

#[test]
fn bound_cmp_abs_start_start_less_inf_past_finite() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.bound_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_start_start_less_finite_finite() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_start_start_equal_inf_past() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.bound_cmp(&AbsoluteStartBound::InfinitePast),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn bound_cmp_abs_start_start_equal_inclusive_inclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_start_equal_inclusive_exclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            ))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_start_equal_exclusive_inclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_start_equal_exclusive_exclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_start_greater_finite_inf_past() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .bound_cmp(&AbsoluteStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_abs_start_start_greater_finite_finite() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_abs_start_end_less_inf_past_inf_future() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.bound_cmp(&AbsoluteEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_start_end_less_inf_past_finite() {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.bound_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_start_end_less_finite_inf_future() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .bound_cmp(&AbsoluteEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_start_end_less_finite_finite() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_start_end_equal_inclusive_inclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_end_equal_inclusive_exclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            ))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_end_equal_exclusive_inclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_end_equal_exclusive_exclusive() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_start_end_greater() {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))).bound_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_abs_end_start_less() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_end_start_equal_inclusive_inclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_end_start_equal_inclusive_exclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            ))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_end_start_equal_exclusive_inclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_end_start_equal_exclusive_exclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_end_start_greater_inf_future_inf_past() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.bound_cmp(&AbsoluteStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_abs_end_start_greater_inf_future_finite() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.bound_cmp(&AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_abs_end_start_greater_finite_inf_past() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .bound_cmp(&AbsoluteStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_abs_end_start_greater_finite_finite() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))).bound_cmp(
            &AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_abs_end_end_less_finite_inf_future() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
            .bound_cmp(&AbsoluteEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_end_end_less_finite_finite() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_abs_end_end_equal_inf_future_inf_future() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.bound_cmp(&AbsoluteEndBound::InfiniteFuture),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn bound_cmp_abs_end_end_equal_inclusive_inclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_end_end_equal_inclusive_exclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))).bound_cmp(
            &AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            ))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_end_end_equal_exclusive_inclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_abs_end_end_equal_exclusive_exclusive() {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_start_less_inf_past_finite() {
    assert_eq!(
        RelativeStartBound::InfinitePast.bound_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new(
            Duration::hours(101)
        ))),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_start_start_less_finite_finite() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(102)))
        ),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_start_start_equal_inf_past() {
    assert_eq!(
        RelativeStartBound::InfinitePast.bound_cmp(&RelativeStartBound::InfinitePast),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn bound_cmp_rel_start_start_equal_inclusive_inclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_start_equal_inclusive_exclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(101),
                BoundInclusivity::Exclusive,
            ))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_start_equal_exclusive_inclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            101
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_start_equal_exclusive_exclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_start_greater_finite_inf_past() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
            .bound_cmp(&RelativeStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_rel_start_start_greater_finite_finite() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(102))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
        ),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_rel_start_end_less_inf_past_inf_future() {
    assert_eq!(
        RelativeStartBound::InfinitePast.bound_cmp(&RelativeEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_start_end_less_inf_past_finite() {
    assert_eq!(
        RelativeStartBound::InfinitePast.bound_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(
            Duration::hours(101)
        ))),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_start_end_less_finite_inf_future() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
            .bound_cmp(&RelativeEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_start_end_less_finite_finite() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(102)))
        ),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_start_end_equal_inclusive_inclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_end_equal_inclusive_exclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(101),
                BoundInclusivity::Exclusive,
            ))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_end_equal_exclusive_inclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(
            101
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_end_equal_exclusive_exclusive() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_start_end_greater() {
    assert_eq!(
        RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(102))).bound_cmp(
            &RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
        ),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_rel_end_start_less() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(102)))
        ),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_end_start_equal_inclusive_inclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_end_start_equal_inclusive_exclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(101),
                BoundInclusivity::Exclusive,
            ))
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_end_start_equal_exclusive_inclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            101
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_end_start_equal_exclusive_exclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_end_start_greater_inf_future_inf_past() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.bound_cmp(&RelativeStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_rel_end_start_greater_inf_future_finite() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.bound_cmp(&RelativeStartBound::Finite(RelativeFiniteBound::new(
            Duration::hours(101)
        ))),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_rel_end_start_greater_finite_inf_past() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
            .bound_cmp(&RelativeStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_rel_end_start_greater_finite_finite() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(102))).bound_cmp(
            &RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
        ),
        BoundOrdering::Greater,
    );
}

#[test]
fn bound_cmp_rel_end_end_less_finite_inf_future() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))
            .bound_cmp(&RelativeEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_end_end_less_finite_finite() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(&RelativeEndBound::Finite(
            RelativeFiniteBound::new(Duration::hours(102))
        )),
        BoundOrdering::Less,
    );
}

#[test]
fn bound_cmp_rel_end_end_equal_inf_future_inf_future() {
    assert_eq!(
        RelativeEndBound::InfiniteFuture.bound_cmp(&RelativeEndBound::InfiniteFuture),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn bound_cmp_rel_end_end_equal_inclusive_inclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(&RelativeEndBound::Finite(
            RelativeFiniteBound::new(Duration::hours(101))
        )),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_end_end_equal_inclusive_exclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101))).bound_cmp(&RelativeEndBound::Finite(
            RelativeFiniteBound::new_with_inclusivity(Duration::hours(101), BoundInclusivity::Exclusive,)
        )),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_end_end_equal_exclusive_inclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(
            101
        )))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn bound_cmp_rel_end_end_equal_exclusive_exclusive() {
    assert_eq!(
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))
        .bound_cmp(&RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(101),
            BoundInclusivity::Exclusive,
        ))),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

use chrono::Utc;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::OpenInterval;
use crate::test_utils::date;

use super::remove_overlap_or_gap::*;

#[test]
fn overlap_or_gap_removal_result_is_single() {
    assert!(OverlapOrGapRemovalResult::Single(()).is_single());
    assert!(!OverlapOrGapRemovalResult::Split((), ()).is_single());
}

#[test]
fn overlap_or_gap_removal_result_is_split() {
    assert!(!OverlapOrGapRemovalResult::Single(()).is_split());
    assert!(OverlapOrGapRemovalResult::Split((), ()).is_split());
}

#[test]
fn overlap_or_gap_removal_result_single_opt() {
    assert_eq!(OverlapOrGapRemovalResult::Single(10).single(), Some(10));
    assert_eq!(OverlapOrGapRemovalResult::Split(10, 20).single(), None);
}

#[test]
fn overlap_or_gap_removal_result_split_opt() {
    assert_eq!(OverlapOrGapRemovalResult::Single(10).split(), None);
    assert_eq!(OverlapOrGapRemovalResult::Split(10, 20).split(), Some((10, 20)));
}

#[test]
fn overlap_or_gap_removal_result_map() {
    assert_eq!(
        OverlapOrGapRemovalResult::Single(10).map(|x| x + 10),
        OverlapOrGapRemovalResult::Single(20)
    );
    assert_eq!(
        OverlapOrGapRemovalResult::Split(10, 20).map(|x| x + 10),
        OverlapOrGapRemovalResult::Split(20, 30)
    );
}

#[test]
fn remove_overlap_or_gap_empty_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.remove_overlap_or_gap(&EmptiableAbsoluteBounds::Empty),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn remove_overlap_or_gap_empty_open() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn remove_overlap_or_gap_open_empty() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .remove_overlap_or_gap(&EmptiableAbsoluteBounds::Empty),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        ))),
    );
}

#[test]
fn remove_overlap_or_gap_open_open() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).remove_overlap_or_gap(
            &AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
        ),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn remove_overlap_or_gap_gap_between_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        )
        .remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
        )),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Exclusive,
            )),
        ))),
    );
}

#[test]
fn remove_overlap_or_gap_overlap_between_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
        )
        .remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
        )),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        ))),
    );
}

#[test]
fn remove_overlap_or_gap_closed_adjacent_inclusive_inclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        )
        .remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        ))),
    );
}

#[test]
fn remove_overlap_or_gap_closed_adjacent_inclusive_exclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        )
        .remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        ))),
    );
}

#[test]
fn remove_overlap_or_gap_closed_adjacent_exclusive_inclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        )
        .remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        ))),
    );
}

#[test]
fn remove_overlap_or_gap_closed_adjacent_exclusive_exclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        )
        .remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        ))),
    );
}

#[test]
fn remove_overlap_or_gap_closed_on_open() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        )
        .remove_overlap_or_gap(&OpenInterval),
        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn remove_overlap_or_gap_open_on_closed() {
    assert_eq!(
        OpenInterval.remove_overlap_or_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        )),
        OverlapOrGapRemovalResult::Split(
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

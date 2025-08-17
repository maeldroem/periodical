use chrono::Utc;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::prelude::{AbsoluteBounds, EmptiableAbsoluteBounds};
use crate::test_utils::date;

use super::remove_overlap::*;

#[test]
fn overlap_removal_result_is_single() {
    assert!(OverlapRemovalResult::Single(()).is_single());
    assert!(!OverlapRemovalResult::Split((), ()).is_single());
}

#[test]
fn overlap_removal_result_is_split() {
    assert!(!OverlapRemovalResult::Single(()).is_split());
    assert!(OverlapRemovalResult::Split((), ()).is_split());
}

#[test]
fn overlap_removal_result_single_opt() {
    assert_eq!(OverlapRemovalResult::Single(10).single(), Some(10));
    assert_eq!(OverlapRemovalResult::Split(10, 20).single(), None);
}

#[test]
fn overlap_removal_result_split_opt() {
    assert_eq!(OverlapRemovalResult::Single(10).split(), None);
    assert_eq!(OverlapRemovalResult::Split(10, 20).split(), Some((10, 20)));
}

#[test]
fn overlap_removal_result_map() {
    assert_eq!(OverlapRemovalResult::Single(10).map(|x| x + 10), OverlapRemovalResult::Single(20));
    assert_eq!(OverlapRemovalResult::Split(10, 20).map(|x| x + 10), OverlapRemovalResult::Split(20, 30));
}

#[test]
fn remove_overlap_empty_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.remove_overlap(&EmptiableAbsoluteBounds::Empty),
        Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty)),
    );
}

#[test]
fn remove_overlap_empty_open() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty)),
    );
}

#[test]
fn remove_overlap_open_empty() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )
            .remove_overlap(&EmptiableAbsoluteBounds::Empty),
        Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )))),
    );
}

#[test]
fn remove_overlap_open_open() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty)),
    );
}

#[test]
fn remove_overlap_closed_no_overlap() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        )
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
            )),
        Err(OverlapRemovalErr::NoOverlap),
    );
}

#[test]
fn remove_overlap_closed_adjacent_inclusive_inclusive() {
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
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                )),
            )),
        Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        )))),
    );
}

#[test]
fn remove_overlap_closed_adjacent_inclusive_exclusive() {
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
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                )),
            )),
        Err(OverlapRemovalErr::NoOverlap),
    );
}

#[test]
fn remove_overlap_closed_adjacent_exclusive_inclusive() {
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
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                )),
            )),
        Err(OverlapRemovalErr::NoOverlap),
    );
}

#[test]
fn remove_overlap_closed_adjacent_exclusive_exclusive() {
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
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                )),
            )),
        Err(OverlapRemovalErr::NoOverlap),
    );
}

#[test]
fn remove_overlap_closed_overlap() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                )),
            )),
        Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        )))),
    );
}

#[test]
fn remove_overlap_closed_on_open() {
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
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBounds::Empty)),
    );
}

#[test]
fn remove_overlap_open_on_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )
            .remove_overlap(&AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                )),
            )),
        Ok(OverlapRemovalResult::Split(
            EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                )),
            )),
            EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::InfiniteFuture,
            )),
        )),
    );
}

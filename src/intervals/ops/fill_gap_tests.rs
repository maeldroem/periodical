use chrono::Utc;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfOpenAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::test_utils::date;

use super::fill_gap::*;

#[test]
fn fill_gap_emptiable_abs_bounds_empty_abs_bounds_open() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.fill_gap(&AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
        Ok(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        ))),
    );
}

#[test]
fn fill_gap_abs_bounds_open_emptiable_abs_bounds_empty() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .fill_gap(&EmptiableAbsoluteBounds::Empty),
        Ok(AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture
        )),
    );
}

#[test]
fn fill_gap_emptiable_abs_bounds_empty_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.fill_gap(&EmptiableAbsoluteBounds::Empty),
        Ok(EmptiableAbsoluteBounds::Empty),
    );
}

#[test]
fn fill_gap_two_overlapping_half_open() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 2), OpeningDirection::ToPast).fill_gap(
            &HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture)
        ),
        Err(GapFillError::Overlap),
    );
}

#[test]
fn fill_gap_two_non_overlapping_half_open() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToPast).fill_gap(
            &HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 2), OpeningDirection::ToFuture)
        ),
        Ok(AbsoluteInterval::HalfOpen(
            HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
    );
}

#[test]
fn fill_gap_two_strictly_adjacent_half_open() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToPast).fill_gap(
            &HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture)
        ),
        Err(GapFillError::Overlap),
    );
}

#[test]
fn fill_gap_two_leniently_adjacent_half_open() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .fill_gap(&HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToFuture
        )),
        Ok(AbsoluteInterval::HalfOpen(
            HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
    );
}

#[test]
fn fill_gap_two_very_leniently_adjacent_half_open() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
        .fill_gap(&HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
        Ok(AbsoluteInterval::HalfOpen(
            HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )
        )),
    );
}

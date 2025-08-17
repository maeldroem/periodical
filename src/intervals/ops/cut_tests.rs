use chrono::{DateTime, Utc};

use crate::intervals::absolute::{
    AbsoluteInterval, ClosedAbsoluteInterval, EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::test_utils::date;

use super::cut::*;

#[test]
fn cut_type_past_bound_inclusivity() {
    assert_eq!(
        CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive).past_bound_inclusivity(),
        BoundInclusivity::Inclusive,
    );
    assert_eq!(
        CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive).past_bound_inclusivity(),
        BoundInclusivity::Exclusive,
    );
}

#[test]
fn cut_type_future_bound_inclusivity() {
    assert_eq!(
        CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive).future_bound_inclusivity(),
        BoundInclusivity::Exclusive,
    );
    assert_eq!(
        CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive).future_bound_inclusivity(),
        BoundInclusivity::Inclusive,
    );
}

#[test]
fn cut_type_opposite() {
    assert_eq!(
        CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive).opposite(),
        CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive),
    );
}

#[test]
fn cut_type_from_bound_inclusivity_pair() {
    assert_eq!(
        CutType::from((BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)),
        CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive),
    );
}

#[test]
fn cut_result_is_uncut() {
    assert!(CutResult::<()>::Uncut.is_uncut());
    assert!(!CutResult::Cut((), ()).is_uncut());
}

#[test]
fn cut_result_is_cut() {
    assert!(!CutResult::<()>::Uncut.is_cut());
    assert!(CutResult::Cut((), ()).is_cut());
}

#[test]
fn cut_result_cut_opt() {
    assert_eq!(CutResult::<u8>::Uncut.cut(), None);
    assert_eq!(CutResult::<u8>::Cut(10, 20).cut(), Some((10, 20)));
}

#[test]
fn cut_result_map_cut() {
    assert_eq!(
        CutResult::<u8>::Cut(10, 20).map_cut(|a, b| (a + 10, b + 20)),
        CutResult::Cut(20, 40)
    );
}

#[test]
fn cut_at_empty_interval() {
    assert_eq!(
        <EmptyInterval as Cuttable<DateTime<Utc>>>::cut_at(
            &EmptyInterval,
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
        ),
        CutResult::Uncut,
    );
}

#[test]
fn cut_at_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
        ),
        CutResult::Uncut,
    );
}

#[test]
fn cut_at_open_interval_inclusive_inclusive_cut() {
    assert_eq!(
        OpenInterval.cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
        ),
        CutResult::Cut(
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

#[test]
fn cut_at_open_interval_inclusive_exclusive_cut() {
    assert_eq!(
        OpenInterval.cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
        ),
        CutResult::Cut(
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

#[test]
fn cut_at_open_interval_exclusive_inclusive_cut() {
    assert_eq!(
        OpenInterval.cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
        ),
        CutResult::Cut(
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

#[test]
fn cut_at_open_interval_exclusive_exclusive_cut() {
    assert_eq!(
        OpenInterval.cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
        ),
        CutResult::Cut(
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

#[test]
fn cut_at_half_open_interval() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture).cut_at(
            date(&Utc, 2025, 1, 2),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
        ),
        CutResult::Cut(
            AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )),
        ),
    );
}

#[test]
fn cut_at_outside_before_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 2), date(&Utc, 2025, 1, 3)).cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
        ),
        CutResult::Uncut,
    );
}

#[test]
fn cut_at_outside_after_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 2), date(&Utc, 2025, 1, 3)).cut_at(
            date(&Utc, 2025, 1, 4),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
        ),
        CutResult::Uncut,
    );
}

#[test]
fn cut_at_inside_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 3)).cut_at(
            date(&Utc, 2025, 1, 2),
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
        ),
        CutResult::Cut(
            AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        ),
    );
}

#[test]
fn cut_at_inclusive_edge_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
        ),
        CutResult::Cut(
            AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteInterval::Closed(ClosedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
        ),
    );
}

#[test]
fn cut_at_inclusive_edge_closed_interval_would_create_illegal_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)).cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
        ),
        CutResult::Uncut,
    );
}

#[test]
fn cut_at_exclusive_edge_closed_interval() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
        .cut_at(
            date(&Utc, 2025, 1, 1),
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
        ),
        CutResult::Uncut,
    );
}

use chrono::Utc;

use crate::intervals::absolute::{AbsoluteInterval, BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
use crate::intervals::meta::OpeningDirection;
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::test_utils::date;

use super::remove_empty::*;

#[test]
fn create_remove_empty_intervals_iter() {
    let intervals = [
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToPast,
        )),
    ];

    intervals.remove_empty_intervals();
}

#[test]
fn remove_empty_intervals_iter_run() {
    let intervals = [
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToPast,
        )),
        AbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::Unbounded(UnboundedInterval),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                date(&Utc, 2025, 1, 2)
            )),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                OpeningDirection::ToPast
            )),
        ],
    );
}

#[test]
fn remove_empty_intervals_iter_run_reverse() {
    let intervals = [
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToPast,
        )),
        AbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().rev().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                OpeningDirection::ToPast
            )),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                date(&Utc, 2025, 1, 2)
            )),
            AbsoluteInterval::Unbounded(UnboundedInterval),
        ],
    );
}

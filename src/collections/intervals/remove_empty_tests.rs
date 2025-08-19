use chrono::Utc;

use crate::intervals::absolute::{AbsoluteInterval, ClosedAbsoluteInterval, HalfOpenAbsoluteInterval};
use crate::intervals::meta::OpeningDirection;
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::test_utils::date;

use super::remove_empty::*;

#[test]
fn create_remove_empty_intervals_iter() {
    let intervals = [
        AbsoluteInterval::Open(OpenInterval),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToPast,
        )),
    ];

    intervals.remove_empty_intervals();
}

#[test]
fn remove_empty_intervals_iter_run() {
    let intervals = [
        AbsoluteInterval::Open(OpenInterval),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToPast,
        )),
        AbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::Open(OpenInterval),
            AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                date(&Utc, 2025, 1, 2)
            )),
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                OpeningDirection::ToPast
            )),
        ],
    );
}

#[test]
fn remove_empty_intervals_iter_run_reverse() {
    let intervals = [
        AbsoluteInterval::Open(OpenInterval),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::Empty(EmptyInterval),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            OpeningDirection::ToPast,
        )),
        AbsoluteInterval::Empty(EmptyInterval),
    ];

    assert_eq!(
        intervals.remove_empty_intervals().rev().collect::<Vec<_>>(),
        vec![
            AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                OpeningDirection::ToPast
            )),
            AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                date(&Utc, 2025, 1, 1),
                date(&Utc, 2025, 1, 2)
            )),
            AbsoluteInterval::Open(OpenInterval),
        ],
    );
}

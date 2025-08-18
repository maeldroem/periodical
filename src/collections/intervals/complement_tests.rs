use chrono::Utc;

use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::ops::ComplementResult;
use crate::prelude::{AbsoluteInterval, ClosedAbsoluteInterval, HalfOpenAbsoluteInterval};
use crate::test_utils::date;

use super::complement::*;

#[test]
fn create_complement_iter() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Open(OpenInterval),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 5),
            OpeningDirection::ToFuture,
        )),
    ];

    intervals.complement();
}

#[test]
fn complement_iter_run() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Open(OpenInterval),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 5),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().collect::<Vec<_>>(),
        vec![
            ComplementResult::Split(
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
            ComplementResult::Single(AbsoluteInterval::Empty(EmptyInterval)),
            ComplementResult::Single(AbsoluteInterval::HalfOpen(
                HalfOpenAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 5),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )
            ),),
        ],
    );
}

#[test]
fn complement_iter_run_reverse() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Open(OpenInterval),
        AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new(
            date(&Utc, 2025, 1, 5),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().rev().collect::<Vec<_>>(),
        vec![
            ComplementResult::Single(AbsoluteInterval::HalfOpen(
                HalfOpenAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 5),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )
            ),),
            ComplementResult::Single(AbsoluteInterval::Empty(EmptyInterval)),
            ComplementResult::Split(
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfOpen(HalfOpenAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
        ],
    );
}

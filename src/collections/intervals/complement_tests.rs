use chrono::Utc;

use crate::intervals::absolute::{AbsoluteInterval, BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::ComplementResult;
use crate::test_utils::date;

use super::complement::*;

#[test]
fn create_complement_iter() {
    let intervals = [
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 5),
            OpeningDirection::ToFuture,
        )),
    ];

    intervals.complement();
}

#[test]
fn complement_iter_run() {
    let intervals = [
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 5),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().collect::<Vec<_>>(),
        vec![
            ComplementResult::Split(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
            ComplementResult::Single(AbsoluteInterval::Empty(EmptyInterval)),
            ComplementResult::Single(AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(
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
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        )),
        AbsoluteInterval::Unbounded(UnboundedInterval),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 5),
            OpeningDirection::ToFuture,
        )),
    ];

    assert_eq!(
        intervals.complement().rev().collect::<Vec<_>>(),
        vec![
            ComplementResult::Single(AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 5),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )
            ),),
            ComplementResult::Single(AbsoluteInterval::Empty(EmptyInterval)),
            ComplementResult::Split(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
        ],
    );
}

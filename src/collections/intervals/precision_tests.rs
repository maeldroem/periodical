use chrono::{Duration, Utc};

use crate::intervals::absolute::{AbsoluteInterval, ClosedAbsoluteInterval};
use crate::ops::Precision;
use crate::test_utils::datetime;

use super::precision::*;

#[test]
fn create_precision_change_iter_from_change_precision() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 1, 8, 59, 1),
            datetime(&Utc, 2025, 1, 1, 10, 23, 12),
        )),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 2, 8, 59, 1),
            datetime(&Utc, 2025, 1, 2, 10, 23, 12),
        )),
    ];

    intervals.change_precision(Precision::ToNearest(Duration::minutes(5)));
}

#[test]
fn create_precision_change_iter_from_change_start_end_precision() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 1, 8, 59, 1),
            datetime(&Utc, 2025, 1, 1, 10, 23, 12),
        )),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 2, 8, 59, 1),
            datetime(&Utc, 2025, 1, 2, 10, 23, 12),
        )),
    ];

    intervals.change_start_end_precision(
        Precision::ToNearest(Duration::minutes(5)),
        Precision::ToFuture(Duration::minutes(10)),
    );
}

#[test]
fn precision_change_iter_from_change_precision_run() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 1, 8, 23, 12),
            datetime(&Utc, 2025, 1, 1, 10, 50, 1),
        )),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 2, 8, 23, 12),
            datetime(&Utc, 2025, 1, 2, 10, 50, 1),
        )),
    ];

    assert_eq!(
        intervals
            .change_precision(Precision::ToNearest(Duration::minutes(5)))
            .collect::<Vec<_>>(),
        vec![
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 1, 8, 25, 0),
                datetime(&Utc, 2025, 1, 1, 10, 50, 0),
            ))),
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 2, 8, 25, 0),
                datetime(&Utc, 2025, 1, 2, 10, 50, 0),
            ))),
        ],
    );
}

#[test]
fn precision_change_iter_from_change_precision_run_reverse() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 1, 8, 23, 12),
            datetime(&Utc, 2025, 1, 1, 10, 50, 1),
        )),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 2, 8, 23, 12),
            datetime(&Utc, 2025, 1, 2, 10, 50, 1),
        )),
    ];

    assert_eq!(
        intervals
            .change_precision(Precision::ToNearest(Duration::minutes(5)))
            .rev()
            .collect::<Vec<_>>(),
        vec![
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 2, 8, 25, 0),
                datetime(&Utc, 2025, 1, 2, 10, 50, 0),
            ))),
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 1, 8, 25, 0),
                datetime(&Utc, 2025, 1, 1, 10, 50, 0),
            ))),
        ],
    );
}

#[test]
fn precision_change_iter_from_change_start_end_precision_run() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 1, 8, 23, 12),
            datetime(&Utc, 2025, 1, 1, 10, 50, 1),
        )),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 2, 8, 23, 12),
            datetime(&Utc, 2025, 1, 2, 10, 50, 1),
        )),
    ];

    assert_eq!(
        intervals
            .change_start_end_precision(
                Precision::ToNearest(Duration::minutes(5)),
                Precision::ToFuture(Duration::minutes(10)),
            )
            .collect::<Vec<_>>(),
        vec![
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 1, 8, 25, 0),
                datetime(&Utc, 2025, 1, 1, 11, 0, 0),
            ))),
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 2, 8, 25, 0),
                datetime(&Utc, 2025, 1, 2, 11, 0, 0),
            ))),
        ],
    );
}

#[test]
fn precision_change_iter_from_change_start_end_precision_run_reverse() {
    let intervals = [
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 1, 8, 23, 12),
            datetime(&Utc, 2025, 1, 1, 10, 50, 1),
        )),
        AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            datetime(&Utc, 2025, 1, 2, 8, 23, 12),
            datetime(&Utc, 2025, 1, 2, 10, 50, 1),
        )),
    ];

    assert_eq!(
        intervals
            .change_start_end_precision(
                Precision::ToNearest(Duration::minutes(5)),
                Precision::ToFuture(Duration::minutes(10)),
            )
            .rev()
            .collect::<Vec<_>>(),
        vec![
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 2, 8, 25, 0),
                datetime(&Utc, 2025, 1, 2, 11, 0, 0),
            ))),
            Ok(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
                datetime(&Utc, 2025, 1, 1, 8, 25, 0),
                datetime(&Utc, 2025, 1, 1, 11, 0, 0),
            ))),
        ],
    );
}

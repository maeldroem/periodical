use chrono::{Duration, Utc};

use crate::ops::*;
use crate::test_utils::datetime;

#[test]
fn precision_round_to_nearest_classic() {
    let precision = Precision::ToNearest(Duration::hours(2));

    /*
    00:00
    02:00
    04:00
    06:00
    */

    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 4, 10, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 4, 0, 0),
        "To nearest - Rounding down",
    );
    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 5, 0, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 0, 0),
        "To nearest - Rounding up when perfectly in the middle",
    );
    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 5, 45, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 0, 0),
        "To nearest - Rounding up",
    );
}

#[test]
fn precision_round_to_nearest_uncommon() {
    let precision = Precision::ToNearest(Duration::hours(1) + Duration::minutes(17));

    /*
    (From Unix epoch)
    00:00
    01:17
    02:34
    03:51
    05:08
    06:25
    */

    assert_eq!(
        precision.precise_time(datetime(&Utc, 1970, 1, 1, 5, 15, 0)).unwrap(),
        datetime(&Utc, 1970, 1, 1, 5, 8, 0),
        "To nearest - Rounding down",
    );
    assert_eq!(
        precision.precise_time(datetime(&Utc, 1970, 1, 1, 5, 46, 30)).unwrap(),
        datetime(&Utc, 1970, 1, 1, 6, 25, 0),
        "To nearest - Rounding up when perfectly in the middle",
    );
    assert_eq!(
        precision.precise_time(datetime(&Utc, 1970, 1, 1, 6, 0, 0)).unwrap(),
        datetime(&Utc, 1970, 1, 1, 6, 25, 0),
        "To nearest - Rounding up",
    );
}

#[test]
fn precision_round_to_future_classic() {
    let precision = Precision::ToFuture(Duration::hours(2));

    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 4, 1, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 0, 0),
    );
}

#[test]
fn precision_round_to_future_uncommon() {
    let precision = Precision::ToFuture(Duration::hours(1) + Duration::minutes(17));

    /*
    (From Unix epoch)
    00:00
    01:17
    02:34
    03:51
    05:08
    06:25
    */

    assert_eq!(
        precision.precise_time(datetime(&Utc, 1970, 1, 1, 3, 53, 0)).unwrap(),
        datetime(&Utc, 1970, 1, 1, 5, 8, 0),
    );
}

#[test]
fn precision_round_to_past_classic() {
    let precision = Precision::ToPast(Duration::hours(2));

    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 5, 59, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 4, 0, 0),
    );
}

#[test]
fn precision_round_to_past_uncommon() {
    let precision = Precision::ToPast(Duration::hours(1) + Duration::minutes(17));

    /*
    (From Unix epoch)
    00:00
    01:17
    02:34
    03:51
    05:08
    06:25
    */

    assert_eq!(
        precision.precise_time(datetime(&Utc, 1970, 1, 1, 5, 7, 0)).unwrap(),
        datetime(&Utc, 1970, 1, 1, 3, 51, 0),
    );
}

#[test]
fn precision_with_base_round_to_nearest_classic() {
    let precision = Precision::ToNearest(Duration::hours(2));

    /*
    00:00
    02:00
    04:00
    06:00
    */

    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 4, 10, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 4, 0, 0),
        "To nearest - Rounding down",
    );
    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 5, 0, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 0, 0),
        "To nearest - Rounding up when perfectly in the middle",
    );
    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 5, 45, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 0, 0),
        "To nearest - Rounding up",
    );
}

#[test]
fn precision_with_base_time_round_to_nearest_uncommon() {
    let precision = Precision::ToNearest(Duration::hours(1) + Duration::minutes(17));
    let base = datetime(&Utc, 2025, 1, 1, 0, 11, 0);

    /*
    (from base time)
    00:11
    01:28
    02:45
    04:02
    05:19
    06:36
    */

    assert_eq!(
        precision.precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 5, 30, 0), base).unwrap(),
        datetime(&Utc, 2025, 1, 1, 5, 19, 0),
        "To nearest - Rounding down",
    );
    assert_eq!(
        precision.precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 5, 57, 30), base).unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 36, 0),
        "To nearest - Rounding up when perfectly in the middle",
    );
    assert_eq!(
        precision.precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 6, 0, 0), base).unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 36, 0),
        "To nearest - Rounding up",
    );
}

#[test]
fn precision_with_base_time_round_to_future_classic() {
    let precision = Precision::ToFuture(Duration::minutes(30));
    let base = datetime(&Utc, 2025, 1, 1, 0, 0, 0);

    assert_eq!(
        precision.precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 4, 5, 0), base).unwrap(),
        datetime(&Utc, 2025, 1, 1, 4, 30, 0),
    );
}

#[test]
fn precision_with_base_time_round_to_future_uncommon() {
    let precision = Precision::ToFuture(Duration::minutes(25));
    let base = datetime(&Utc, 2025, 1, 1, 0, 0, 0);

    /*
    00:00
    00:25
    00:50
    01:15
    01:40
    02:05
    02:30
    02:55
    03:20
    */

    assert_eq!(
        precision.precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 2, 10, 0), base).unwrap(),
        datetime(&Utc, 2025, 1, 1, 2, 30, 0),
    );
}

#[test]
fn precision_with_base_time_round_to_past_classic() {
    let precision = Precision::ToPast(Duration::minutes(20));
    let base = datetime(&Utc, 2025, 1, 1, 0, 0, 0);

    assert_eq!(
        // 2024-12-31T23:59:00Z
        precision.precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 5, 59, 0), base).unwrap(),
        datetime(&Utc, 2025, 1, 1, 5, 40, 0),
    );
}

#[test]
fn precision_with_base_time_round_to_past_uncommon() {
    let precision = Precision::ToPast(Duration::minutes(25));
    let base = datetime(&Utc, 2025, 1, 1, 0, 0, 0);

    /*
    00:00
    00:25
    00:50
    01:15
    01:40
    02:05
    02:30
    02:55
    03:20
    */

    assert_eq!(
        precision.precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 3, 17, 0), base).unwrap(),
        datetime(&Utc, 2025, 1, 1, 2, 55, 0),
    );
}

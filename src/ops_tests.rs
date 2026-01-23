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
        precision
            .precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 5, 30, 0), base)
            .unwrap(),
        datetime(&Utc, 2025, 1, 1, 5, 19, 0),
        "To nearest - Rounding down",
    );
    assert_eq!(
        precision
            .precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 5, 57, 30), base)
            .unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 36, 0),
        "To nearest - Rounding up when perfectly in the middle",
    );
    assert_eq!(
        precision
            .precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 6, 0, 0), base)
            .unwrap(),
        datetime(&Utc, 2025, 1, 1, 6, 36, 0),
        "To nearest - Rounding up",
    );
}

#[test]
fn precision_with_base_time_round_to_future_classic() {
    let precision = Precision::ToFuture(Duration::minutes(30));
    let base = datetime(&Utc, 2025, 1, 1, 0, 0, 0);

    assert_eq!(
        precision
            .precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 4, 5, 0), base)
            .unwrap(),
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
        precision
            .precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 2, 10, 0), base)
            .unwrap(),
        datetime(&Utc, 2025, 1, 1, 2, 30, 0),
    );
}

#[test]
fn precision_with_base_time_round_to_past_classic() {
    let precision = Precision::ToPast(Duration::minutes(20));
    let base = datetime(&Utc, 2025, 1, 1, 0, 0, 0);

    assert_eq!(
        precision
            .precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 5, 59, 0), base)
            .unwrap(),
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
        precision
            .precise_time_with_base_time(datetime(&Utc, 2025, 1, 1, 3, 17, 0), base)
            .unwrap(),
        datetime(&Utc, 2025, 1, 1, 2, 55, 0),
    );
}

#[test]
fn precision_round_to_future_time_on_rounding_instant_must_not_change() {
    let precision = Precision::ToFuture(Duration::minutes(5));

    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 8, 5, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 8, 5, 0),
    );
}

#[test]
fn precise_round_to_past_time_on_rounding_instance_must_not_change() {
    let precision = Precision::ToPast(Duration::minutes(5));

    assert_eq!(
        precision.precise_time(datetime(&Utc, 2025, 1, 1, 8, 5, 0)).unwrap(),
        datetime(&Utc, 2025, 1, 1, 8, 5, 0),
    );
}

#[test]
fn running_result_is_running() {
    assert!(RunningResult::<()>::Running(()).is_running());
    assert!(!RunningResult::<()>::Done(()).is_running());
}

#[test]
fn running_result_is_done() {
    assert!(!RunningResult::<()>::Running(()).is_done());
    assert!(RunningResult::<()>::Done(()).is_done());
}

#[test]
fn running_result_running_opt() {
    assert_eq!(RunningResult::<u8>::Running(10).running(), Some(10));
    assert_eq!(RunningResult::<u8>::Done(10).running(), None);
}

#[test]
fn running_result_done_opt() {
    assert_eq!(RunningResult::<u8>::Running(10).done(), None);
    assert_eq!(RunningResult::<u8>::Done(10).done(), Some(10));
}

#[test]
fn running_result_map_running() {
    assert_eq!(
        RunningResult::<u8>::Running(10).map_running(|x| x + 10),
        RunningResult::<u8>::Running(20)
    );
}

#[test]
fn running_result_map_done() {
    assert_eq!(
        RunningResult::<u8>::Done(10).map_done(|x| x + 10),
        RunningResult::<u8>::Done(20)
    );
}

#[test]
fn complement_result_is_single() {
    assert!(ComplementResult::<()>::Single(()).is_single());
    assert!(!ComplementResult::<()>::Split((), ()).is_single());
}

#[test]
fn complement_result_is_split() {
    assert!(!ComplementResult::<()>::Single(()).is_split());
    assert!(ComplementResult::<()>::Split((), ()).is_split());
}

#[test]
fn complement_result_single_opt() {
    assert_eq!(ComplementResult::<u8>::Single(10).single(), Some(10));
    assert_eq!(ComplementResult::<u8>::Split(10, 20).single(), None);
}

#[test]
fn complement_result_split_opt() {
    assert_eq!(ComplementResult::<u8>::Single(10).split(), None);
    assert_eq!(ComplementResult::<u8>::Split(10, 20).split(), Some((10, 20)));
}

#[test]
fn complement_result_map() {
    assert_eq!(
        ComplementResult::<u8>::Single(10).map(|x| x + 10),
        ComplementResult::<u8>::Single(20)
    );
    assert_eq!(
        ComplementResult::<u8>::Split(10, 20).map(|x| x + 10),
        ComplementResult::<u8>::Split(20, 30)
    );
}

#[test]
fn union_result_is_united() {
    assert!(UnionResult::<()>::United(()).is_united());
    assert!(!UnionResult::<()>::Separate.is_united());
}

#[test]
fn union_result_is_separate() {
    assert!(!UnionResult::<()>::United(()).is_separate());
    assert!(UnionResult::<()>::Separate.is_separate());
}

#[test]
fn union_result_united_opt() {
    assert_eq!(UnionResult::<u8>::United(10).united(), Some(10));
    assert_eq!(UnionResult::<u8>::Separate.united(), None);
}

#[test]
fn union_result_map_united() {
    assert_eq!(
        UnionResult::<u8>::United(10).map_united(|x| x + 10),
        UnionResult::United(20)
    );
}

#[test]
fn intersection_result_is_intersected() {
    assert!(IntersectionResult::<()>::Intersected(()).is_intersected());
    assert!(!IntersectionResult::<()>::Separate.is_intersected());
}

#[test]
fn intersection_result_is_separate() {
    assert!(!IntersectionResult::<()>::Intersected(()).is_separate());
    assert!(IntersectionResult::<()>::Separate.is_separate());
}

#[test]
fn intersection_result_intersected_opt() {
    assert_eq!(IntersectionResult::<u8>::Intersected(10).intersected(), Some(10));
    assert_eq!(IntersectionResult::<u8>::Separate.intersected(), None);
}

#[test]
fn intersection_result_map_intersected() {
    assert_eq!(
        IntersectionResult::<u8>::Intersected(10).map_intersected(|x| x + 10),
        IntersectionResult::<u8>::Intersected(20),
    );
}

#[test]
fn difference_result_is_shrunk() {
    assert!(DifferenceResult::<()>::Single(()).is_difference_single());
    assert!(!DifferenceResult::<()>::Split((), ()).is_difference_single());
    assert!(!DifferenceResult::<()>::Separate.is_difference_single());
}

#[test]
fn difference_result_is_split() {
    assert!(!DifferenceResult::<()>::Single(()).is_difference_split());
    assert!(DifferenceResult::<()>::Split((), ()).is_difference_split());
    assert!(!DifferenceResult::<()>::Separate.is_difference_split());
}

#[test]
fn difference_result_is_separate() {
    assert!(!DifferenceResult::<()>::Single(()).is_separate());
    assert!(!DifferenceResult::<()>::Split((), ()).is_separate());
    assert!(DifferenceResult::<()>::Separate.is_separate());
}

#[test]
fn difference_result_shrunk_opt() {
    assert_eq!(DifferenceResult::<u8>::Single(10).single(), Some(10));
    assert_eq!(DifferenceResult::<u8>::Split(10, 20).single(), None);
    assert_eq!(DifferenceResult::<u8>::Separate.single(), None);
}

#[test]
fn difference_result_split_opt() {
    assert_eq!(DifferenceResult::<u8>::Single(10).split(), None);
    assert_eq!(DifferenceResult::<u8>::Split(10, 20).split(), Some((10, 20)));
    assert_eq!(DifferenceResult::<u8>::Separate.split(), None);
}

#[test]
fn difference_result_map_difference() {
    assert_eq!(
        DifferenceResult::<u8>::Single(10).map_difference(|x| x + 10),
        DifferenceResult::<u8>::Single(20),
    );
    assert_eq!(
        DifferenceResult::<u8>::Split(10, 20).map_difference(|x| x + 10),
        DifferenceResult::<u8>::Split(20, 30),
    );
}

#[test]
fn sym_difference_result_has_symmetric_difference() {
    assert!(SymmetricDifferenceResult::<()>::Single(()).is_symmetric_difference());
    assert!(SymmetricDifferenceResult::<()>::Split((), ()).is_symmetric_difference());
    assert!(!SymmetricDifferenceResult::<()>::Separate.is_symmetric_difference());
}

#[test]
fn sym_difference_result_is_shrunk() {
    assert!(SymmetricDifferenceResult::<()>::Single(()).is_single());
    assert!(!SymmetricDifferenceResult::<()>::Split((), ()).is_single());
    assert!(!SymmetricDifferenceResult::<()>::Separate.is_single());
}

#[test]
fn sym_difference_result_is_split() {
    assert!(!SymmetricDifferenceResult::<()>::Single(()).is_split());
    assert!(SymmetricDifferenceResult::<()>::Split((), ()).is_split());
    assert!(!SymmetricDifferenceResult::<()>::Separate.is_split());
}

#[test]
fn sym_difference_result_is_separate() {
    assert!(!SymmetricDifferenceResult::<()>::Single(()).is_separate());
    assert!(!SymmetricDifferenceResult::<()>::Split((), ()).is_separate());
    assert!(SymmetricDifferenceResult::<()>::Separate.is_separate());
}

#[test]
fn sym_difference_result_shrunk_opt() {
    assert_eq!(SymmetricDifferenceResult::<u8>::Single(10).single(), Some(10));
    assert_eq!(SymmetricDifferenceResult::<u8>::Split(10, 20).single(), None);
    assert_eq!(SymmetricDifferenceResult::<u8>::Separate.single(), None);
}

#[test]
fn sym_difference_result_split_opt() {
    assert_eq!(SymmetricDifferenceResult::<u8>::Single(10).split(), None);
    assert_eq!(SymmetricDifferenceResult::<u8>::Split(10, 20).split(), Some((10, 20)));
    assert_eq!(SymmetricDifferenceResult::<u8>::Separate.split(), None);
}

#[test]
fn sym_difference_result_map_symmetric_difference() {
    assert_eq!(
        SymmetricDifferenceResult::<u8>::Single(10).map_symmetric_difference(|x| x + 10),
        SymmetricDifferenceResult::<u8>::Single(20),
    );
    assert_eq!(
        SymmetricDifferenceResult::<u8>::Split(10, 20).map_symmetric_difference(|x| x + 10),
        SymmetricDifferenceResult::<u8>::Split(20, 30),
    );
}

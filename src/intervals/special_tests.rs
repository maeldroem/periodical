use chrono::{Duration, Utc};

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::meta::{Duration as IntervalDuration, Openness, Relativity};
use crate::intervals::relative::{RelativeEndBound, RelativeStartBound};
use crate::prelude::*;
use crate::test_utils::date;

use super::special::*;

#[test]
fn open_interval_openness() {
    assert_eq!(OpenInterval.openness(), Openness::Open);
}

#[test]
fn open_interval_relativity() {
    assert_eq!(OpenInterval.relativity(), Relativity::Any);
}

#[test]
fn open_interval_duration() {
    assert_eq!(OpenInterval.duration(), IntervalDuration::Infinite);
}

#[test]
fn open_interval_abs_bounds() {
    assert_eq!(
        OpenInterval.abs_bounds(),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );
}

#[test]
fn open_interval_abs_start() {
    assert_eq!(OpenInterval.abs_start(), AbsoluteStartBound::InfinitePast);
}

#[test]
fn open_interval_abs_end() {
    assert_eq!(OpenInterval.abs_end(), AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn open_interval_rel_bounds() {
    assert_eq!(
        OpenInterval.rel_bounds(),
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    );
}

#[test]
fn open_interval_rel_start() {
    assert_eq!(OpenInterval.rel_start(), RelativeStartBound::InfinitePast);
}

#[test]
fn open_interval_rel_end() {
    assert_eq!(OpenInterval.rel_end(), RelativeEndBound::InfiniteFuture);
}

#[test]
fn open_interval_try_from_abs_interval_correct_variant() {
    assert_eq!(
        OpenInterval::try_from(AbsoluteInterval::Open(OpenInterval)),
        Ok(OpenInterval),
    );
}

#[test]
fn open_interval_try_from_abs_interval_wrong_variant() {
    assert_eq!(
        OpenInterval::try_from(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        ))),
        Err(OpenIntervalConversionErr::WrongVariant),
    );
}

#[test]
fn open_interval_try_from_rel_interval_correct_variant() {
    assert_eq!(
        OpenInterval::try_from(RelativeInterval::Open(OpenInterval)),
        Ok(OpenInterval),
    );
}

#[test]
fn open_interval_try_from_rel_interval_wrong_variant() {
    assert_eq!(
        OpenInterval::try_from(RelativeInterval::Closed(ClosedRelativeInterval::new(
            Duration::hours(1),
            Duration::hours(5),
        ))),
        Err(OpenIntervalConversionErr::WrongVariant),
    );
}

#[test]
fn empty_interval_openness() {
    assert_eq!(EmptyInterval.openness(), Openness::Empty);
}

#[test]
fn empty_interval_relativity() {
    assert_eq!(EmptyInterval.relativity(), Relativity::Any);
}

#[test]
fn empty_interval_duration() {
    assert_eq!(EmptyInterval.duration(), IntervalDuration::Finite(Duration::zero()));
}

#[test]
fn empty_interval_emptiable_abs_bounds() {
    assert_eq!(EmptyInterval.emptiable_abs_bounds(), EmptiableAbsoluteBounds::Empty);
}

#[test]
fn empty_interval_partial_abs_start() {
    assert!(EmptyInterval.partial_abs_start().is_none());
}

#[test]
fn empty_interval_partial_abs_end() {
    assert!(EmptyInterval.partial_abs_end().is_none());
}

#[test]
fn empty_interval_emptiable_rel_bounds() {
    assert_eq!(EmptyInterval.emptiable_rel_bounds(), EmptiableRelativeBounds::Empty);
}

#[test]
fn empty_interval_partial_rel_start() {
    assert!(EmptyInterval.partial_rel_start().is_none());
}

#[test]
fn empty_interval_partial_rel_end() {
    assert!(EmptyInterval.partial_rel_end().is_none());
}

#[test]
fn empty_interval_is_empty() {
    assert!(EmptyInterval.is_empty());
}

#[test]
fn empty_interval_try_from_abs_interval_correct_variant() {
    assert_eq!(
        EmptyInterval::try_from(AbsoluteInterval::Empty(EmptyInterval)),
        Ok(EmptyInterval)
    );
}

#[test]
fn empty_interval_try_from_abs_interval_wrong_variant() {
    assert_eq!(
        EmptyInterval::try_from(AbsoluteInterval::Closed(ClosedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        ))),
        Err(EmptyIntervalConversionErr::WrongVariant),
    );
}

#[test]
fn empty_interval_try_from_rel_interval_correct_variant() {
    assert_eq!(
        EmptyInterval::try_from(RelativeInterval::Empty(EmptyInterval)),
        Ok(EmptyInterval)
    );
}

#[test]
fn empty_interval_try_from_rel_interval_wrong_variant() {
    assert_eq!(
        EmptyInterval::try_from(RelativeInterval::Closed(ClosedRelativeInterval::new(
            Duration::hours(1),
            Duration::hours(5),
        ))),
        Err(EmptyIntervalConversionErr::WrongVariant),
    );
}

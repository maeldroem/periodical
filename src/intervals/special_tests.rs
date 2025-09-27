use chrono::{Duration, Utc};

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, BoundedAbsoluteInterval,
    EmptiableAbsoluteBounds, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::{
    Duration as IntervalDuration, Emptiable, Epsilon, HasDuration, HasOpenness, HasRelativity, Openness, Relativity,
};
use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBounds, HasEmptiableRelativeBounds, HasRelativeBounds, RelativeBounds,
    RelativeEndBound, RelativeInterval, RelativeStartBound,
};
use crate::test_utils::date;

use super::special::*;

#[test]
fn unbounded_interval_openness() {
    assert_eq!(UnboundedInterval.openness(), Openness::Unbounded);
}

#[test]
fn unbounded_interval_relativity() {
    assert_eq!(UnboundedInterval.relativity(), Relativity::Any);
}

#[test]
fn unbounded_interval_duration() {
    assert_eq!(UnboundedInterval.duration(), IntervalDuration::Infinite);
}

#[test]
fn unbounded_interval_abs_bounds() {
    assert_eq!(
        UnboundedInterval.abs_bounds(),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );
}

#[test]
fn unbounded_interval_abs_start() {
    assert_eq!(UnboundedInterval.abs_start(), AbsoluteStartBound::InfinitePast);
}

#[test]
fn unbounded_interval_abs_end() {
    assert_eq!(UnboundedInterval.abs_end(), AbsoluteEndBound::InfiniteFuture);
}

#[test]
fn unbounded_interval_rel_bounds() {
    assert_eq!(
        UnboundedInterval.rel_bounds(),
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    );
}

#[test]
fn unbounded_interval_rel_start() {
    assert_eq!(UnboundedInterval.rel_start(), RelativeStartBound::InfinitePast);
}

#[test]
fn unbounded_interval_rel_end() {
    assert_eq!(UnboundedInterval.rel_end(), RelativeEndBound::InfiniteFuture);
}

#[test]
fn unbounded_interval_try_from_abs_interval_correct_variant() {
    assert_eq!(
        UnboundedInterval::try_from(AbsoluteInterval::Unbounded(UnboundedInterval)),
        Ok(UnboundedInterval),
    );
}

#[test]
fn unbounded_interval_try_from_abs_interval_wrong_variant() {
    assert_eq!(
        UnboundedInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            date(&Utc, 2025, 1, 1),
            date(&Utc, 2025, 1, 2),
        ))),
        Err(UnboundedIntervalConversionErr::WrongVariant),
    );
}

#[test]
fn unbounded_interval_try_from_rel_interval_correct_variant() {
    assert_eq!(
        UnboundedInterval::try_from(RelativeInterval::Unbounded(UnboundedInterval)),
        Ok(UnboundedInterval),
    );
}

#[test]
fn unbounded_interval_try_from_rel_interval_wrong_variant() {
    assert_eq!(
        UnboundedInterval::try_from(RelativeInterval::Bounded(BoundedRelativeInterval::new(
            Duration::hours(1),
            Duration::hours(5),
        ))),
        Err(UnboundedIntervalConversionErr::WrongVariant),
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
    assert_eq!(
        EmptyInterval.duration(),
        IntervalDuration::Finite(Duration::zero(), Epsilon::None)
    );
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
        EmptyInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
        EmptyInterval::try_from(RelativeInterval::Bounded(BoundedRelativeInterval::new(
            Duration::hours(1),
            Duration::hours(5),
        ))),
        Err(EmptyIntervalConversionErr::WrongVariant),
    );
}

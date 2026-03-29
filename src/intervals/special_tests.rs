use std::error::Error;
use std::time::Duration as StdDuration;

use jiff::{SignedDuration, Timestamp};

use super::special::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{
    Duration as IntervalDuration,
    Emptiable,
    Epsilon,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
};

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
fn unbounded_interval_abs_bound_pair() {
    assert_eq!(
        UnboundedInterval.abs_bound_pair(),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
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
fn unbounded_interval_rel_bound_pair() {
    assert_eq!(
        UnboundedInterval.rel_bound_pair(),
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
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
fn unbounded_interval_try_from_abs_interval_wrong_variant() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        UnboundedInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        ))),
        Err(UnboundedIntervalConversionErr::WrongVariant),
    );
    Ok(())
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
            SignedDuration::from_hours(1),
            SignedDuration::from_hours(5),
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
        IntervalDuration::Finite(StdDuration::ZERO, Epsilon::None)
    );
}

#[test]
fn empty_interval_emptiable_abs_bound_pair() {
    assert_eq!(
        EmptyInterval.emptiable_abs_bound_pair(),
        EmptiableAbsoluteBoundPair::Empty
    );
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
fn empty_interval_emptiable_rel_bound_pair() {
    assert_eq!(
        EmptyInterval.emptiable_rel_bound_pair(),
        EmptiableRelativeBoundPair::Empty
    );
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

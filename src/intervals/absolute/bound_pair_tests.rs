use std::cmp::Ordering;
use std::error::Error;

use jiff::Timestamp;

use super::bound_pair::*;
use crate::intervals::absolute::{
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn unchecked_new() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let abs_bounds = AbsoluteBoundPair::unchecked_new(start, end);

    assert_eq!(abs_bounds.abs_start(), start);
    assert_eq!(abs_bounds.abs_end(), end);
    Ok(())
}

#[test]
fn new_should_swap() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn from_range() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let range = start..;

    let bound_pair = AbsoluteBoundPair::from_range(range);

    assert_eq!(bound_pair.start(), AbsoluteFiniteBound::new(start).to_start_bound());
    assert_eq!(bound_pair.end(), AbsoluteEndBound::InfiniteFuture);
    Ok(())
}

#[test]
fn to_emptiable() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(
        AbsoluteBoundPair::new(start, end).to_emptiable(),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(start, end)),
    );
    Ok(())
}

#[test]
fn unchecked_set_start() -> Result<(), Box<dyn Error>> {
    let mut bounds = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    let new_start = AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound();

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.abs_start(), new_start);
    Ok(())
}

#[test]
fn unchecked_set_end() -> Result<(), Box<dyn Error>> {
    let mut bounds = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    let new_end = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.abs_end(), new_end);
    Ok(())
}

#[test]
fn set_start() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let mut bounds = AbsoluteBoundPair::new(start, end);

    assert!(!bounds.set_start(AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound()));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
    Ok(())
}

#[test]
fn set_end() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let mut bounds = AbsoluteBoundPair::new(start, end);

    assert!(!bounds.set_end(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
    Ok(())
}

#[test]
fn unbounded_unbounded_cmp() {
    let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Equal);
}

#[test]
fn unbounded_half_bounded_to_future_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
    Ok(())
}

#[test]
fn unbounded_half_bounded_to_past_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
    Ok(())
}

#[test]
fn unbounded_bounded_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
    Ok(())
}

#[test]
fn half_bounded_to_future_unbounded_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_future_after_first_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_future_before_first_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_future_same_time_exclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_future_same_time_exclusive_inclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_future_same_time_inclusive_exclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_future_same_time_inclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );

    assert_eq!(a.cmp(&b), Ordering::Equal);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_past_before_first_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_past_after_first_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_past_same_time_exclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_past_same_time_exclusive_inclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_past_same_time_inclusive_exclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_to_past_same_time_inclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_bounded_starts_before_first_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Greater);
    Ok(())
}

#[test]
fn half_bounded_to_future_bounded_starts_after_first_cmp() -> Result<(), Box<dyn Error>> {
    let a = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let b = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2025-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    assert_eq!(a.cmp(&b), Ordering::Less);
    Ok(())
}

#[test]
fn try_from_emptiable_correct_variant() {
    assert_eq!(
        AbsoluteBoundPair::try_from(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        ))),
        Ok(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn try_from_emptiable_wrong_variant() {
    assert_eq!(
        AbsoluteBoundPair::try_from(EmptiableAbsoluteBoundPair::Empty),
        Err(AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError),
    );
}

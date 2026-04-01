use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::finite_bound::*;
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

#[test]
fn new() -> Result<(), Box<dyn Error>> {
    let time = "2025-01-01 00:00:00Z".parse::<Timestamp>()?;
    let abs_finite_bound = AbsoluteFiniteBound::new(time);

    assert_eq!(abs_finite_bound.time(), time);
    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
    Ok(())
}

#[test]
fn new_with_inclusivity() -> Result<(), Box<dyn Error>> {
    let time = "2025-01-01 00:00:00Z".parse::<Timestamp>()?;
    let abs_finite_bound = AbsoluteFiniteBound::new_with_inclusivity(time, BoundInclusivity::Exclusive);

    assert_eq!(abs_finite_bound.time(), time);
    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
    Ok(())
}

#[test]
fn set_time() -> Result<(), Box<dyn Error>> {
    let mut abs_finite_bound = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    let new_time = "2025-05-01 00:00:00Z".parse::<Timestamp>()?;

    abs_finite_bound.set_time(new_time);

    assert_eq!(abs_finite_bound.time(), new_time);
    Ok(())
}

#[test]
fn set_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut abs_finite_bound = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    );

    abs_finite_bound.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Inclusive);
    Ok(())
}

#[test]
fn inclusivity() -> Result<(), Box<dyn Error>> {
    let abs_finite_bound = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    );

    assert_eq!(abs_finite_bound.inclusivity(), BoundInclusivity::Exclusive);
    Ok(())
}

#[test]
fn cmp_greater_times() -> Result<(), Box<dyn Error>> {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?),
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Greater);
    Ok(())
}

#[test]
fn cmp_equal_times() -> Result<(), Box<dyn Error>> {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Equal);
    Ok(())
}

#[test]
fn cmp_equal_time_different_inclusivities() -> Result<(), Box<dyn Error>> {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Equal);
    Ok(())
}

#[test]
fn cmp_less() -> Result<(), Box<dyn Error>> {
    let abs_finite_bound = [
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?),
    ];

    assert_eq!(abs_finite_bound[0].cmp(&abs_finite_bound[1]), Ordering::Less);
    Ok(())
}

#[test]
fn from_timestamp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::from("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ),
    );
    Ok(())
}

#[test]
fn from_timestamp_inclusivity_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::from((
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ),
    );
    Ok(())
}

#[test]
fn try_from_inclusive_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Included("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive
        )),
    );
    Ok(())
}

#[test]
fn try_from_exclusive_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )),
    );
    Ok(())
}

#[test]
fn try_from_unbounded_bound() {
    assert_eq!(
        AbsoluteFiniteBound::try_from(Bound::Unbounded),
        Err(AbsoluteFiniteBoundTryFromBoundError),
    );
}

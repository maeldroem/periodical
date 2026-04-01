use std::error::Error;

use jiff::Timestamp;

use super::bounded_interval::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::UnboundedInterval;

#[test]
fn interval_unchecked_new() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::unchecked_new(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn interval_new_no_swap() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::new(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn interval_new_swap() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::new(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn interval_new_with_inclusivity_no_swap() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn interval_new_with_inclusivity_swap() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn unchecked_set_start() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_start("2025-01-03 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(interval.start(), "2025-01-03 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn unchecked_set_end() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-03 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_end("2025-01-01 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(interval.start(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn set_start() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    assert_eq!(
        interval.set_start("2025-01-03 00:00:00Z".parse::<Timestamp>()?),
        Err(BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation),
    );

    Ok(())
}

#[test]
fn set_end() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-03 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    assert_eq!(
        interval.set_end("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        Err(BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation),
    );

    Ok(())
}

#[test]
fn set_start_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.set_start_inclusivity(BoundInclusivity::Inclusive)?;

    assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn set_end_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-03 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.set_end_inclusivity(BoundInclusivity::Exclusive)?;

    assert_eq!(interval.start(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-03 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn interval_from_datetime_pair_swap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::from((
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?
        )),
        BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ),
    );

    Ok(())
}

#[test]
fn interval_from_pair_of_datetime_inclusivity_pairs_swap() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::from((
            (
                "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            ),
            (
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive
            ),
        )),
        BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ),
    );

    Ok(())
}

#[test]
fn interval_from_range() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::from(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?.."2025-01-02 00:00:00Z".parse::<Timestamp>()?
        ),
        BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ),
    );

    Ok(())
}

#[test]
fn interval_from_range_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::from(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?..="2025-01-02 00:00:00Z".parse::<Timestamp>()?
        ),
        BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?
        ),
    );

    Ok(())
}

#[test]
fn interval_try_from_absolute_bounds_correct() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )),
        )),
        Ok(BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )),
    );

    Ok(())
}

#[test]
fn interval_try_from_absolute_bounds_wrong() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        )),
        Err(BoundedAbsoluteIntervalTryFromAbsoluteBoundPairError),
    );
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(BoundedAbsoluteIntervalTryFromAbsoluteBoundPairError),
    );
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(BoundedAbsoluteIntervalTryFromAbsoluteBoundPairError),
    );

    Ok(())
}

#[test]
fn interval_try_from_absolute_interval_correct() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        ))),
        Ok(BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        )),
    );

    Ok(())
}

#[test]
fn interval_try_from_absolute_interval_wrong() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteInterval::Unbounded(UnboundedInterval)),
        Err(BoundedAbsoluteIntervalFromAbsoluteIntervalError),
    );
    assert_eq!(
        BoundedAbsoluteInterval::try_from(AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture,
        ))),
        Err(BoundedAbsoluteIntervalFromAbsoluteIntervalError),
    );

    Ok(())
}

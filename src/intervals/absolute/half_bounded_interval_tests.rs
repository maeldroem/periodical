use std::error::Error;

use jiff::Timestamp;

use super::half_bounded_interval::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::UnboundedInterval;

#[test]
fn new() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

    assert_eq!(interval.reference(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn new_with_inclusivity() -> Result<(), Box<dyn Error>> {
    let interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.reference(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn set_reference() -> Result<(), Box<dyn Error>> {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference("2025-01-02 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );

    Ok(())
}

#[test]
fn set_reference_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );

    Ok(())
}

#[test]
fn set_opening_direction() -> Result<(), Box<dyn Error>> {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );

    Ok(())
}

#[test]
fn from_datetime_opening_direction_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)),
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture),
    );

    Ok(())
}

#[test]
fn from_pair_of_datetime_bound_inclusivity_pair_and_opening_direction() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from((
            (
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            ),
            OpeningDirection::ToPast
        )),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );

    Ok(())
}

#[test]
fn from_range_from() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from("2025-01-01 00:00:00Z".parse::<Timestamp>()?..),
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture),
    );

    Ok(())
}

#[test]
fn from_range_to() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(.."2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );

    Ok(())
}

#[test]
fn from_range_to_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(..="2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToPast),
    );

    Ok(())
}

#[test]
fn try_from_absolute_bounds_correct() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )),
        )),
        Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );

    Ok(())
}

#[test]
fn try_from_absolute_bounds_wrong() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteBoundPairError::NotHalfBoundedInterval),
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)),
        )),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteBoundPairError::NotHalfBoundedInterval),
    );

    Ok(())
}

#[test]
fn try_from_absolute_interval_correct() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast,
            )
        )),
        Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )),
    );

    Ok(())
}

#[test]
fn try_from_absolute_interval_wrong() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteInterval::Unbounded(UnboundedInterval)),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        ))),
        Err(HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError::WrongVariant),
    );

    Ok(())
}

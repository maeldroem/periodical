use std::error::Error;

use jiff::Timestamp;

use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::UnboundedInterval;

use super::interval::*;

#[test]
fn from_absolute_bounds() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::from(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::InfiniteFuture,
        )),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )),
    );

    Ok(())
}

#[test]
fn from_opt_datetime_pair_unbounded() {
    assert_eq!(
        <AbsoluteInterval as From<(Option<Timestamp>, Option<Timestamp>)>>::from((None, None)),
        AbsoluteInterval::Unbounded(UnboundedInterval),
    );
}

#[test]
fn from_opt_datetime_pair_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::from((None, Some("2025-01-01 00:00:00Z".parse::<Timestamp>()?))),
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToPast,
        )),
    );

    Ok(())
}

#[test]
fn from_opt_datetime_bound_inclusivity_pairs() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::from((
            Some(("2025-01-01 00:00:00Z".parse::<Timestamp>()?, BoundInclusivity::Exclusive)),
            Some(("2025-01-02 00:00:00Z".parse::<Timestamp>()?, BoundInclusivity::Exclusive)),
        )),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
    );

    Ok(())
}

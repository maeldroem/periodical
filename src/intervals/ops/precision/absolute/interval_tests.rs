use std::error::Error;
use std::time::Duration;

use jiff::Zoned;
use jiff::tz::TimeZone;

use super::interval::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition, EmptiableAbsoluteBoundPair};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::{Precision, PrecisionMode};

#[test]
fn abs_bound_pair_same_precision() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .precise_interval(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?
        ),
        Ok(AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_different_precisions() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .precise_interval_with_different_precisions(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
        ),
        Ok(AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 09:55:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )),
    );

    Ok(())
}

#[test]
fn start_empty() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.precise_interval(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(EmptiableAbsoluteBoundPair::Empty),
    );

    Ok(())
}

#[test]
fn end_empty() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty.precise_interval(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(EmptiableAbsoluteBoundPair::Empty),
    );

    Ok(())
}

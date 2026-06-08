use std::error::Error;
use std::time::Duration;

use jiff::Zoned;
use jiff::tz::TimeZone;

use super::interval::*;
use crate::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::{Precision, PrecisionMode};

#[test]
fn abs_bound_pair_same_precision() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?
        ),
        Ok(AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
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
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        )
        .precise_different_precisions(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
        ),
        Ok(AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
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
        EmptiableAbsBoundPair::Empty.precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(EmptiableAbsBoundPair::Empty),
    );

    Ok(())
}

#[test]
fn end_empty() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsBoundPair::Empty.precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(EmptiableAbsBoundPair::Empty),
    );

    Ok(())
}

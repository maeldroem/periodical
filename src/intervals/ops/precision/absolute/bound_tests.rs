use std::error::Error;
use std::time::Duration;

use jiff::Zoned;
use jiff::tz::TimeZone;

use super::bound::*;
use crate::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::{Precision, PrecisionMode};

#[test]
fn finite_bound_position() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 10:42:31[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive
        )
        .precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToNearest)?
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 10:45:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )),
    );

    Ok(())
}

#[test]
fn start_infinite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::InfinitePast.precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsStartBound::InfinitePast),
    );

    Ok(())
}

#[test]
fn start_common_precision() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
        .precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()),
    );

    Ok(())
}

#[test]
fn start_uncommon_precision_with_base() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
        .precise_with_base_time(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(
                Duration::from_mins(7) + Duration::from_secs(31),
                PrecisionMode::ToFuture
            )?,
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 02:30:20[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()),
    );

    Ok(())
}

#[test]
fn end_infinite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsEndBound::InfiniteFuture.precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn end_common_precision() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
        .precise(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()),
    );

    Ok(())
}

#[test]
fn end_uncommon_precision_with_base() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
        .precise_with_base_time(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(
                Duration::from_mins(7) + Duration::from_secs(31),
                PrecisionMode::ToFuture
            )?,
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 10:01:20[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()),
    );

    Ok(())
}

use std::error::Error;
use std::time::Duration;

use jiff::Zoned;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::{Precision, PrecisionMode};

use super::precision::*;

#[test]
fn finite_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 10:42:31[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive
        )
            .precise_bound(TimeZone::get("Europe/Oslo")?, Precision::new(Duration::from_mins(5), PrecisionMode::ToNearest)?),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 10:45:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )),
    );

    Ok(())
}

#[test]
fn start_infinite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::InfinitePast.precise_bound(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsoluteStartBound::InfinitePast),
    );

    Ok(())
}

#[test]
fn start_common_precision() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn start_uncommon_precision_with_base() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound_with_base_time(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(7) + Duration::from_secs(31), PrecisionMode::ToFuture)?,
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ),
        Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 02:30:20[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn end_infinite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.precise_bound(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsoluteEndBound::InfiniteFuture),
    );

    Ok(())
}

#[test]
fn end_common_precision() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
        ),
        Ok(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn end_uncommon_precision_with_base() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))
        .precise_bound_with_base_time(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(7) + Duration::from_secs(31), PrecisionMode::ToFuture)?,
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ),
        Ok(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 10:01:20[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_same_precision() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )
        .precise_interval(TimeZone::get("Europe/Oslo")?, Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?),
        Ok(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 10:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )),
    );

    Ok(())
}

#[test]
fn abs_bound_pair_different_precisions() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 02:23:44[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 09:56:21[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )
        .precise_interval_with_different_precisions(
            TimeZone::get("Europe/Oslo")?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
            Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
        ),
        Ok(AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 02:25:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 09:55:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
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

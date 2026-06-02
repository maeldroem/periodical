use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::relativity_conversion::*;
use crate::intervals::absolute::BoundedAbsoluteInterval;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::BoundedRelativeInterval;

#[test]
fn no_op_absolute_to_absolute() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::from_times_and_inclusivities(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Inclusive,
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_absolute("2000-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        BoundedAbsoluteInterval::from_times_and_inclusivities(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Inclusive,
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ),
    );

    Ok(())
}

#[test]
fn no_op_relative_to_relative() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedRelativeInterval::from_offsets_and_inclusivities(
            SignedDuration::ZERO,
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .to_relative("2000-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        BoundedRelativeInterval::from_offsets_and_inclusivities(
            SignedDuration::ZERO,
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ),
    );

    Ok(())
}

#[test]
fn from_absolute_to_relative() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::from_times_and_inclusivities(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Inclusive,
            "2025-01-01 01:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_relative("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        BoundedRelativeInterval::from_offsets_and_inclusivities(
            SignedDuration::ZERO,
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ),
    );

    Ok(())
}

#[test]
fn from_relative_to_absolute() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedRelativeInterval::from_offsets_and_inclusivities(
            SignedDuration::ZERO,
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .to_absolute("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        BoundedAbsoluteInterval::from_times_and_inclusivities(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Inclusive,
            "2025-01-01 01:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        ),
    );

    Ok(())
}

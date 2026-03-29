use std::error::Error;

use jiff::Zoned;
use jiff::civil::Date;
use jiff::tz::TimeZone;

use crate::intervals::absolute::HalfBoundedAbsoluteInterval;
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::time::{Month, OffsetIsoWeek};

#[test]
fn since_date() -> Result<(), Box<dyn Error>> {
    let from_first_of_may =
        HalfBoundedAbsoluteInterval::since_date("2026-05-01".parse::<Date>()?, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        from_first_of_may.reference(),
        "2026-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    );
    assert_eq!(from_first_of_may.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(from_first_of_may.opening_direction(), OpeningDirection::ToFuture);

    Ok(())
}

#[test]
fn until_date() -> Result<(), Box<dyn Error>> {
    let until_first_of_may =
        HalfBoundedAbsoluteInterval::until_date("2026-05-01".parse::<Date>()?, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        until_first_of_may.reference(),
        "2026-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    );
    assert_eq!(until_first_of_may.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_first_of_may.opening_direction(), OpeningDirection::ToPast);

    Ok(())
}

#[test]
fn since_week() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsoluteInterval::since_week(OffsetIsoWeek::new(5, 2026)?, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.reference(),
        "2026-01-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);

    Ok(())
}

#[test]
fn until_week() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsoluteInterval::until_week(OffsetIsoWeek::new(5, 2026)?, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.reference(),
        "2026-01-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);

    Ok(())
}

#[test]
fn since_month() -> Result<(), Box<dyn Error>> {
    let since_month =
        HalfBoundedAbsoluteInterval::since_month(Month::March.with_year(2026), TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        since_month.reference(),
        "2026-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(since_month.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(since_month.opening_direction(), OpeningDirection::ToFuture);

    Ok(())
}

#[test]
fn until_month() -> Result<(), Box<dyn Error>> {
    let until_month =
        HalfBoundedAbsoluteInterval::until_month(Month::March.with_year(2026), TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        until_month.reference(),
        "2026-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(until_month.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_month.opening_direction(), OpeningDirection::ToPast);

    Ok(())
}

#[test]
fn since_year() -> Result<(), Box<dyn Error>> {
    let since_year = HalfBoundedAbsoluteInterval::since_year(2026, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        since_year.reference(),
        "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(since_year.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(since_year.opening_direction(), OpeningDirection::ToFuture);

    Ok(())
}

#[test]
fn until_year() -> Result<(), Box<dyn Error>> {
    let until_year = HalfBoundedAbsoluteInterval::until_year(2026, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        until_year.reference(),
        "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(until_year.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_year.opening_direction(), OpeningDirection::ToPast);

    Ok(())
}

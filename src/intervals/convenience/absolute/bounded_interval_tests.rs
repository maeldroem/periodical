use std::error::Error;

use jiff::Zoned;
use jiff::civil::Date;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{BoundedAbsInterval, BoundedAbsIntervalCreationError};
use crate::intervals::meta::BoundInclusivity;
use crate::time::{CalendarAnchorOffset, Month, OffsetIsoWeek};

#[test]
fn from_date() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsInterval::from_date("2026-01-05".parse::<Date>()?, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.start_time(),
        "2026-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_date_max_date() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_date(Date::MAX, TimeZone::get("Europe/Oslo")?),
        Err(BoundedAbsIntervalCreationError::ComputationError),
    );

    Ok(())
}

#[test]
fn day_after_duration_from_date() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsInterval::day_after_duration_from_date(
        "2026-04-29".parse::<Date>()?,
        CalendarAnchorOffset::Days(5),
        TimeZone::get("Europe/Oslo")?,
    )?;

    assert_eq!(
        interval.start_time(),
        "2026-05-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-05-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn day_before_duration_from_date() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsInterval::day_before_duration_from_date(
        "2026-04-29".parse::<Date>()?,
        CalendarAnchorOffset::Days(5),
        TimeZone::get("Europe/Oslo")?,
    )?;

    assert_eq!(
        interval.start_time(),
        "2026-04-24 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-04-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_date_range() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-05".parse::<Date>()?;
    let end = "2026-01-10".parse::<Date>()?;

    let interval = BoundedAbsInterval::from_inclusive_date_range(start, end, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.start_time(),
        "2026-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-01-11 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_date_range_min_from_and_to() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_inclusive_date_range(Date::MIN, Date::MAX, TimeZone::get("Europe/Oslo")?),
        Err(BoundedAbsIntervalCreationError::ComputationError),
    );

    Ok(())
}

#[test]
fn from_inclusive_date_range_max_to() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_inclusive_date_range(
            "2026-01-01".parse::<Date>()?,
            Date::MAX,
            TimeZone::get("Europe/Oslo")?,
        ),
        Err(BoundedAbsIntervalCreationError::OutOfRangeEnd)
    );

    Ok(())
}

#[test]
fn from_inclusive_date_range_reversed_order() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-10".parse::<Date>()?;
    let end = "2026-01-05".parse::<Date>()?;

    let interval = BoundedAbsInterval::from_inclusive_date_range(start, end, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.start_time(),
        "2026-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-01-11 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_week() -> Result<(), Box<dyn Error>> {
    let week_interval = BoundedAbsInterval::from_week(OffsetIsoWeek::new(2026, 5)?, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        week_interval.start_time(),
        "2026-01-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(week_interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        week_interval.end_time(),
        "2026-02-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(week_interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_week_range() -> Result<(), Box<dyn Error>> {
    let start = OffsetIsoWeek::new(2026, 5)?;
    let end = OffsetIsoWeek::new(2026, 10)?;

    let interval = BoundedAbsInterval::from_inclusive_week_range(start, end, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.start_time(),
        "2026-01-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-03-09 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_week_range_same_week() -> Result<(), Box<dyn Error>> {
    let week = OffsetIsoWeek::new(2026, 5)?;

    let interval = BoundedAbsInterval::from_inclusive_week_range(week, week, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.start_time(),
        "2026-01-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-02-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_week_range_reverse_order() -> Result<(), Box<dyn Error>> {
    let start = OffsetIsoWeek::new_with_offset(2026, 5, 4)?;
    let end = OffsetIsoWeek::new_with_offset(2026, 5, -4)?;

    let interval = BoundedAbsInterval::from_inclusive_week_range(start, end, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.start_time(),
        "2026-01-28 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-01-31 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn week_from_month() -> Result<(), Box<dyn Error>> {
    let month = BoundedAbsInterval::from_month(Month::May.with_year(2026), TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        month.start_time(),
        "2026-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        month.end_time(),
        "2026-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_month_range() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsInterval::from_inclusive_month_range(
        Month::January.with_year(2026),
        Month::May.with_year(2026),
        TimeZone::get("Europe/Oslo")?,
    )?;

    assert_eq!(
        interval.start_time(),
        "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_month_range_same_month() -> Result<(), Box<dyn Error>> {
    let month = Month::May.with_year(2026);
    let interval = BoundedAbsInterval::from_inclusive_month_range(month, month, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        interval.start_time(),
        "2026-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_month_range_reverse_order() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsInterval::from_inclusive_month_range(
        Month::May.with_year(2026),
        Month::January.with_year(2026),
        TimeZone::get("Europe/Oslo")?,
    )?;

    assert_eq!(
        interval.start_time(),
        "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        interval.end_time(),
        "2026-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn month_after_duration_from_date() -> Result<(), Box<dyn Error>> {
    let month = BoundedAbsInterval::month_after_duration_from_date(
        "2026-05-05".parse::<Date>()?,
        CalendarAnchorOffset::Months(2),
        TimeZone::get("Europe/Oslo")?,
    )?;

    assert_eq!(
        month.start_time(),
        "2026-07-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        month.end_time(),
        "2026-08-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn month_before_duration_from_date() -> Result<(), Box<dyn Error>> {
    let month = BoundedAbsInterval::month_before_duration_from_date(
        "2026-05-05".parse::<Date>()?,
        CalendarAnchorOffset::Months(2),
        TimeZone::get("Europe/Oslo")?,
    )?;

    assert_eq!(
        month.start_time(),
        "2026-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        month.end_time(),
        "2026-04-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_year_common() -> Result<(), Box<dyn Error>> {
    let year = BoundedAbsInterval::from_year(2026, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        year.start_time(),
        "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        year.end_time(),
        "2027-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_year_leap() -> Result<(), Box<dyn Error>> {
    let year = BoundedAbsInterval::from_year(2028, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        year.start_time(),
        "2028-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        year.end_time(),
        "2029-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_year_range() -> Result<(), Box<dyn Error>> {
    let years = BoundedAbsInterval::from_inclusive_year_range(2025, 2030, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        years.start_time(),
        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(years.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        years.end_time(),
        "2031-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(years.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_year_range_same_year() -> Result<(), Box<dyn Error>> {
    let year = BoundedAbsInterval::from_inclusive_year_range(2030, 2030, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        year.start_time(),
        "2030-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        year.end_time(),
        "2031-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn from_inclusive_year_range_reverse_order() -> Result<(), Box<dyn Error>> {
    let years = BoundedAbsInterval::from_inclusive_year_range(2030, 2025, TimeZone::get("Europe/Oslo")?)?;

    assert_eq!(
        years.start_time(),
        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(years.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        years.end_time(),
        "2031-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(years.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn year_after_duration_from_date() -> Result<(), Box<dyn Error>> {
    let year = BoundedAbsInterval::year_after_duration_from_date(
        "2026-05-05".parse::<Date>()?,
        CalendarAnchorOffset::Months(15),
        TimeZone::get("Europe/Oslo")?,
    )?;

    assert_eq!(
        year.start_time(),
        "2027-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        year.end_time(),
        "2028-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

#[test]
fn year_before_duration_from_date() -> Result<(), Box<dyn Error>> {
    let year = BoundedAbsInterval::year_before_duration_from_date(
        "2026-05-05".parse::<Date>()?,
        CalendarAnchorOffset::Months(15),
        TimeZone::get("Europe/Oslo")?,
    )
    .unwrap();

    assert_eq!(
        year.start_time(),
        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(
        year.end_time(),
        "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
    );
    assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

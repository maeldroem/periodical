use std::cmp::Ordering;
use std::error::Error;

use jiff::civil::{Date, Weekday};
use jiff::tz::TimeZone;

use super::time::*;

#[test]
fn date_today_smoke_test() -> Result<(), Box<dyn Error>> {
    let _ = date_today(TimeZone::get("Europe/Oslo")?);
    Ok(())
}

mod iso_weeks_in_year_fn {
    use super::*;

    #[test]
    fn short_year() -> Result<(), Box<dyn Error>> {
        [
            2025, 2024, 2023, 2022, 2021, 2019, 2018, 2017, 2016, 2014, 2013, 2012, 2011, 2010,
        ]
        .into_iter()
        .try_for_each(|year| {
            assert_eq!(
                iso_weeks_in_year(year)?,
                ISO_WEEKS_IN_SHORT_YEAR,
                "Expecting short ISO year for year {year}",
            );
            Ok(())
        })
    }

    #[test]
    fn long_year() -> Result<(), Box<dyn Error>> {
        [2026, 2020, 2015, 2009].into_iter().try_for_each(|year| {
            assert_eq!(
                iso_weeks_in_year(year)?,
                ISO_WEEKS_IN_LONG_YEAR,
                "Expecting long ISO year for year {year}",
            );
            Ok(())
        })
    }
}

mod offset_iso_week {
    use super::*;

    #[test]
    fn new_without_offset() -> Result<(), Box<dyn Error>> {
        let iso_week = OffsetIsoWeek::new(2026, 5)?;
        assert_eq!(iso_week.first_day()?, "2026-01-26".parse::<Date>()?);
        assert_eq!(iso_week.last_day()?, "2026-02-01".parse::<Date>()?);
        Ok(())
    }

    #[test]
    fn new_with_offset_sunday() -> Result<(), Box<dyn Error>> {
        let offset_iso_week = OffsetIsoWeek::new_with_offset(2026, 5, -1)?;
        assert_eq!(offset_iso_week.first_day()?, "2026-01-25".parse::<Date>()?);
        assert_eq!(offset_iso_week.last_day()?, "2026-01-31".parse::<Date>()?);
        Ok(())
    }

    #[test]
    fn new_with_offset_wednesday() -> Result<(), Box<dyn Error>> {
        let offset_iso_week = OffsetIsoWeek::new_with_offset(2026, 5, 2)?;
        assert_eq!(offset_iso_week.first_day()?, "2026-01-28".parse::<Date>()?);
        assert_eq!(offset_iso_week.last_day()?, "2026-02-03".parse::<Date>()?);
        Ok(())
    }

    #[test]
    fn new_out_of_range_week_zero() {
        assert_eq!(
            OffsetIsoWeek::new(2026, 0),
            Err(OffsetIsoWeekCreationError::OutOfRangeWeek)
        );
    }

    #[test]
    fn new_out_of_range_week() {
        assert_eq!(
            OffsetIsoWeek::new(2026, 55),
            Err(OffsetIsoWeekCreationError::OutOfRangeWeek)
        );
    }

    #[test]
    fn new_with_out_of_range_offset() {
        assert_eq!(
            OffsetIsoWeek::new_with_offset(2026, 5, -10),
            Err(OffsetIsoWeekCreationError::OutOfRangeOffset)
        );
        assert_eq!(
            OffsetIsoWeek::new_with_offset(2026, 5, 10),
            Err(OffsetIsoWeekCreationError::OutOfRangeOffset)
        );
    }

    #[test]
    fn from_date() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date("2023-01-01".parse::<Date>()?)?;

        assert_eq!(week.year(), 2022);
        assert_eq!(week.week(), 52);
        assert_eq!(week.week_start_offset(), 0);

        Ok(())
    }

    #[test]
    fn from_date_with_offset_out_of_range_offset() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            OffsetIsoWeek::from_date_with_offset("2026-01-01".parse::<Date>()?, -10),
            Err(OffsetIsoWeekCreationError::OutOfRangeOffset),
        );
        assert_eq!(
            OffsetIsoWeek::from_date_with_offset("2026-01-01".parse::<Date>()?, 10),
            Err(OffsetIsoWeekCreationError::OutOfRangeOffset),
        );

        Ok(())
    }

    #[test]
    fn from_date_with_offset_no_offset() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date_with_offset("2026-05-01".parse::<Date>()?, 0)?;

        assert_eq!(week.year(), 2026);
        assert_eq!(week.week(), 18);
        assert_eq!(week.week_start_offset(), 0);

        Ok(())
    }

    #[test]
    fn from_date_with_offset_positive_offset_year_wrap() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date_with_offset("2025-12-31".parse::<Date>()?, 5)?;

        assert_eq!(week.year(), 2025);
        assert_eq!(week.week(), 52);
        assert_eq!(week.week_start_offset(), 5);

        Ok(())
    }

    #[test]
    fn from_date_with_offset_negative_offset_year_wrap() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date_with_offset("2025-12-25".parse::<Date>()?, -5)?;

        assert_eq!(week.year(), 2026);
        assert_eq!(week.week(), 1);
        assert_eq!(week.week_start_offset(), -5);

        Ok(())
    }

    #[test]
    fn from_date_with_offset_positive_offset_week_wrap() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date_with_offset("2026-05-01".parse::<Date>()?, 5)?;

        assert_eq!(week.year(), 2026);
        assert_eq!(week.week(), 17);
        assert_eq!(week.week_start_offset(), 5);

        Ok(())
    }

    #[test]
    fn from_date_with_offset_negative_offset_week_wrap() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date_with_offset("2026-05-01".parse::<Date>()?, -5)?;

        assert_eq!(week.year(), 2026);
        assert_eq!(week.week(), 19);
        assert_eq!(week.week_start_offset(), -5);

        Ok(())
    }

    #[test]
    fn from_date_with_offset_positive_offset_no_wrap() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date_with_offset("2026-05-01".parse::<Date>()?, 2)?;

        assert_eq!(week.year(), 2026);
        assert_eq!(week.week(), 18);
        assert_eq!(week.week_start_offset(), 2);

        Ok(())
    }

    #[test]
    fn from_date_with_offset_negative_offset_no_wrap() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::from_date_with_offset("2026-05-01".parse::<Date>()?, -2)?;

        assert_eq!(week.year(), 2026);
        assert_eq!(week.week(), 18);
        assert_eq!(week.week_start_offset(), -2);

        Ok(())
    }

    #[test]
    fn start_end_weekday() -> Result<(), Box<dyn Error>> {
        let positive_offset_week = OffsetIsoWeek::new_with_offset(2026, 1, 5)?;

        assert_eq!(positive_offset_week.start_weekday(), Weekday::Saturday);
        assert_eq!(positive_offset_week.end_weekday(), Weekday::Friday);

        let negative_offset_week = OffsetIsoWeek::new_with_offset(2026, 1, -5)?;

        assert_eq!(negative_offset_week.start_weekday(), Weekday::Wednesday);
        assert_eq!(negative_offset_week.end_weekday(), Weekday::Tuesday);

        Ok(())
    }

    #[test]
    fn zero_one_based_nth_day() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::new_with_offset(2026, 1, 5)?;
        let expected_date = "2026-01-07".parse::<Date>()?;

        assert_eq!(week.zero_based_nth_day(4)?, expected_date);
        assert_eq!(week.one_based_nth_day(5)?, expected_date);

        Ok(())
    }

    #[test]
    fn zero_one_based_nth_day_out_of_range() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::new_with_offset(2026, 1, 5)?;

        assert_eq!(week.zero_based_nth_day(7), Err(OffsetIsoWeekDateError));
        assert_eq!(week.one_based_nth_day(0), Err(OffsetIsoWeekDateError));
        assert_eq!(week.one_based_nth_day(8), Err(OffsetIsoWeekDateError));

        Ok(())
    }

    #[test]
    fn weekday_date() -> Result<(), Box<dyn Error>> {
        let week = OffsetIsoWeek::new_with_offset(2026, 1, 5)?;

        assert_eq!(week.weekday_date(Weekday::Monday)?, "2026-01-05".parse::<Date>()?);
        assert_eq!(week.weekday_date(Weekday::Wednesday)?, "2026-01-07".parse::<Date>()?);
        assert_eq!(week.weekday_date(Weekday::Friday)?, "2026-01-09".parse::<Date>()?);
        assert_eq!(week.weekday_date(Weekday::Sunday)?, "2026-01-04".parse::<Date>()?);

        Ok(())
    }
}

mod month {
    use super::*;

    #[test]
    fn try_from_zero_offset() {
        assert_eq!(Month::try_from_zero_offset(0), Ok(Month::January));
        assert_eq!(Month::try_from_zero_offset(1), Ok(Month::February));
        assert_eq!(Month::try_from_zero_offset(2), Ok(Month::March));
        assert_eq!(Month::try_from_zero_offset(3), Ok(Month::April));
        assert_eq!(Month::try_from_zero_offset(4), Ok(Month::May));
        assert_eq!(Month::try_from_zero_offset(5), Ok(Month::June));
        assert_eq!(Month::try_from_zero_offset(6), Ok(Month::July));
        assert_eq!(Month::try_from_zero_offset(7), Ok(Month::August));
        assert_eq!(Month::try_from_zero_offset(8), Ok(Month::September));
        assert_eq!(Month::try_from_zero_offset(9), Ok(Month::October));
        assert_eq!(Month::try_from_zero_offset(10), Ok(Month::November));
        assert_eq!(Month::try_from_zero_offset(11), Ok(Month::December));
    }

    #[test]
    fn try_from_zero_offset_out_of_range() {
        assert_eq!(Month::try_from_zero_offset(12), Err(MonthTryFromNumberError));
    }

    #[test]
    fn try_from_one_offset() {
        assert_eq!(Month::try_from_one_offset(1), Ok(Month::January));
        assert_eq!(Month::try_from_one_offset(2), Ok(Month::February));
        assert_eq!(Month::try_from_one_offset(3), Ok(Month::March));
        assert_eq!(Month::try_from_one_offset(4), Ok(Month::April));
        assert_eq!(Month::try_from_one_offset(5), Ok(Month::May));
        assert_eq!(Month::try_from_one_offset(6), Ok(Month::June));
        assert_eq!(Month::try_from_one_offset(7), Ok(Month::July));
        assert_eq!(Month::try_from_one_offset(8), Ok(Month::August));
        assert_eq!(Month::try_from_one_offset(9), Ok(Month::September));
        assert_eq!(Month::try_from_one_offset(10), Ok(Month::October));
        assert_eq!(Month::try_from_one_offset(11), Ok(Month::November));
        assert_eq!(Month::try_from_one_offset(12), Ok(Month::December));
    }

    #[test]
    fn try_from_one_offset_out_of_range() {
        assert_eq!(Month::try_from_one_offset(0), Err(MonthTryFromNumberError));
        assert_eq!(Month::try_from_one_offset(13), Err(MonthTryFromNumberError));
    }

    #[test]
    fn zero_offset_number() {
        assert_eq!(Month::January.zero_offset_number(), 0);
        assert_eq!(Month::February.zero_offset_number(), 1);
        assert_eq!(Month::March.zero_offset_number(), 2);
        assert_eq!(Month::April.zero_offset_number(), 3);
        assert_eq!(Month::May.zero_offset_number(), 4);
        assert_eq!(Month::June.zero_offset_number(), 5);
        assert_eq!(Month::July.zero_offset_number(), 6);
        assert_eq!(Month::August.zero_offset_number(), 7);
        assert_eq!(Month::September.zero_offset_number(), 8);
        assert_eq!(Month::October.zero_offset_number(), 9);
        assert_eq!(Month::November.zero_offset_number(), 10);
        assert_eq!(Month::December.zero_offset_number(), 11);
    }

    #[test]
    fn one_offset_number() {
        assert_eq!(Month::January.one_offset_number(), 1);
        assert_eq!(Month::February.one_offset_number(), 2);
        assert_eq!(Month::March.one_offset_number(), 3);
        assert_eq!(Month::April.one_offset_number(), 4);
        assert_eq!(Month::May.one_offset_number(), 5);
        assert_eq!(Month::June.one_offset_number(), 6);
        assert_eq!(Month::July.one_offset_number(), 7);
        assert_eq!(Month::August.one_offset_number(), 8);
        assert_eq!(Month::September.one_offset_number(), 9);
        assert_eq!(Month::October.one_offset_number(), 10);
        assert_eq!(Month::November.one_offset_number(), 11);
        assert_eq!(Month::December.one_offset_number(), 12);
    }

    #[test]
    fn from_month_in_year() {
        assert_eq!(Month::from(MonthInYear::new(2026, Month::April)), Month::April);
    }

    #[test]
    fn try_from_date() -> Result<(), Box<dyn Error>> {
        assert_eq!(Month::try_from("2026-04-23".parse::<Date>()?)?, Month::April);
        Ok(())
    }
}

mod month_in_year {
    use super::*;

    #[test]
    fn month_first_and_last_days() -> Result<(), Box<dyn Error>> {
        let month = MonthInYear::new(2026, Month::May);
        assert_eq!(month.first_day()?, "2026-05-01".parse::<Date>()?);
        assert_eq!(month.last_day()?, "2026-05-31".parse::<Date>()?);
        Ok(())
    }
}

mod calendar_anchor_offset {
    use super::*;

    #[test]
    fn calendar_anchor_offset_days_is_zero() {
        assert!(!CalendarAnchorOffset::Days(1).is_zero());
        assert!(CalendarAnchorOffset::Days(0).is_zero());
        assert!(!CalendarAnchorOffset::Days(-1).is_zero());
    }

    #[test]
    fn calendar_anchor_offset_weeks_is_zero() {
        assert!(!CalendarAnchorOffset::Weeks(1, Weekday::Monday).is_zero());
        assert!(CalendarAnchorOffset::Weeks(0, Weekday::Monday).is_zero());
        assert!(!CalendarAnchorOffset::Weeks(-1, Weekday::Monday).is_zero());
    }

    #[test]
    fn calendar_anchor_offset_months_is_zero() {
        assert!(!CalendarAnchorOffset::Months(1).is_zero());
        assert!(CalendarAnchorOffset::Months(0).is_zero());
        assert!(!CalendarAnchorOffset::Months(-1).is_zero());
    }

    #[test]
    fn calendar_anchor_offset_years_is_zero() {
        assert!(!CalendarAnchorOffset::Years(1).is_zero());
        assert!(CalendarAnchorOffset::Years(0).is_zero());
        assert!(!CalendarAnchorOffset::Years(-1).is_zero());
    }

    #[test]
    fn calendar_anchor_offset_days_is_positive() {
        assert!(CalendarAnchorOffset::Days(1).is_positive());
        assert!(!CalendarAnchorOffset::Days(0).is_positive());
        assert!(!CalendarAnchorOffset::Days(-1).is_positive());
    }

    #[test]
    fn calendar_anchor_offset_weeks_is_positive() {
        assert!(CalendarAnchorOffset::Weeks(1, Weekday::Monday).is_positive());
        assert!(!CalendarAnchorOffset::Weeks(0, Weekday::Monday).is_positive());
        assert!(!CalendarAnchorOffset::Weeks(-1, Weekday::Monday).is_positive());
    }

    #[test]
    fn calendar_anchor_offset_months_is_positive() {
        assert!(CalendarAnchorOffset::Months(1).is_positive());
        assert!(!CalendarAnchorOffset::Months(0).is_positive());
        assert!(!CalendarAnchorOffset::Months(-1).is_positive());
    }

    #[test]
    fn calendar_anchor_offset_years_is_positive() {
        assert!(CalendarAnchorOffset::Years(1).is_positive());
        assert!(!CalendarAnchorOffset::Years(0).is_positive());
        assert!(!CalendarAnchorOffset::Years(-1).is_positive());
    }

    #[test]
    fn calendar_anchor_offset_days_is_negative() {
        assert!(!CalendarAnchorOffset::Days(1).is_negative());
        assert!(!CalendarAnchorOffset::Days(0).is_negative());
        assert!(CalendarAnchorOffset::Days(-1).is_negative());
    }

    #[test]
    fn calendar_anchor_offset_weeks_is_negative() {
        assert!(!CalendarAnchorOffset::Weeks(1, Weekday::Monday).is_negative());
        assert!(!CalendarAnchorOffset::Weeks(0, Weekday::Monday).is_negative());
        assert!(CalendarAnchorOffset::Weeks(-1, Weekday::Monday).is_negative());
    }

    #[test]
    fn calendar_anchor_offset_months_is_negative() {
        assert!(!CalendarAnchorOffset::Months(1).is_negative());
        assert!(!CalendarAnchorOffset::Months(0).is_negative());
        assert!(CalendarAnchorOffset::Months(-1).is_negative());
    }

    #[test]
    fn calendar_anchor_offset_years_is_negative() {
        assert!(!CalendarAnchorOffset::Years(1).is_negative());
        assert!(!CalendarAnchorOffset::Years(0).is_negative());
        assert!(CalendarAnchorOffset::Years(-1).is_negative());
    }

    #[test]
    fn calendar_anchor_offset_cant_compare_different_units() {
        assert_eq!(
            CalendarAnchorOffset::Days(1).partial_cmp(&CalendarAnchorOffset::Weeks(1, Weekday::Monday)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Days(1).partial_cmp(&CalendarAnchorOffset::Months(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Days(1).partial_cmp(&CalendarAnchorOffset::Years(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Weeks(1, Weekday::Monday).partial_cmp(&CalendarAnchorOffset::Days(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Weeks(1, Weekday::Monday).partial_cmp(&CalendarAnchorOffset::Months(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Weeks(1, Weekday::Monday).partial_cmp(&CalendarAnchorOffset::Years(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Months(1).partial_cmp(&CalendarAnchorOffset::Days(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Months(1).partial_cmp(&CalendarAnchorOffset::Weeks(1, Weekday::Monday)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Months(1).partial_cmp(&CalendarAnchorOffset::Years(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Years(1).partial_cmp(&CalendarAnchorOffset::Days(1)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Years(1).partial_cmp(&CalendarAnchorOffset::Weeks(1, Weekday::Monday)),
            None
        );
        assert_eq!(
            CalendarAnchorOffset::Years(1).partial_cmp(&CalendarAnchorOffset::Months(1)),
            None
        );
    }

    #[test]
    fn calendar_anchor_offset_compare_days() {
        assert_eq!(
            CalendarAnchorOffset::Days(1).partial_cmp(&CalendarAnchorOffset::Days(0)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            CalendarAnchorOffset::Days(0).partial_cmp(&CalendarAnchorOffset::Days(1)),
            Some(Ordering::Less)
        );
        assert_eq!(
            CalendarAnchorOffset::Days(0).partial_cmp(&CalendarAnchorOffset::Days(0)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn calendar_anchor_offset_compare_weeks_same_ref_day() {
        assert_eq!(
            CalendarAnchorOffset::Weeks(1, Weekday::Monday)
                .partial_cmp(&CalendarAnchorOffset::Weeks(0, Weekday::Monday)),
            Some(Ordering::Greater),
        );
        assert_eq!(
            CalendarAnchorOffset::Weeks(0, Weekday::Monday)
                .partial_cmp(&CalendarAnchorOffset::Weeks(1, Weekday::Monday)),
            Some(Ordering::Less),
        );
        assert_eq!(
            CalendarAnchorOffset::Weeks(0, Weekday::Monday)
                .partial_cmp(&CalendarAnchorOffset::Weeks(0, Weekday::Monday)),
            Some(Ordering::Equal),
        );
    }

    #[test]
    fn calendar_anchor_offset_compare_weeks_different_ref_day() {
        assert_eq!(
            CalendarAnchorOffset::Weeks(1, Weekday::Monday)
                .partial_cmp(&CalendarAnchorOffset::Weeks(0, Weekday::Sunday)),
            Some(Ordering::Greater),
        );
        assert_eq!(
            CalendarAnchorOffset::Weeks(0, Weekday::Monday)
                .partial_cmp(&CalendarAnchorOffset::Weeks(1, Weekday::Sunday)),
            Some(Ordering::Less),
        );
        assert_eq!(
            CalendarAnchorOffset::Weeks(0, Weekday::Monday)
                .partial_cmp(&CalendarAnchorOffset::Weeks(0, Weekday::Sunday)),
            Some(Ordering::Equal),
        );
    }

    #[test]
    fn calendar_anchor_offset_compare_months() {
        assert_eq!(
            CalendarAnchorOffset::Months(1).partial_cmp(&CalendarAnchorOffset::Months(0)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            CalendarAnchorOffset::Months(0).partial_cmp(&CalendarAnchorOffset::Months(1)),
            Some(Ordering::Less)
        );
        assert_eq!(
            CalendarAnchorOffset::Months(0).partial_cmp(&CalendarAnchorOffset::Months(0)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn calendar_anchor_offset_compare_years() {
        assert_eq!(
            CalendarAnchorOffset::Years(1).partial_cmp(&CalendarAnchorOffset::Years(0)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            CalendarAnchorOffset::Years(0).partial_cmp(&CalendarAnchorOffset::Years(1)),
            Some(Ordering::Less)
        );
        assert_eq!(
            CalendarAnchorOffset::Years(0).partial_cmp(&CalendarAnchorOffset::Years(0)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_zero_days() -> Result<(), Box<dyn Error>> {
        let date = "2026-05-01".parse::<Date>()?;

        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(0), date)?,
            date,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_positive_days() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(420), "2026-05-01".parse::<Date>()?,)?,
            "2027-06-25".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_negative_days() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Days(-420),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2025-03-07".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_zero_weeks_monday_ref() -> Result<(), Box<dyn Error>> {
        // Per `checked_add_calendar_anchor_offset_to_date`'s doc, adding weeks to get a day
        // returns the first day of the week.
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-04-27".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_zero_weeks_sunday_ref() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-04-26".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_zero_weeks_monday_ref_on_sunday() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                "2026-02-08".parse::<Date>()?,
            )?,
            "2026-02-02".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_zero_weeks_sunday_ref_on_sunday() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                "2026-02-08".parse::<Date>()?,
            )?,
            "2026-02-08".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_positive_weeks() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(15, Weekday::Monday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-08-10".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_negative_weeks() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(-10, Weekday::Monday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-02-16".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_zero_months() -> Result<(), Box<dyn Error>> {
        // Per `checked_add_calendar_anchor_offset_to_date`'s doc, adding months to get a day
        // returns the first day of the month.
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(0), "2026-05-20".parse::<Date>()?,)?,
            "2026-05-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_positive_months_no_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(30),
                "2026-05-20".parse::<Date>()?,
            )?,
            "2028-11-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_positive_months_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(30),
                "2026-10-20".parse::<Date>()?,
            )?,
            "2029-04-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_negative_months_no_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(-30),
                "2026-08-20".parse::<Date>()?,
            )?,
            "2024-02-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_negative_months_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(-30),
                "2026-05-20".parse::<Date>()?,
            )?,
            "2023-11-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_zero_years() -> Result<(), Box<dyn Error>> {
        // Per `checked_add_calendar_anchor_offset_to_date`'s doc, adding years to get a day
        // returns the first day of the year.
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(0), "2026-05-20".parse::<Date>()?,)?,
            "2026-01-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_positive_years() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(10), "2026-05-20".parse::<Date>()?,)?,
            "2036-01-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_add_calendar_anchor_offset_to_date_negative_years() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_add_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Years(-10),
                "2026-05-20".parse::<Date>()?,
            )?,
            "2016-01-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_zero_days() -> Result<(), Box<dyn Error>> {
        let date = "2026-05-01".parse::<Date>()?;

        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(0), date)?,
            date,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_positive_days() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(420), "2026-05-01".parse::<Date>()?,)?,
            "2025-03-07".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_negative_days() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Days(-420),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2027-06-25".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_zero_weeks_monday_ref() -> Result<(), Box<dyn Error>> {
        // Per `checked_sub_calendar_anchor_offset_to_date`'s doc, subtracting weeks to get a day
        // returns the first day of the week.
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-04-27".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_zero_weeks_sunday_ref() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-04-26".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_zero_weeks_monday_ref_on_sunday() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                "2026-02-08".parse::<Date>()?,
            )?,
            "2026-02-02".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_zero_weeks_sunday_ref_on_sunday() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                "2026-02-08".parse::<Date>()?,
            )?,
            "2026-02-08".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_positive_weeks() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(15, Weekday::Monday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-01-12".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_negative_weeks() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Weeks(-10, Weekday::Monday),
                "2026-05-01".parse::<Date>()?,
            )?,
            "2026-07-06".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_zero_months() -> Result<(), Box<dyn Error>> {
        // Per `checked_sub_calendar_anchor_offset_to_date`'s doc, subtracting months to get a day
        // returns the first day of the month.
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(0), "2026-05-20".parse::<Date>()?,)?,
            "2026-05-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_positive_months_no_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(30),
                "2026-08-20".parse::<Date>()?,
            )?,
            "2024-02-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_positive_months_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(30),
                "2026-05-20".parse::<Date>()?,
            )?,
            "2023-11-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_negative_months_no_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(-30),
                "2026-10-20".parse::<Date>()?,
            )?,
            "2029-04-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_negative_months_extra_year() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Months(-30),
                "2026-05-20".parse::<Date>()?,
            )?,
            "2028-11-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_zero_years() -> Result<(), Box<dyn Error>> {
        // Per `checked_sub_calendar_anchor_offset_to_date`'s doc, adding years to get a day
        // returns the first day of the year.
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(0), "2026-05-20".parse::<Date>()?,)?,
            "2026-01-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_positive_years() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(10), "2026-05-20".parse::<Date>()?,)?,
            "2016-01-01".parse::<Date>()?,
        );
        Ok(())
    }

    #[test]
    fn checked_sub_calendar_anchor_offset_to_date_negative_years() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            checked_sub_calendar_anchor_offset_to_date(
                CalendarAnchorOffset::Years(-10),
                "2026-05-20".parse::<Date>()?,
            )?,
            "2036-01-01".parse::<Date>()?,
        );
        Ok(())
    }
}

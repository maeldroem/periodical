use std::cmp::Ordering;

use jiff::civil::{Date, Weekday, date};
use jiff::tz::TimeZone;

use super::time::*;
use crate::test_utils::MOCK_TODAY_DATE;

#[test]
fn mockable_date_today_mock() {
    assert_eq!(mockable_date_today(true, TimeZone::UTC), MOCK_TODAY_DATE);
    assert_eq!(mockable_date_today(true, TimeZone::unknown()), MOCK_TODAY_DATE);
}

#[test]
fn mockable_date_today_no_mock() {
    let _ = mockable_date_today(false, TimeZone::UTC);
}

#[test]
fn date_today_returns_mock_date() {
    assert_eq!(date_today(TimeZone::UTC), MOCK_TODAY_DATE);
    assert_eq!(date_today(TimeZone::unknown()), MOCK_TODAY_DATE);
}

mod iso_weeks_in_year_fn {
    use super::*;

    #[test]
    fn short_year() {
        let short_years = [
            2025, 2024, 2023, 2022, 2021, 2019, 2018, 2017, 2016, 2014, 2013, 2012, 2011, 2010,
        ];

        for short_year in short_years {
            assert_eq!(
                iso_weeks_in_year(short_year).unwrap(),
                ISO_WEEKS_IN_SHORT_YEAR,
                "Expecting short ISO year for year {short_year}",
            );
        }
    }

    #[test]
    fn long_year() {
        let long_years = [2026, 2020, 2015, 2009];

        for long_year in long_years {
            assert_eq!(
                iso_weeks_in_year(long_year).unwrap(),
                ISO_WEEKS_IN_LONG_YEAR,
                "Expecting long ISO year for year {long_year}",
            );
        }
    }
}

mod offset_iso_week {
    use super::*;

    #[test]
    fn new_without_offset() {
        let iso_week = OffsetIsoWeek::new(2026, 5).unwrap();
        assert_eq!(iso_week.first_day().unwrap(), date(2026, 1, 26));
        assert_eq!(iso_week.last_day().unwrap(), date(2026, 2, 1));
    }

    mod new_with_offset {
        use super::*;

        #[test]
        fn offset_sunday() {
            let offset_iso_week = OffsetIsoWeek::new_with_offset(2026, 5, -1).unwrap();
            assert_eq!(offset_iso_week.first_day().unwrap(), date(2026, 1, 25));
            assert_eq!(offset_iso_week.last_day().unwrap(), date(2026, 1, 31));
        }

        #[test]
        fn offset_wednesday() {
            let offset_iso_week = OffsetIsoWeek::new_with_offset(2026, 5, 2).unwrap();
            assert_eq!(offset_iso_week.first_day().unwrap(), date(2026, 1, 28));
            assert_eq!(offset_iso_week.last_day().unwrap(), date(2026, 2, 3));
        }

        #[test]
        fn out_of_range_week_zero() {
            assert_eq!(
                OffsetIsoWeek::new(2026, 0),
                Err(OffsetIsoWeekCreationError::OutOfRangeWeek)
            );
        }

        #[test]
        fn out_of_range_week() {
            assert_eq!(
                OffsetIsoWeek::new(2026, 55),
                Err(OffsetIsoWeekCreationError::OutOfRangeWeek)
            );
        }

        #[test]
        fn out_of_range_offset() {
            assert_eq!(
                OffsetIsoWeek::new_with_offset(2026, 5, -10),
                Err(OffsetIsoWeekCreationError::OutOfRangeOffset)
            );
            assert_eq!(
                OffsetIsoWeek::new_with_offset(2026, 5, 10),
                Err(OffsetIsoWeekCreationError::OutOfRangeOffset)
            );
        }
    }

    #[test]
    fn from_date() {
        let week = OffsetIsoWeek::from_date(date(2023, 1, 1)).unwrap();

        assert_eq!(week.year(), 2022);
        assert_eq!(week.week(), 52);
        assert_eq!(week.week_start_offset(), 0);
    }

    mod from_date_with_offset {
        use super::*;

        #[test]
        fn out_of_range_offset() {
            assert_eq!(
                OffsetIsoWeek::from_date_with_offset(date(2026, 1, 1), -10),
                Err(OffsetIsoWeekCreationError::OutOfRangeOffset),
            );
            assert_eq!(
                OffsetIsoWeek::from_date_with_offset(date(2026, 1, 1), 10),
                Err(OffsetIsoWeekCreationError::OutOfRangeOffset),
            );
        }

        #[test]
        fn no_offset() {
            let week = OffsetIsoWeek::from_date_with_offset(date(2026, 5, 1), 0).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 18);
            assert_eq!(week.week_start_offset(), 0);
        }

        #[test]
        fn positive_offset_year_wrap() {
            let week = OffsetIsoWeek::from_date_with_offset(date(2025, 12, 31), 5).unwrap();

            assert_eq!(week.year(), 2025);
            assert_eq!(week.week(), 52);
            assert_eq!(week.week_start_offset(), 5);
        }

        #[test]
        fn negative_offset_year_wrap() {
            let week = OffsetIsoWeek::from_date_with_offset(date(2025, 12, 25), -5).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 1);
            assert_eq!(week.week_start_offset(), -5);
        }

        #[test]
        fn positive_offset_week_wrap() {
            let week = OffsetIsoWeek::from_date_with_offset(date(2026, 5, 1), 5).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 17);
            assert_eq!(week.week_start_offset(), 5);
        }

        #[test]
        fn negative_offset_week_wrap() {
            let week = OffsetIsoWeek::from_date_with_offset(date(2026, 5, 1), -5).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 19);
            assert_eq!(week.week_start_offset(), -5);
        }

        #[test]
        fn positive_offset_no_wrap() {
            let week = OffsetIsoWeek::from_date_with_offset(date(2026, 5, 1), 2).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 18);
            assert_eq!(week.week_start_offset(), 2);
        }

        #[test]
        fn negative_offset_no_wrap() {
            let week = OffsetIsoWeek::from_date_with_offset(date(2026, 5, 1), -2).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 18);
            assert_eq!(week.week_start_offset(), -2);
        }
    }

    #[test]
    fn start_end_weekday() {
        let positive_offset_week = OffsetIsoWeek::new_with_offset(2026, 1, 5).unwrap();

        assert_eq!(positive_offset_week.start_weekday(), Weekday::Saturday);
        assert_eq!(positive_offset_week.end_weekday(), Weekday::Friday);

        let negative_offset_week = OffsetIsoWeek::new_with_offset(2026, 1, -5).unwrap();

        assert_eq!(negative_offset_week.start_weekday(), Weekday::Wednesday);
        assert_eq!(negative_offset_week.end_weekday(), Weekday::Tuesday);
    }

    #[test]
    fn zero_one_based_nth_day() {
        let week = OffsetIsoWeek::new_with_offset(2026, 1, 5).unwrap();
        let expected_date = date(2026, 1, 7);

        assert_eq!(week.zero_based_nth_day(4).unwrap(), expected_date);
        assert_eq!(week.one_based_nth_day(5).unwrap(), expected_date);
    }

    #[test]
    fn zero_one_based_nth_day_out_of_range() {
        let week = OffsetIsoWeek::new_with_offset(2026, 1, 5).unwrap();

        assert_eq!(week.zero_based_nth_day(7), Err(OffsetIsoWeekDateError));
        assert_eq!(week.one_based_nth_day(0), Err(OffsetIsoWeekDateError));
        assert_eq!(week.one_based_nth_day(8), Err(OffsetIsoWeekDateError));
    }

    #[test]
    fn weekday_date() {
        let week = OffsetIsoWeek::new_with_offset(2026, 1, 5).unwrap();

        assert_eq!(week.weekday_date(Weekday::Monday).unwrap(), date(2026, 1, 5));
        assert_eq!(week.weekday_date(Weekday::Wednesday).unwrap(), date(2026, 1, 7));
        assert_eq!(week.weekday_date(Weekday::Friday).unwrap(), date(2026, 1, 9));
        assert_eq!(week.weekday_date(Weekday::Sunday).unwrap(), date(2026, 1, 4));
    }

    mod try_from_impl_on_date {
        use super::*;

        #[test]
        fn ok() {
            let week = OffsetIsoWeek::try_from(date(2023, 1, 1)).unwrap();

            assert_eq!(week.year(), 2022);
            assert_eq!(week.week(), 52);
            assert_eq!(week.week_start_offset(), 0);
        }
    }

    mod try_from_impl_on_date_i8_tuple {
        use super::*;

        #[test]
        fn out_of_range_offset() {
            assert_eq!(
                OffsetIsoWeek::try_from((date(2026, 1, 1), -10)),
                Err(OffsetIsoWeekCreationError::OutOfRangeOffset),
            );
            assert_eq!(
                OffsetIsoWeek::try_from((date(2026, 1, 1), 10)),
                Err(OffsetIsoWeekCreationError::OutOfRangeOffset),
            );
        }

        #[test]
        fn no_offset() {
            let week = OffsetIsoWeek::try_from((date(2026, 5, 1), 0)).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 18);
            assert_eq!(week.week_start_offset(), 0);
        }

        #[test]
        fn positive_offset_year_wrap() {
            let week = OffsetIsoWeek::try_from((date(2025, 12, 31), 5)).unwrap();

            assert_eq!(week.year(), 2025);
            assert_eq!(week.week(), 52);
            assert_eq!(week.week_start_offset(), 5);
        }

        #[test]
        fn negative_offset_year_wrap() {
            let week = OffsetIsoWeek::try_from((date(2025, 12, 25), -5)).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 1);
            assert_eq!(week.week_start_offset(), -5);
        }

        #[test]
        fn positive_offset_week_wrap() {
            let week = OffsetIsoWeek::try_from((date(2026, 5, 1), 5)).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 17);
            assert_eq!(week.week_start_offset(), 5);
        }

        #[test]
        fn negative_offset_week_wrap() {
            let week = OffsetIsoWeek::try_from((date(2026, 5, 1), -5)).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 19);
            assert_eq!(week.week_start_offset(), -5);
        }

        #[test]
        fn positive_offset_no_wrap() {
            let week = OffsetIsoWeek::try_from((date(2026, 5, 1), 2)).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 18);
            assert_eq!(week.week_start_offset(), 2);
        }

        #[test]
        fn negative_offset_no_wrap() {
            let week = OffsetIsoWeek::try_from((date(2026, 5, 1), -2)).unwrap();

            assert_eq!(week.year(), 2026);
            assert_eq!(week.week(), 18);
            assert_eq!(week.week_start_offset(), -2);
        }
    }
}

mod month {
    use super::*;

    mod try_from_zero_offset {
        use super::*;

        #[test]
        fn ok() {
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
        fn out_of_range() {
            assert_eq!(Month::try_from_zero_offset(12), Err(MonthTryFromNumberError));
        }
    }

    mod try_from_one_offset {
        use super::*;

        #[test]
        fn ok() {
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
        fn out_of_range() {
            assert_eq!(Month::try_from_one_offset(0), Err(MonthTryFromNumberError));
            assert_eq!(Month::try_from_one_offset(13), Err(MonthTryFromNumberError));
        }
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
    fn try_from_date() {
        assert_eq!(Month::try_from(date(2026, 4, 23)).unwrap(), Month::April);
    }
}

mod month_in_year {
    use super::*;

    #[test]
    fn month_first_and_last_days() {
        let month = MonthInYear::new(2026, Month::May);
        assert_eq!(month.first_day().unwrap(), date(2026, 5, 1));
        assert_eq!(month.last_day().unwrap(), date(2026, 5, 31));
    }
}

mod calendar_anchor_offset {
    use super::*;

    mod is_zero {
        use super::*;

        #[test]
        fn days() {
            assert!(!CalendarAnchorOffset::Days(1).is_zero());
            assert!(CalendarAnchorOffset::Days(0).is_zero());
            assert!(!CalendarAnchorOffset::Days(-1).is_zero());
        }

        #[test]
        fn weeks() {
            assert!(!CalendarAnchorOffset::Weeks(1, Weekday::Monday).is_zero());
            assert!(CalendarAnchorOffset::Weeks(0, Weekday::Monday).is_zero());
            assert!(!CalendarAnchorOffset::Weeks(-1, Weekday::Monday).is_zero());
        }

        #[test]
        fn months() {
            assert!(!CalendarAnchorOffset::Months(1).is_zero());
            assert!(CalendarAnchorOffset::Months(0).is_zero());
            assert!(!CalendarAnchorOffset::Months(-1).is_zero());
        }

        #[test]
        fn years() {
            assert!(!CalendarAnchorOffset::Years(1).is_zero());
            assert!(CalendarAnchorOffset::Years(0).is_zero());
            assert!(!CalendarAnchorOffset::Years(-1).is_zero());
        }
    }

    mod is_positive {
        use super::*;

        #[test]
        fn days() {
            assert!(CalendarAnchorOffset::Days(1).is_positive());
            assert!(!CalendarAnchorOffset::Days(0).is_positive());
            assert!(!CalendarAnchorOffset::Days(-1).is_positive());
        }

        #[test]
        fn weeks() {
            assert!(CalendarAnchorOffset::Weeks(1, Weekday::Monday).is_positive());
            assert!(!CalendarAnchorOffset::Weeks(0, Weekday::Monday).is_positive());
            assert!(!CalendarAnchorOffset::Weeks(-1, Weekday::Monday).is_positive());
        }

        #[test]
        fn months() {
            assert!(CalendarAnchorOffset::Months(1).is_positive());
            assert!(!CalendarAnchorOffset::Months(0).is_positive());
            assert!(!CalendarAnchorOffset::Months(-1).is_positive());
        }

        #[test]
        fn years() {
            assert!(CalendarAnchorOffset::Years(1).is_positive());
            assert!(!CalendarAnchorOffset::Years(0).is_positive());
            assert!(!CalendarAnchorOffset::Years(-1).is_positive());
        }
    }

    mod is_negative {
        use super::*;

        #[test]
        fn days() {
            assert!(!CalendarAnchorOffset::Days(1).is_negative());
            assert!(!CalendarAnchorOffset::Days(0).is_negative());
            assert!(CalendarAnchorOffset::Days(-1).is_negative());
        }

        #[test]
        fn weeks() {
            assert!(!CalendarAnchorOffset::Weeks(1, Weekday::Monday).is_negative());
            assert!(!CalendarAnchorOffset::Weeks(0, Weekday::Monday).is_negative());
            assert!(CalendarAnchorOffset::Weeks(-1, Weekday::Monday).is_negative());
        }

        #[test]
        fn months() {
            assert!(!CalendarAnchorOffset::Months(1).is_negative());
            assert!(!CalendarAnchorOffset::Months(0).is_negative());
            assert!(CalendarAnchorOffset::Months(-1).is_negative());
        }

        #[test]
        fn years() {
            assert!(!CalendarAnchorOffset::Years(1).is_negative());
            assert!(!CalendarAnchorOffset::Years(0).is_negative());
            assert!(CalendarAnchorOffset::Years(-1).is_negative());
        }
    }

    mod cmp {
        use super::*;

        #[test]
        fn cant_compare_different_units() {
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
        fn days() {
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
        fn weeks_same_ref_day() {
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
        fn weeks_different_ref_day() {
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
        fn months() {
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
        fn years() {
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
    }

    mod checked_add_calendar_anchor_offset_to_date {
        use super::*;

        #[test]
        fn zero_days() {
            let date = date(2026, 5, 1);

            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(0), date).unwrap(),
                date,
            );
        }

        #[test]
        fn positive_days() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(420), date(2026, 5, 1),).unwrap(),
                date(2027, 6, 25),
            );
        }

        #[test]
        fn negative_days() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(-420), date(2026, 5, 1),)
                    .unwrap(),
                date(2025, 3, 7),
            );
        }

        #[test]
        fn zero_weeks_monday_ref() {
            // Per `checked_add_calendar_anchor_offset_to_date`'s doc, adding weeks to get a day
            // returns the first day of the week.
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 4, 27),
            );
        }

        #[test]
        fn zero_weeks_sunday_ref() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 4, 26),
            );
        }

        #[test]
        fn zero_weeks_monday_ref_on_sunday() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                    date(2026, 2, 8),
                )
                .unwrap(),
                date(2026, 2, 2),
            );
        }

        #[test]
        fn zero_weeks_sunday_ref_on_sunday() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                    date(2026, 2, 8),
                )
                .unwrap(),
                date(2026, 2, 8),
            );
        }

        #[test]
        fn positive_weeks() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(15, Weekday::Monday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 8, 10),
            );
        }

        #[test]
        fn negative_weeks() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(-10, Weekday::Monday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 2, 16),
            );
        }

        #[test]
        fn zero_iso_weeks() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::IsoWeeks(0), date(2026, 4, 23),)
                    .unwrap(),
                date(2026, 4, 20),
            );
        }

        #[test]
        fn positive_iso_weeks() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::IsoWeeks(10), date(2026, 5, 1),)
                    .unwrap(),
                date(2026, 7, 6),
            );
        }

        #[test]
        fn negative_iso_weeks() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::IsoWeeks(-10), date(2026, 5, 1),)
                    .unwrap(),
                date(2026, 2, 16),
            );
        }

        #[test]
        fn zero_months() {
            // Per `checked_add_calendar_anchor_offset_to_date`'s doc, adding months to get a day
            // returns the first day of the month.
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(0), date(2026, 5, 20),)
                    .unwrap(),
                date(2026, 5, 1),
            );
        }

        #[test]
        fn positive_months_no_extra_year() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(30), date(2026, 5, 20),)
                    .unwrap(),
                date(2028, 11, 1),
            );
        }

        #[test]
        fn positive_months_extra_year() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(30), date(2026, 10, 20),)
                    .unwrap(),
                date(2029, 4, 1),
            );
        }

        #[test]
        fn negative_months_no_extra_year() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(-30), date(2026, 8, 20),)
                    .unwrap(),
                date(2024, 2, 1),
            );
        }

        #[test]
        fn negative_months_extra_year() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(-30), date(2026, 5, 20),)
                    .unwrap(),
                date(2023, 11, 1),
            );
        }

        #[test]
        fn zero_years() {
            // Per `checked_add_calendar_anchor_offset_to_date`'s doc, adding years to get a day
            // returns the first day of the year.
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(0), date(2026, 5, 20),).unwrap(),
                date(2026, 1, 1),
            );
        }

        #[test]
        fn positive_years() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(10), date(2026, 5, 20),)
                    .unwrap(),
                date(2036, 1, 1),
            );
        }

        #[test]
        fn negative_years() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(-10), date(2026, 5, 20),)
                    .unwrap(),
                date(2016, 1, 1),
            );
        }

        #[test]
        fn offset_too_large() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(i32::MAX), date(2026, 5, 1),),
                Err(CalendarAnchorOffsetDateError::OffsetTooLarge),
            );
        }

        #[test]
        fn out_of_range_result() {
            assert_eq!(
                checked_add_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Years(7974), // Will make year 10'000, not supported by jiff
                    date(2026, 5, 1),
                ),
                Err(CalendarAnchorOffsetDateError::OutOfRangeResult),
            );
        }
    }

    mod checked_sub_calendar_anchor_offset_to_date {
        use super::*;

        #[test]
        fn zero_days() {
            let date = date(2026, 5, 1);

            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(0), date).unwrap(),
                date,
            );
        }

        #[test]
        fn positive_days() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(420), date(2026, 5, 1),).unwrap(),
                date(2025, 3, 7),
            );
        }

        #[test]
        fn negative_days() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(-420), date(2026, 5, 1),)
                    .unwrap(),
                date(2027, 6, 25),
            );
        }

        #[test]
        fn zero_weeks_monday_ref() {
            // Per `checked_sub_calendar_anchor_offset_to_date`'s doc, subtracting weeks to get a day
            // returns the first day of the week.
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 4, 27),
            );
        }

        #[test]
        fn zero_weeks_sunday_ref() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 4, 26),
            );
        }

        #[test]
        fn zero_weeks_monday_ref_on_sunday() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Monday),
                    date(2026, 2, 8),
                )
                .unwrap(),
                date(2026, 2, 2),
            );
        }

        #[test]
        fn zero_weeks_sunday_ref_on_sunday() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(0, Weekday::Sunday),
                    date(2026, 2, 8),
                )
                .unwrap(),
                date(2026, 2, 8),
            );
        }

        #[test]
        fn positive_weeks() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(15, Weekday::Monday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 1, 12),
            );
        }

        #[test]
        fn negative_weeks() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Weeks(-10, Weekday::Monday),
                    date(2026, 5, 1),
                )
                .unwrap(),
                date(2026, 7, 6),
            );
        }

        #[test]
        fn zero_iso_weeks() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::IsoWeeks(0), date(2026, 4, 23),)
                    .unwrap(),
                date(2026, 4, 20),
            );
        }

        #[test]
        fn positive_iso_weeks() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::IsoWeeks(10), date(2026, 5, 1),)
                    .unwrap(),
                date(2026, 2, 16),
            );
        }

        #[test]
        fn negative_iso_weeks() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::IsoWeeks(-10), date(2026, 5, 1),)
                    .unwrap(),
                date(2026, 7, 6),
            );
        }

        #[test]
        fn zero_months() {
            // Per `checked_sub_calendar_anchor_offset_to_date`'s doc, subtracting months to get a day
            // returns the first day of the month.
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(0), date(2026, 5, 20),)
                    .unwrap(),
                date(2026, 5, 1),
            );
        }

        #[test]
        fn positive_months_no_extra_year() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(30), date(2026, 8, 20),)
                    .unwrap(),
                date(2024, 2, 1),
            );
        }

        #[test]
        fn positive_months_extra_year() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(30), date(2026, 5, 20),)
                    .unwrap(),
                date(2023, 11, 1),
            );
        }

        #[test]
        fn negative_months_no_extra_year() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(-30), date(2026, 10, 20),)
                    .unwrap(),
                date(2029, 4, 1),
            );
        }

        #[test]
        fn negative_months_extra_year() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Months(-30), date(2026, 5, 20),)
                    .unwrap(),
                date(2028, 11, 1),
            );
        }

        #[test]
        fn zero_years() {
            // Per `checked_sub_calendar_anchor_offset_to_date`'s doc, adding years to get a day
            // returns the first day of the year.
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(0), date(2026, 5, 20),).unwrap(),
                date(2026, 1, 1),
            );
        }

        #[test]
        fn positive_years() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(10), date(2026, 5, 20),)
                    .unwrap(),
                date(2016, 1, 1),
            );
        }

        #[test]
        fn negative_years() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(-10), date(2026, 5, 20),)
                    .unwrap(),
                date(2036, 1, 1),
            );
        }

        #[test]
        fn offset_too_large() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Years(i32::MAX), date(2026, 5, 1),),
                Err(CalendarAnchorOffsetDateError::OffsetTooLarge),
            );
        }

        #[test]
        fn out_of_range_result() {
            assert_eq!(
                checked_sub_calendar_anchor_offset_to_date(
                    CalendarAnchorOffset::Years(7000), // Will make year -10'000, not supported by jiff
                    Date::new(-3000, 5, 1).unwrap(),
                ),
                Err(CalendarAnchorOffsetDateError::OutOfRangeResult),
            );
        }
    }
}

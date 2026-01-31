use std::cmp::Ordering;

use chrono::{Month, NaiveDate, Weekday};

use super::time::*;

#[test]
fn naive_month_checked_first_day() {
    assert_eq!(
        NaiveMonth::new(2026, Month::April).checked_first_day().unwrap(),
        NaiveDate::from_ymd_opt(2026, 4, 1).unwrap(),
    );
}

#[test]
fn naive_month_checked_last_day() {
    assert_eq!(
        NaiveMonth::new(2026, Month::April).checked_last_day().unwrap(),
        NaiveDate::from_ymd_opt(2026, 4, 30).unwrap(),
    );
}

#[test]
fn naive_duration_days_is_zero() {
    assert!(!NaiveDuration::days(1).is_zero());
    assert!(NaiveDuration::days(0).is_zero());
    assert!(!NaiveDuration::days(-1).is_zero());
}

#[test]
fn naive_duration_weeks_is_zero() {
    assert!(!NaiveDuration::weeks(Weekday::Mon, 1).is_zero());
    assert!(NaiveDuration::weeks(Weekday::Mon, 0).is_zero());
    assert!(!NaiveDuration::weeks(Weekday::Mon, -1).is_zero());
}

#[test]
fn naive_duration_months_is_zero() {
    assert!(!NaiveDuration::months(1).is_zero());
    assert!(NaiveDuration::months(0).is_zero());
    assert!(!NaiveDuration::months(-1).is_zero());
}

#[test]
fn naive_duration_years_is_zero() {
    assert!(!NaiveDuration::years(1).is_zero());
    assert!(NaiveDuration::years(0).is_zero());
    assert!(!NaiveDuration::years(-1).is_zero());
}

#[test]
fn naive_duration_days_is_positive() {
    assert!(NaiveDuration::days(1).is_positive());
    assert!(!NaiveDuration::days(0).is_positive());
    assert!(!NaiveDuration::days(-1).is_positive());
}

#[test]
fn naive_duration_weeks_is_positive() {
    assert!(NaiveDuration::weeks(Weekday::Mon, 1).is_positive());
    assert!(!NaiveDuration::weeks(Weekday::Mon, 0).is_positive());
    assert!(!NaiveDuration::weeks(Weekday::Mon, -1).is_positive());
}

#[test]
fn naive_duration_months_is_positive() {
    assert!(NaiveDuration::months(1).is_positive());
    assert!(!NaiveDuration::months(0).is_positive());
    assert!(!NaiveDuration::months(-1).is_positive());
}

#[test]
fn naive_duration_years_is_positive() {
    assert!(NaiveDuration::years(1).is_positive());
    assert!(!NaiveDuration::years(0).is_positive());
    assert!(!NaiveDuration::years(-1).is_positive());
}

#[test]
fn naive_duration_days_is_negative() {
    assert!(!NaiveDuration::days(1).is_negative());
    assert!(!NaiveDuration::days(0).is_negative());
    assert!(NaiveDuration::days(-1).is_negative());
}

#[test]
fn naive_duration_weeks_is_negative() {
    assert!(!NaiveDuration::weeks(Weekday::Mon, 1).is_negative());
    assert!(!NaiveDuration::weeks(Weekday::Mon, 0).is_negative());
    assert!(NaiveDuration::weeks(Weekday::Mon, -1).is_negative());
}

#[test]
fn naive_duration_months_is_negative() {
    assert!(!NaiveDuration::months(1).is_negative());
    assert!(!NaiveDuration::months(0).is_negative());
    assert!(NaiveDuration::months(-1).is_negative());
}

#[test]
fn naive_duration_years_is_negative() {
    assert!(!NaiveDuration::years(1).is_negative());
    assert!(!NaiveDuration::years(0).is_negative());
    assert!(NaiveDuration::years(-1).is_negative());
}

#[test]
fn naive_duration_cant_compare_different_units() {
    assert_eq!(
        NaiveDuration::days(1).partial_cmp(&NaiveDuration::weeks(Weekday::Mon, 1)),
        None
    );
    assert_eq!(NaiveDuration::days(1).partial_cmp(&NaiveDuration::months(1)), None);
    assert_eq!(NaiveDuration::days(1).partial_cmp(&NaiveDuration::years(1)), None);
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 1).partial_cmp(&NaiveDuration::days(1)),
        None
    );
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 1).partial_cmp(&NaiveDuration::months(1)),
        None
    );
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 1).partial_cmp(&NaiveDuration::years(1)),
        None
    );
    assert_eq!(NaiveDuration::months(1).partial_cmp(&NaiveDuration::days(1)), None);
    assert_eq!(
        NaiveDuration::months(1).partial_cmp(&NaiveDuration::weeks(Weekday::Mon, 1)),
        None
    );
    assert_eq!(NaiveDuration::months(1).partial_cmp(&NaiveDuration::years(1)), None);
    assert_eq!(NaiveDuration::years(1).partial_cmp(&NaiveDuration::days(1)), None);
    assert_eq!(
        NaiveDuration::years(1).partial_cmp(&NaiveDuration::weeks(Weekday::Mon, 1)),
        None
    );
    assert_eq!(NaiveDuration::years(1).partial_cmp(&NaiveDuration::months(1)), None);
}

#[test]
fn naive_duration_compare_days() {
    assert_eq!(
        NaiveDuration::days(1).partial_cmp(&NaiveDuration::days(0)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        NaiveDuration::days(0).partial_cmp(&NaiveDuration::days(1)),
        Some(Ordering::Less)
    );
    assert_eq!(
        NaiveDuration::days(0).partial_cmp(&NaiveDuration::days(0)),
        Some(Ordering::Equal)
    );
}

#[test]
fn naive_duration_compare_weeks_same_ref_day() {
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 1).partial_cmp(&NaiveDuration::weeks(Weekday::Mon, 0)),
        Some(Ordering::Greater),
    );
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 0).partial_cmp(&NaiveDuration::weeks(Weekday::Mon, 1)),
        Some(Ordering::Less),
    );
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 0).partial_cmp(&NaiveDuration::weeks(Weekday::Mon, 0)),
        Some(Ordering::Equal),
    );
}

#[test]
fn naive_duration_compare_weeks_different_ref_day() {
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 1).partial_cmp(&NaiveDuration::weeks(Weekday::Sun, 0)),
        Some(Ordering::Greater),
    );
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 0).partial_cmp(&NaiveDuration::weeks(Weekday::Sun, 1)),
        Some(Ordering::Less),
    );
    assert_eq!(
        NaiveDuration::weeks(Weekday::Mon, 0).partial_cmp(&NaiveDuration::weeks(Weekday::Sun, 0)),
        Some(Ordering::Equal),
    );
}

#[test]
fn naive_duration_compare_months() {
    assert_eq!(
        NaiveDuration::months(1).partial_cmp(&NaiveDuration::months(0)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        NaiveDuration::months(0).partial_cmp(&NaiveDuration::months(1)),
        Some(Ordering::Less)
    );
    assert_eq!(
        NaiveDuration::months(0).partial_cmp(&NaiveDuration::months(0)),
        Some(Ordering::Equal)
    );
}

#[test]
fn naive_duration_compare_years() {
    assert_eq!(
        NaiveDuration::years(1).partial_cmp(&NaiveDuration::years(0)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        NaiveDuration::years(0).partial_cmp(&NaiveDuration::years(1)),
        Some(Ordering::Less)
    );
    assert_eq!(
        NaiveDuration::years(0).partial_cmp(&NaiveDuration::years(0)),
        Some(Ordering::Equal)
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_zero_days() {
    let naive_date = NaiveDate::from_ymd_opt(2026, 5, 1).unwrap();

    assert_eq!(
        checked_add_naive_duration_to_naive_date(naive_date, NaiveDuration::Days(0)).unwrap(),
        naive_date,
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_positive_days() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::days(420),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2027, 6, 25).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_negative_days() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::days(-420),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2025, 3, 7).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_zero_weeks_monday_ref() {
    // Per `checked_add_naive_duration_to_naive_date`'s doc, adding weeks to get a day
    // returns the first day of the week.
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 4, 27).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_zero_weeks_sunday_ref() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Sun, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 4, 26).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_zero_weeks_monday_ref_on_sunday() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 2, 8).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 2, 2).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_zero_weeks_sunday_ref_on_sunday() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 2, 8).unwrap(),
            NaiveDuration::weeks(Weekday::Sun, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 2, 8).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_positive_weeks() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, 15),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 8, 10).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_negative_weeks() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, -10),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 2, 16).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_zero_months() {
    // Per `checked_add_naive_duration_to_naive_date`'s doc, adding months to get a day
    // returns the first day of the month.
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::months(0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_positive_months_no_extra_year() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::months(30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2028, 11, 1).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_positive_months_extra_year() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 10, 20).unwrap(),
            NaiveDuration::months(30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2029, 4, 1).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_negative_months_no_extra_year() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 8, 20).unwrap(),
            NaiveDuration::months(-30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2024, 2, 1).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_negative_months_extra_year() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::months(-30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2023, 11, 1).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_zero_years() {
    // Per `checked_add_naive_duration_to_naive_date`'s doc, adding years to get a day
    // returns the first day of the year.
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::years(0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 1, 1).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_positive_years() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::years(10),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2036, 1, 1).unwrap(),
    );
}

#[test]
fn checked_add_naive_duration_to_naive_date_negative_years() {
    assert_eq!(
        checked_add_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::years(-10),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2016, 1, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_zero_days() {
    let naive_date = NaiveDate::from_ymd_opt(2026, 5, 1).unwrap();

    assert_eq!(
        checked_sub_naive_duration_to_naive_date(naive_date, NaiveDuration::Days(0)).unwrap(),
        naive_date,
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_positive_days() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::days(420),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2025, 3, 7).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_negative_days() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::days(-420),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2027, 6, 25).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_zero_weeks_monday_ref() {
    // Per `checked_sub_naive_duration_to_naive_date`'s doc, subtracting weeks to get a day
    // returns the first day of the week.
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 4, 27).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_zero_weeks_sunday_ref() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Sun, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 4, 26).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_zero_weeks_monday_ref_on_sunday() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 2, 8).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 2, 2).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_zero_weeks_sunday_ref_on_sunday() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 2, 8).unwrap(),
            NaiveDuration::weeks(Weekday::Sun, 0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 2, 8).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_positive_weeks() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, 15),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 1, 12).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_negative_weeks() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
            NaiveDuration::weeks(Weekday::Mon, -10),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 7, 6).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_zero_months() {
    // Per `checked_sub_naive_duration_to_naive_date`'s doc, subtracting months to get a day
    // returns the first day of the month.
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::months(0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_positive_months_no_extra_year() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 8, 20).unwrap(),
            NaiveDuration::months(30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2024, 2, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_positive_months_extra_year() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::months(30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2023, 11, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_negative_months_no_extra_year() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 10, 20).unwrap(),
            NaiveDuration::months(-30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2029, 4, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_negative_months_extra_year() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::months(-30),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2028, 11, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_zero_years() {
    // Per `checked_sub_naive_duration_to_naive_date`'s doc, adding years to get a day
    // returns the first day of the year.
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::years(0),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2026, 1, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_positive_years() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::years(10),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2016, 1, 1).unwrap(),
    );
}

#[test]
fn checked_sub_naive_duration_to_naive_date_negative_years() {
    assert_eq!(
        checked_sub_naive_duration_to_naive_date(
            NaiveDate::from_ymd_opt(2026, 5, 20).unwrap(),
            NaiveDuration::years(-10),
        )
        .unwrap(),
        NaiveDate::from_ymd_opt(2036, 1, 1).unwrap(),
    );
}

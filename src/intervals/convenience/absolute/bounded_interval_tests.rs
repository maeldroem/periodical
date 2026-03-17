

#[test]
fn bounded_absolute_interval_from_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let date = NaiveDate::from_ymd_opt(2026, 1, 5).unwrap();

    let interval = BoundedAbsoluteInterval::from_date(date, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 5, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_max_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let date = NaiveDate::MAX;

    assert_eq!(
        BoundedAbsoluteInterval::from_date(date, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)
    );
}

#[test]
fn bounded_absolute_interval_day_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = BoundedAbsoluteInterval::day_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 4, 29).unwrap(),
        CalendarAnchorOffset::Days(5),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 5, 3, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 4, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_day_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = BoundedAbsoluteInterval::day_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 4, 29).unwrap(),
        CalendarAnchorOffset::Days(5),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 4, 23, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 4, 24, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 5).unwrap();
    let to = NaiveDate::from_ymd_opt(2026, 1, 10).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_date_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 10, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range_max_from_and_to() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    assert_eq!(
        BoundedAbsoluteInterval::from_inclusive_date_range(NaiveDate::MAX, NaiveDate::MAX, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)
    );
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range_max_to() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 1).unwrap();

    assert_eq!(
        BoundedAbsoluteInterval::from_inclusive_date_range(from, NaiveDate::MAX, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)
    );
}

#[test]
fn bounded_absolute_interval_from_inclusive_date_range_reversed_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 10).unwrap();
    let to = NaiveDate::from_ymd_opt(2026, 1, 5).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_date_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 10, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().week(Weekday::Tue);

    let week_interval = BoundedAbsoluteInterval::from_week(week, offset_tz).unwrap();

    assert_eq!(week_interval.from_time(), datetime(&Utc, 2026, 4, 27, 22, 0, 0));
    assert_eq!(week_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week_interval.to_time(), datetime(&Utc, 2026, 5, 4, 22, 0, 0));
    assert_eq!(week_interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_week_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().week(Weekday::Mon);
    let to = NaiveDate::from_ymd_opt(2026, 3, 17).unwrap().week(Weekday::Sat);

    let interval = BoundedAbsoluteInterval::from_inclusive_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 3, 20, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_week_range_same_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().week(Weekday::Mon);

    let interval = BoundedAbsoluteInterval::from_inclusive_week_range(week, week, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 11, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_week_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 2, 20).unwrap().week(Weekday::Tue);
    let to = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().week(Weekday::Sat);

    let interval = BoundedAbsoluteInterval::from_inclusive_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 2, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 2, 23, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::week_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::Weeks(Weekday::Mon, 2),
        Weekday::Mon,
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 5, 10, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 5, 17, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::week_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::Weeks(Weekday::Mon, 2),
        Weekday::Mon,
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 4, 12, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 4, 19, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_iso_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let iso_week = NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().iso_week();

    let iso_week_interval = BoundedAbsoluteInterval::from_iso_week(iso_week, offset_tz).unwrap();

    assert_eq!(iso_week_interval.from_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(iso_week_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(iso_week_interval.to_time(), datetime(&Utc, 2026, 5, 3, 22, 0, 0));
    assert_eq!(iso_week_interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_iso_week_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().iso_week();
    let to = NaiveDate::from_ymd_opt(2026, 3, 17).unwrap().iso_week();

    let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 3, 22, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_iso_week_range_same_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().iso_week();

    let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(week, week, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 1, 11, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_iso_week_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from = NaiveDate::from_ymd_opt(2026, 3, 17).unwrap().iso_week();
    let to = NaiveDate::from_ymd_opt(2026, 1, 7).unwrap().iso_week();

    let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(from, to, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 1, 4, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 3, 22, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_from_iso_year_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let iso_week = BoundedAbsoluteInterval::week_from_iso_year_week(2026, 5, offset_tz).unwrap();

    assert_eq!(iso_week.from_time(), datetime(&Utc, 2026, 1, 25, 22, 0, 0));
    assert_eq!(iso_week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(iso_week.to_time(), datetime(&Utc, 2026, 2, 1, 22, 0, 0));
    assert_eq!(iso_week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_from_iso_year_week_invalid_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    assert_eq!(
        BoundedAbsoluteInterval::week_from_iso_year_week(2026, 60, offset_tz),
        Err(BoundedAbsoluteIntervalCreationError::DateOperationError),
    );
}

#[test]
fn bounded_absolute_interval_iso_week_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::iso_week_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::IsoWeeks(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 5, 10, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 5, 17, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_iso_week_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let week = BoundedAbsoluteInterval::iso_week_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(),
        CalendarAnchorOffset::IsoWeeks(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(week.from_time(), datetime(&Utc, 2026, 4, 12, 22, 0, 0));
    assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(week.to_time(), datetime(&Utc, 2026, 4, 19, 22, 0, 0));
    assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_week_from_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let month = BoundedAbsoluteInterval::from_month(MonthInYear::new(2026, Month::May), offset_tz).unwrap();

    assert_eq!(month.from_time(), datetime(&Utc, 2026, 4, 30, 22, 0, 0));
    assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(month.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_month_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_month_range(
        MonthInYear::new(2026, Month::January),
        MonthInYear::new(2026, Month::May),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_month_range_same_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let month = MonthInYear::new(2026, Month::May);

    let interval = BoundedAbsoluteInterval::from_inclusive_month_range(month, month, offset_tz).unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2026, 4, 30, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_month_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let interval = BoundedAbsoluteInterval::from_inclusive_month_range(
        MonthInYear::new(2026, Month::May),
        MonthInYear::new(2026, Month::January),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.from_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.to_time(), datetime(&Utc, 2026, 5, 31, 22, 0, 0));
    assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_month_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let month = BoundedAbsoluteInterval::month_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(month.from_time(), datetime(&Utc, 2026, 6, 30, 22, 0, 0));
    assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(month.to_time(), datetime(&Utc, 2026, 7, 31, 22, 0, 0));
    assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_month_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let month = BoundedAbsoluteInterval::month_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(2),
        offset_tz,
    )
    .unwrap();

    assert_eq!(month.from_time(), datetime(&Utc, 2026, 2, 28, 22, 0, 0));
    assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(month.to_time(), datetime(&Utc, 2026, 3, 31, 22, 0, 0));
    assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_year_common() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let year = BoundedAbsoluteInterval::from_year(2026, offset_tz).unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2026, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_year_leap() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let year = BoundedAbsoluteInterval::from_year(2028, offset_tz).unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2027, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2028, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_year_range() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let years = BoundedAbsoluteInterval::from_inclusive_year_range(2025, 2030, offset_tz).unwrap();

    assert_eq!(years.from_time(), datetime(&Utc, 2024, 12, 31, 22, 0, 0));
    assert_eq!(years.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(years.to_time(), datetime(&Utc, 2030, 12, 31, 22, 0, 0));
    assert_eq!(years.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_year_range_same_year() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let year = BoundedAbsoluteInterval::from_inclusive_year_range(2030, 2030, offset_tz).unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2029, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2030, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_from_inclusive_year_range_reverse_order() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let years = BoundedAbsoluteInterval::from_inclusive_year_range(2030, 2025, offset_tz).unwrap();

    assert_eq!(years.from_time(), datetime(&Utc, 2024, 12, 31, 22, 0, 0));
    assert_eq!(years.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(years.to_time(), datetime(&Utc, 2030, 12, 31, 22, 0, 0));
    assert_eq!(years.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_year_after_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let year = BoundedAbsoluteInterval::year_after_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(15),
        offset_tz,
    )
    .unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2026, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2027, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

#[test]
fn bounded_absolute_interval_year_before_naive_duration_from_naive_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();

    let year = BoundedAbsoluteInterval::year_before_naive_duration_from_naive_date(
        NaiveDate::from_ymd_opt(2026, 5, 5).unwrap(),
        CalendarAnchorOffset::Months(15),
        offset_tz,
    )
    .unwrap();

    assert_eq!(year.from_time(), datetime(&Utc, 2024, 12, 31, 22, 0, 0));
    assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(year.to_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
}

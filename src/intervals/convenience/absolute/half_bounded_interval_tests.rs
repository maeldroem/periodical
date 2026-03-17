
#[test]
fn half_bounded_absolute_interval_since_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let from_first_of_may =
        HalfBoundedAbsoluteInterval::since_date(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(), offset_tz).unwrap();

    assert_eq!(
        from_first_of_may.reference_time(),
        datetime(&Utc, 2026, 4, 30, 22, 0, 0)
    );
    assert_eq!(from_first_of_may.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(from_first_of_may.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_date() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let until_first_of_may =
        HalfBoundedAbsoluteInterval::until_date(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap(), offset_tz).unwrap();

    assert_eq!(
        until_first_of_may.reference_time(),
        datetime(&Utc, 2026, 4, 30, 22, 0, 0)
    );
    assert_eq!(until_first_of_may.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_first_of_may.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = HalfBoundedAbsoluteInterval::since_week(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().week(Weekday::Mon),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval = HalfBoundedAbsoluteInterval::until_week(
        NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().week(Weekday::Mon),
        offset_tz,
    )
    .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_iso_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval =
        HalfBoundedAbsoluteInterval::since_iso_week(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().iso_week(), offset_tz)
            .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_iso_week() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let interval =
        HalfBoundedAbsoluteInterval::until_iso_week(NaiveDate::from_ymd_opt(2026, 5, 1).unwrap().iso_week(), offset_tz)
            .unwrap();

    assert_eq!(interval.reference_time(), datetime(&Utc, 2026, 4, 26, 22, 0, 0));
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let since_month = HalfBoundedAbsoluteInterval::since_month(MonthInYear::new(2026, Month::March), offset_tz).unwrap();

    assert_eq!(since_month.reference_time(), datetime(&Utc, 2026, 2, 28, 22, 0, 0));
    assert_eq!(since_month.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(since_month.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_month() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let until_month = HalfBoundedAbsoluteInterval::until_month(MonthInYear::new(2026, Month::March), offset_tz).unwrap();

    assert_eq!(until_month.reference_time(), datetime(&Utc, 2026, 2, 28, 22, 0, 0));
    assert_eq!(until_month.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_month.opening_direction(), OpeningDirection::ToPast);
}

#[test]
fn half_bounded_absolute_interval_since_year() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let since_year = HalfBoundedAbsoluteInterval::since_year(2026, offset_tz).unwrap();

    assert_eq!(since_year.reference_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(since_year.reference_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(since_year.opening_direction(), OpeningDirection::ToFuture);
}

#[test]
fn half_bounded_absolute_interval_until_year() {
    let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into().unwrap()).unwrap();
    let until_year = HalfBoundedAbsoluteInterval::until_year(2026, offset_tz).unwrap();

    assert_eq!(until_year.reference_time(), datetime(&Utc, 2025, 12, 31, 22, 0, 0));
    assert_eq!(until_year.reference_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(until_year.opening_direction(), OpeningDirection::ToPast);
}

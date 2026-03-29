//! Convenience methods for [`BoundedAbsoluteInterval`]

use jiff::Span;
use jiff::civil::Date;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
use crate::intervals::meta::BoundInclusivity;
use crate::time::{
    CalendarAnchorOffset,
    CalendarAnchorOffsetDateError,
    MonthInYear,
    OffsetIsoWeek,
    checked_add_calendar_anchor_offset_to_date,
    checked_sub_calendar_anchor_offset_to_date,
    date_today,
};

impl BoundedAbsoluteInterval {
    /// Creates a new [`BoundedAbsoluteInterval`] of the date in the given
    /// timezone
    ///
    /// If you wish to create a [`BoundedAbsoluteInterval`] of a date to which
    /// an offset is applied, consider using
    /// [`checked_add_calendar_anchor_offset_to_date`] or
    /// [`checked_sub_calendar_anchor_offset_to_date`] before using this
    /// method to get the interval.
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError) if
    /// the conversion method [`Date::to_zoned`] failed.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsoluteIntervalCreationError::OutOfRangeEnd) if the day after
    /// the given date is out of range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let date = "2026-01-05".parse::<Date>()?;
    /// let interval = BoundedAbsoluteInterval::from_date(date, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-01-05 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-01-06 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_date(date: Date, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        // Date::to_zoned already selects the earliest point in time for that particular
        // date, already handling cases where midnight doesn't exist because of
        // a time gap.
        let start = date
            .to_zoned(tz.clone())
            .or(Err(BoundedAbsoluteIntervalCreationError::ComputationError))?
            .timestamp();

        let end = date
            .checked_add(Span::new().days(1))
            .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEnd))?
            .to_zoned(tz)
            .or(Err(BoundedAbsoluteIntervalCreationError::ComputationError))?
            .timestamp();

        Ok(Self::unchecked_new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        ))
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day after a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_date`](BoundedAbsoluteInterval::from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsoluteInterval::day_after_duration_from_date(
    ///     "2026-05-01".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-05-06 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-05-07 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn day_after_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let date =
            checked_add_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsoluteIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    BoundedAbsoluteIntervalCreationError::OutOfRangeStart
                },
            })?;

        Self::from_date(date, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day before a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_date`](BoundedAbsoluteInterval::from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsoluteInterval::day_before_duration_from_date(
    ///     "2026-05-01".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-04-26 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-04-27 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn day_before_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let date =
            checked_sub_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsoluteIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    BoundedAbsoluteIntervalCreationError::OutOfRangeStart
                },
            })?;

        Self::from_date(date, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day after a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`day_after_duration_from_date`](BoundedAbsoluteInterval::day_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsoluteInterval::day_after_duration_from_today(
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn day_after_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_after_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day before a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`day_before_duration_from_date`](BoundedAbsoluteInterval::day_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsoluteInterval::day_before_duration_from_today(
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn day_before_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_before_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Returns the current day in the given [`TimeZone`] as a
    /// [`BoundedAbsoluteInterval`]
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`] returns an error.
    ///
    /// Returns any error that [`from_date`](BoundedAbsoluteInterval::from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let today = BoundedAbsoluteInterval::today(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn today(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_date(date_today(tz.clone()), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of tomorrow in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// See [`day_after_duration_from_today`](BoundedAbsoluteInterval::day_after_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let tomorrow = BoundedAbsoluteInterval::tomorrow(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn tomorrow(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_after_duration_from_today(CalendarAnchorOffset::Days(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of yesterday in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// See [`day_before_duration_from_today`](BoundedAbsoluteInterval::day_before_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let yesterday = BoundedAbsoluteInterval::yesterday(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn yesterday(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_before_duration_from_today(CalendarAnchorOffset::Days(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the inclusive date range
    /// in the given timezone
    ///
    /// If the given dates are not in chronological order, they are swapped.
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`Date::to_zoned`] returned an error.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsoluteIntervalCreationError::OutOfRangeEnd) if the day after
    /// the given end date is out of range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let interval = BoundedAbsoluteInterval::from_inclusive_date_range(
    ///     "2026-01-04".parse::<Date>()?,
    ///     "2026-01-10".parse::<Date>()?,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-01-04 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-01-11 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_inclusive_date_range(
        mut start_date: Date,
        mut end_date: Date,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if start_date > end_date {
            std::mem::swap(&mut start_date, &mut end_date);
        }

        let start = start_date
            .to_zoned(tz.clone())
            .or(Err(BoundedAbsoluteIntervalCreationError::ComputationError))?
            .timestamp();

        let end = end_date
            .checked_add(Span::new().days(1))
            .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEnd))?
            .to_zoned(tz)
            .or(Err(BoundedAbsoluteIntervalCreationError::ComputationError))?
            .timestamp();

        Ok(Self::unchecked_new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        ))
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the [`OffsetIsoWeek`] in
    /// the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart) if
    /// the week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsoluteIntervalCreationError::OutOfRangeEnd) if
    /// the week's last day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::OffsetIsoWeek;
    /// let week_interval = BoundedAbsoluteInterval::from_week(
    ///     OffsetIsoWeek::new(5, 2026)?,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     week_interval.start(),
    ///     "2026-01-26 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(
    ///     week_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     week_interval.end(),
    ///     "2026-02-02 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(week_interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_week(week: OffsetIsoWeek, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_inclusive_date_range(
            week.first_day()
                .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeStart))?,
            week.last_day()
                .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEnd))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided inclusive
    /// [`OffsetIsoWeek`] range in the given timezone
    ///
    /// If the given start week's first day is before the given end week's last
    /// day, the given end week's last day will be used as the start and the
    /// given start week's first day will be used as the end[^1].
    ///
    /// Note that the given start/end weeks can have different start days, so
    /// the resulting interval may not always be a multiple of 7 days.
    ///
    /// [^1]: Swapping the weeks instead of the days would result in confusing intervals by creating larger intervals
    /// than expected.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart) if
    /// the start week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsoluteIntervalCreationError::OutOfRangeEnd) if
    /// the end week's last day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::OffsetIsoWeek;
    /// let start = OffsetIsoWeek::new_with_offset(10, 2026, -1)?; // Sunday week
    /// let end = OffsetIsoWeek::new_with_offset(14, 2026, 2)?; // Wednesday week
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_week_range(
    ///     start,
    ///     end,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-03-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-04-08 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_inclusive_week_range(
        start: OffsetIsoWeek,
        end: OffsetIsoWeek,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let mut start_day = start
            .first_day()
            .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeStart))?;
        let mut end_day = end
            .last_day()
            .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEnd))?;

        if start_day > end_day {
            std::mem::swap(&mut start_day, &mut end_day);
        }

        Self::from_inclusive_date_range(start_day, end_day, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the given month in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart) if
    /// the first day of the month is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsoluteIntervalCreationError::OutOfRangeEnd) if
    /// the last day of the month is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::Month;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let month = BoundedAbsoluteInterval::from_month(
    ///     Month::May.with_year(2026),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     month.start(),
    ///     "2026-05-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     month.end(),
    ///     "2026-06-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_month(month: MonthInYear, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_inclusive_date_range(
            month
                .first_day()
                .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeStart))?,
            month
                .last_day()
                .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEnd))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the inclusive month range
    /// in the given timezone
    ///
    /// If the given months are not in chronological order, they are swapped.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart) if
    /// the start month's first day is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsoluteIntervalCreationError::OutOfRangeEnd) if
    /// the end month's last day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::{Month, MonthInYear};
    /// let interval = BoundedAbsoluteInterval::from_inclusive_month_range(
    ///     Month::January.with_year(2026),
    ///     Month::May.with_year(2026),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-06-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_inclusive_month_range(
        mut start: MonthInYear,
        mut end: MonthInYear,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if start > end {
            std::mem::swap(&mut start, &mut end);
        }

        Self::from_inclusive_date_range(
            start
                .first_day()
                .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeStart))?,
            end.last_day()
                .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEnd))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month after a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError) if
    /// conversion of [`Date`] to a [`MonthInYear`] failed.
    ///
    /// Returns any error that
    /// [`from_month`](BoundedAbsoluteInterval::from_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsoluteInterval::month_after_duration_from_date(
    ///     "2026-02-27".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-03-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-04-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn month_after_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let date =
            checked_add_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsoluteIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    BoundedAbsoluteIntervalCreationError::OutOfRangeStart
                },
            })?;

        let month = MonthInYear::try_from(date).or(Err(BoundedAbsoluteIntervalCreationError::ComputationError))?;

        Self::from_month(month, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month before a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError) if
    /// conversion of [`Date`] to a [`MonthInYear`] failed.
    ///
    /// Returns any error that
    /// [`from_month`](BoundedAbsoluteInterval::from_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsoluteInterval::month_before_duration_from_date(
    ///     "2026-03-02".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start(),
    ///     "2026-02-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end(),
    ///     "2026-03-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn month_before_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let date =
            checked_sub_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsoluteIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    BoundedAbsoluteIntervalCreationError::OutOfRangeStart
                },
            })?;

        let month = MonthInYear::try_from(date).or(Err(BoundedAbsoluteIntervalCreationError::ComputationError))?;

        Self::from_month(month, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month after a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_after_duration_from_date`](BoundedAbsoluteInterval::month_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let month = BoundedAbsoluteInterval::month_after_duration_from_today(
    ///     CalendarAnchorOffset::Months(2),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn month_after_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_after_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month before a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_before_duration_from_date`](BoundedAbsoluteInterval::month_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let month = BoundedAbsoluteInterval::month_before_duration_from_today(
    ///     CalendarAnchorOffset::Months(2),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn month_before_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_before_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the current month in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError) if
    /// conversion of today's [`Date`] to a [`MonthInYear`] failed.
    ///
    /// Return any error that
    /// [`from_month`](BoundedAbsoluteInterval::from_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let month = BoundedAbsoluteInterval::this_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn this_month(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let month = MonthInYear::try_from(date_today(tz.clone()))
            .or(Err(BoundedAbsoluteIntervalCreationError::ComputationError))?;

        Self::from_month(month, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the next month in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_after_duration_from_today`](BoundedAbsoluteInterval::month_after_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let month = BoundedAbsoluteInterval::next_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn next_month(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_after_duration_from_today(CalendarAnchorOffset::Months(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the previous month in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_before_duration_from_today`](BoundedAbsoluteInterval::month_before_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let month = BoundedAbsoluteInterval::previous_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn previous_month(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_before_duration_from_today(CalendarAnchorOffset::Months(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the given year in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart) if
    /// the year's first day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let year = BoundedAbsoluteInterval::from_year(2026, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     year.start(),
    ///     "2026-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     year.end(),
    ///     "2027-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_year(year: i16, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let first_day_of_year = Date::new(year, 1, 1).or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeStart))?;
        let last_day_of_year = first_day_of_year.last_of_year();

        Self::from_inclusive_date_range(first_day_of_year, last_day_of_year, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided inclusive
    /// year range in the given timezone
    ///
    /// If the given years are not in chronological order, they are swapped.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart) if
    /// the first day of the start year is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsoluteIntervalCreationError::OutOfRangeEnd) if
    /// the last day of the end year is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let years = BoundedAbsoluteInterval::from_inclusive_year_range(
    ///     2025,
    ///     2030,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     years.start(),
    ///     "2025-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(years.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     years.end(),
    ///     "2031-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(years.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_inclusive_year_range(
        mut start_year: i16,
        mut end_year: i16,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if start_year > end_year {
            std::mem::swap(&mut start_year, &mut end_year);
        }

        let first_day_of_start_year =
            Date::new(start_year, 1, 1).or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeStart))?;

        let last_day_of_end_year = Date::new(end_year, 1, 1)
            .or(Err(BoundedAbsoluteIntervalCreationError::OutOfRangeEnd))?
            .last_of_year();

        Self::from_inclusive_date_range(first_day_of_start_year, last_day_of_end_year, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year after a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_year`](BoundedAbsoluteInterval::from_year)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsoluteInterval::year_after_duration_from_date(
    ///     "2026-05-05".parse::<Date>()?,
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     year.start(),
    ///     "2027-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     year.end(),
    ///     "2028-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn year_after_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let year = checked_add_calendar_anchor_offset_to_date(calendar_anchor_offset, date)
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsoluteIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    BoundedAbsoluteIntervalCreationError::OutOfRangeStart
                },
            })?
            .year();

        Self::from_year(year, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year before a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsoluteIntervalCreationError::OutOfRangeStart)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_year`](BoundedAbsoluteInterval::from_year)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsoluteInterval::year_before_duration_from_date(
    ///     "2026-05-05".parse::<Date>()?,
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     year.start(),
    ///     "2025-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     year.end(),
    ///     "2026-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn year_before_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let year = checked_sub_calendar_anchor_offset_to_date(calendar_anchor_offset, date)
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsoluteIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    BoundedAbsoluteIntervalCreationError::OutOfRangeStart
                },
            })?
            .year();

        Self::from_year(year, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year after a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_after_duration_from_date`](BoundedAbsoluteInterval::year_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsoluteInterval::year_after_duration_from_today(
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn year_after_duration_from_today(
        duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_after_duration_from_date(date_today(tz.clone()), duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year before a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_before_duration_from_date`](BoundedAbsoluteInterval::year_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsoluteInterval::year_before_duration_from_today(
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn year_before_duration_from_today(
        duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_before_duration_from_date(date_today(tz.clone()), duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the current year in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that [`from_year`](BoundedAbsoluteInterval::from_year)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let year = BoundedAbsoluteInterval::this_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn this_year(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_year(date_today(tz.clone()).year(), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the next year in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_after_duration_from_today`](BoundedAbsoluteInterval::year_after_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let year = BoundedAbsoluteInterval::next_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn next_year(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_after_duration_from_today(CalendarAnchorOffset::Years(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the previous year in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_before_duration_from_today`](BoundedAbsoluteInterval::year_before_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let year = BoundedAbsoluteInterval::next_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn previous_year(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_before_duration_from_today(CalendarAnchorOffset::Years(1), tz)
    }
}

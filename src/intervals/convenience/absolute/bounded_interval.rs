//! Convenience methods for [`BoundedAbsInterval`]

use jiff::Span;
use jiff::civil::Date;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{BoundedAbsInterval, BoundedAbsIntervalCreationError};
use crate::intervals::meta::BoundInclusivity;
use crate::time::{
    CalendarAnchorOffset,
    CalendarAnchorOffsetDateError,
    MonthInYear,
    OffsetIsoWeek,
    OffsetIsoWeekCreationError,
    checked_add_calendar_anchor_offset_to_date,
    checked_sub_calendar_anchor_offset_to_date,
    date_today,
};

impl BoundedAbsInterval {
    /// Creates a new [`BoundedAbsInterval`] of the date in the given
    /// timezone
    ///
    /// If you wish to create a [`BoundedAbsInterval`] of a date to which
    /// an offset is applied, consider using [`checked_add_calendar_anchor_offset_to_date`] or
    /// [`checked_sub_calendar_anchor_offset_to_date`] before using this
    /// method to get the interval.
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError) if
    /// the conversion method [`Date::to_zoned`] failed.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if the day after
    /// the given date is out of range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let date = "2026-01-05".parse::<Date>()?;
    /// let interval = BoundedAbsInterval::from_date(date, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-01-05 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
    ///     "2026-01-06 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_date(date: Date, tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        // Date::to_zoned already selects the earliest point in time for that particular
        // date, already handling cases where midnight doesn't exist because of
        // a time gap.
        let start = date
            .to_zoned(tz.clone())
            .or(Err(BoundedAbsIntervalCreationError::ComputationError))?
            .timestamp();

        let end = date
            .checked_add(Span::new().days(1))
            .or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?
            .to_zoned(tz)
            .or(Err(BoundedAbsIntervalCreationError::ComputationError))?
            .timestamp();

        Ok(Self::unchecked_from_times_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        ))
    }

    /// Creates a new [`BoundedAbsInterval`] of the day after a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_date`](BoundedAbsInterval::from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsInterval::day_after_duration_from_date(
    ///     "2026-05-01".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-05-06 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let date =
            checked_add_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?;

        Self::from_date(date, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the day before a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_date`](BoundedAbsInterval::from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsInterval::day_before_duration_from_date(
    ///     "2026-05-01".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-04-26 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let date =
            checked_sub_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?;

        Self::from_date(date, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the day after a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`day_after_duration_from_date`](BoundedAbsInterval::day_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsInterval::day_after_duration_from_today(
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn day_after_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::day_after_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the day before a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`day_before_duration_from_date`](BoundedAbsInterval::day_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsInterval::day_before_duration_from_today(
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn day_before_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::day_before_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Returns the current day in the given [`TimeZone`] as a
    /// [`BoundedAbsInterval`]
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`] returns an error.
    ///
    /// Returns any error that [`from_date`](BoundedAbsInterval::from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let today = BoundedAbsInterval::today(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn today(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::from_date(date_today(tz.clone()), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of tomorrow in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// See [`day_after_duration_from_today`](BoundedAbsInterval::day_after_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let tomorrow = BoundedAbsInterval::tomorrow(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn tomorrow(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::day_after_duration_from_today(CalendarAnchorOffset::Days(1), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of yesterday in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// See [`day_before_duration_from_today`](BoundedAbsInterval::day_before_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let yesterday = BoundedAbsInterval::yesterday(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn yesterday(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::day_before_duration_from_today(CalendarAnchorOffset::Days(1), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] from the inclusive date range
    /// in the given timezone
    ///
    /// If the given dates are not in chronological order, they are swapped.
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`Date::to_zoned`] returned an error.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if the day after
    /// the given end date is out of range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let interval = BoundedAbsInterval::from_inclusive_date_range(
    ///     "2026-01-04".parse::<Date>()?,
    ///     "2026-01-10".parse::<Date>()?,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-01-04 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        if start_date > end_date {
            std::mem::swap(&mut start_date, &mut end_date);
        }

        let start = start_date
            .to_zoned(tz.clone())
            .or(Err(BoundedAbsIntervalCreationError::ComputationError))?
            .timestamp();

        let end = end_date
            .checked_add(Span::new().days(1))
            .or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?
            .to_zoned(tz)
            .or(Err(BoundedAbsIntervalCreationError::ComputationError))?
            .timestamp();

        Ok(Self::unchecked_from_times_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        ))
    }

    /// Creates a new [`BoundedAbsInterval`] from the [`OffsetIsoWeek`] in
    /// the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if
    /// the week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if
    /// the week's last day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::OffsetIsoWeek;
    /// let week_interval =
    ///     BoundedAbsInterval::from_week(OffsetIsoWeek::new(2026, 5)?, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     week_interval.start_time(),
    ///     "2026-01-26 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(
    ///     week_interval.start_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// assert_eq!(
    ///     week_interval.end_time(),
    ///     "2026-02-02 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(week_interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_week(week: OffsetIsoWeek, tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::from_inclusive_date_range(
            week.first_day()
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?,
            week.last_day()
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsInterval`] of the offset ISO week after a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// The given week start offset must be greater than `-7` and less than `7`.
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`OffsetIsoWeek::from_date_with_offset`]
    /// returns [`Computation`](OffsetIsoWeekCreationError::Computation)
    /// or [`OutOfRangeOffset`](OffsetIsoWeekCreationError::OutOfRangeOffset).
    ///
    /// Returns any error that [`from_week`](BoundedAbsInterval::from_week) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::{Date, Weekday};
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let interval = BoundedAbsInterval::offset_week_after_duration_from_date(
    ///     "2026-01-18".parse::<Date>()?,
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     -2,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-01-24 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
    ///     "2026-01-31 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn offset_week_after_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        week_start_offset: i8,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let date =
            checked_add_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?;

        let week = OffsetIsoWeek::from_date_with_offset(date, week_start_offset).map_err(|err| match err {
            OffsetIsoWeekCreationError::Computation | OffsetIsoWeekCreationError::OutOfRangeOffset => {
                BoundedAbsIntervalCreationError::ComputationError
            },
            OffsetIsoWeekCreationError::OutOfRangeWeek | OffsetIsoWeekCreationError::OutOfRangeYear => {
                BoundedAbsIntervalCreationError::OutOfRangeStart
            },
        })?;

        Self::from_week(week, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the ISO week after a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`offset_week_after_duration_from_date`](BoundedAbsInterval::offset_week_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::{Date, Weekday};
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let interval = BoundedAbsInterval::week_after_duration_from_date(
    ///     "2026-01-18".parse::<Date>()?,
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-01-26 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
    ///     "2026-02-02 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn week_after_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::offset_week_after_duration_from_date(date, calendar_anchor_offset, OffsetIsoWeek::ISO_OFFSET, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the offset ISO week before a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// The given week start offset must be greater than `-7` and less than `7`.
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`OffsetIsoWeek::from_date_with_offset`]
    /// returns [`Computation`](OffsetIsoWeekCreationError::Computation)
    /// or [`OutOfRangeOffset`](OffsetIsoWeekCreationError::OutOfRangeOffset).
    ///
    /// Returns any error that [`from_week`](BoundedAbsInterval::from_week) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::{Date, Weekday};
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let interval = BoundedAbsInterval::offset_week_before_duration_from_date(
    ///     "2026-01-25".parse::<Date>()?,
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     -2,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-01-03 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
    ///     "2026-01-10 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn offset_week_before_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        week_start_offset: i8,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let date =
            checked_sub_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?;

        let week = OffsetIsoWeek::from_date_with_offset(date, week_start_offset).map_err(|err| match err {
            OffsetIsoWeekCreationError::Computation | OffsetIsoWeekCreationError::OutOfRangeOffset => {
                BoundedAbsIntervalCreationError::ComputationError
            },
            OffsetIsoWeekCreationError::OutOfRangeWeek | OffsetIsoWeekCreationError::OutOfRangeYear => {
                BoundedAbsIntervalCreationError::OutOfRangeStart
            },
        })?;

        Self::from_week(week, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the ISO week before a given
    /// [`CalendarAnchorOffset`] relative to the given date
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`offset_week_before_duration_from_date`](BoundedAbsInterval::offset_week_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::{Date, Weekday};
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let interval = BoundedAbsInterval::week_before_duration_from_date(
    ///     "2026-01-25".parse::<Date>()?,
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-01-05 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
    ///     "2026-01-12 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp()
    /// );
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn week_before_duration_from_date(
        date: Date,
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::offset_week_before_duration_from_date(date, calendar_anchor_offset, OffsetIsoWeek::ISO_OFFSET, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the offset ISO week after a given
    /// [`CalendarAnchorOffset`] relative to today
    ///
    /// # Errors
    ///
    /// Returns any error that [`offset_week_after_duration_from_date`](Self::offset_week_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::civil::Weekday;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::offset_week_after_duration_from_today(
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     -2,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn offset_week_after_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        week_start_offset: i8,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::offset_week_after_duration_from_date(
            date_today(tz.clone()),
            calendar_anchor_offset,
            week_start_offset,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsInterval`] of the ISO week after a given
    /// [`CalendarAnchorOffset`] relative to today
    ///
    /// # Errors
    ///
    /// Returns any error that [`week_after_duration_from_date`](Self::week_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::civil::Weekday;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::week_after_duration_from_today(
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn week_after_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::week_after_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the offset ISO week before a given
    /// [`CalendarAnchorOffset`] relative to today
    ///
    /// # Errors
    ///
    /// Returns any error that [`offset_week_before_duration_from_date`](Self::offset_week_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::civil::Weekday;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::offset_week_before_duration_from_today(
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     -2,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn offset_week_before_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        week_start_offset: i8,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::offset_week_before_duration_from_date(
            date_today(tz.clone()),
            calendar_anchor_offset,
            week_start_offset,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsInterval`] of the ISO week after a given
    /// [`CalendarAnchorOffset`] relative to today
    ///
    /// # Errors
    ///
    /// Returns any error that [`week_before_duration_from_date`](Self::week_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::civil::Weekday;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::CalendarAnchorOffset;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::week_before_duration_from_today(
    ///     CalendarAnchorOffset::Weeks(2, Weekday::Tuesday),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn week_before_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::week_before_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of this offset ISO week
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`OffsetIsoWeek::from_date_with_offset`]
    /// returns [`Computation`](OffsetIsoWeekCreationError::Computation)
    /// or [`OutOfRangeOffset`](OffsetIsoWeekCreationError::OutOfRangeOffset).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`OffsetIsoWeek::from_date_with_offset`]
    /// returns [`OutOfRangeWeek`](OffsetIsoWeekCreationError::OutOfRangeWeek)
    /// or [`OutOfRangeYear`](OffsetIsoWeekCreationError::OutOfRangeYear).
    ///
    /// Returns any error that [`OffsetIsoWeek::from_date_with_offset`] may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::this_offset_week(-2, TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn this_offset_week(week_start_offset: i8, tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        let week =
            OffsetIsoWeek::from_date_with_offset(date_today(tz.clone()), week_start_offset).map_err(
                |err| match err {
                    OffsetIsoWeekCreationError::Computation | OffsetIsoWeekCreationError::OutOfRangeOffset => {
                        BoundedAbsIntervalCreationError::ComputationError
                    },
                    OffsetIsoWeekCreationError::OutOfRangeWeek | OffsetIsoWeekCreationError::OutOfRangeYear => {
                        BoundedAbsIntervalCreationError::OutOfRangeStart
                    },
                },
            )?;

        Self::from_week(week, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of this ISO week
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`OffsetIsoWeek::from_date_with_offset`]
    /// returns [`Computation`](OffsetIsoWeekCreationError::Computation).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`OffsetIsoWeek::from_date_with_offset`]
    /// returns [`OutOfRangeWeek`](OffsetIsoWeekCreationError::OutOfRangeWeek)
    /// or [`OutOfRangeYear`](OffsetIsoWeekCreationError::OutOfRangeYear).
    ///
    /// Returns any error that [`OffsetIsoWeek::from_date_with_offset`] may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::this_week(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn this_week(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        let week = OffsetIsoWeek::from_date(date_today(tz.clone())).map_err(|err| match err {
            OffsetIsoWeekCreationError::Computation | OffsetIsoWeekCreationError::OutOfRangeOffset => {
                BoundedAbsIntervalCreationError::ComputationError
            },
            OffsetIsoWeekCreationError::OutOfRangeWeek | OffsetIsoWeekCreationError::OutOfRangeYear => {
                BoundedAbsIntervalCreationError::OutOfRangeStart
            },
        })?;

        Self::from_week(week, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the next offset ISO week
    ///
    /// # Errors
    ///
    /// Returns any error that [`offset_week_after_duration_from_today`](Self::offset_week_after_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::next_offset_week(-2, TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn next_offset_week(week_start_offset: i8, tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::offset_week_after_duration_from_today(CalendarAnchorOffset::IsoWeeks(1), week_start_offset, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the next offset ISO week
    ///
    /// # Errors
    ///
    /// Returns any error that [`week_after_duration_from_today`](Self::week_after_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::next_week(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn next_week(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::week_after_duration_from_today(CalendarAnchorOffset::IsoWeeks(1), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the previous offset ISO week
    ///
    /// # Errors
    ///
    /// Returns any error that [`offset_week_before_duration_from_today`](Self::offset_week_before_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::previous_offset_week(-2, TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn previous_offset_week(week_start_offset: i8, tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::offset_week_before_duration_from_today(CalendarAnchorOffset::IsoWeeks(1), week_start_offset, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the previous ISO week
    ///
    /// # Errors
    ///
    /// Returns any error that [`week_before_duration_from_today`](Self::week_before_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let interval = BoundedAbsInterval::previous_week(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn previous_week(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::week_before_duration_from_today(CalendarAnchorOffset::IsoWeeks(1), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] from the provided inclusive
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
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if
    /// the start week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if
    /// the end week's last day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::OffsetIsoWeek;
    /// let start = OffsetIsoWeek::new_with_offset(2026, 10, -1)?; // Sunday week
    /// let end = OffsetIsoWeek::new_with_offset(2026, 14, 2)?; // Wednesday week
    ///
    /// let interval =
    ///     BoundedAbsInterval::from_inclusive_week_range(start, end, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-03-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let mut start_day = start
            .first_day()
            .or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?;
        let mut end_day = end.last_day().or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?;

        if start_day > end_day {
            std::mem::swap(&mut start_day, &mut end_day);
        }

        Self::from_inclusive_date_range(start_day, end_day, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the given month in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if
    /// the first day of the month is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if
    /// the last day of the month is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::time::Month;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let month =
    ///     BoundedAbsInterval::from_month(Month::May.with_year(2026), TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     month.start_time(),
    ///     "2026-05-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     month.end_time(),
    ///     "2026-06-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_month(month: MonthInYear, tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::from_inclusive_date_range(
            month
                .first_day()
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?,
            month
                .last_day()
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsInterval`] from the inclusive month range
    /// in the given timezone
    ///
    /// If the given months are not in chronological order, they are swapped.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if
    /// the start month's first day is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if
    /// the end month's last day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::{Month, MonthInYear};
    /// let interval = BoundedAbsInterval::from_inclusive_month_range(
    ///     Month::January.with_year(2026),
    ///     Month::May.with_year(2026),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        if start > end {
            std::mem::swap(&mut start, &mut end);
        }

        Self::from_inclusive_date_range(
            start
                .first_day()
                .or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?,
            end.last_day().or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsInterval`] of the month after a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError) if
    /// conversion of [`Date`] to a [`MonthInYear`] failed.
    ///
    /// Returns any error that
    /// [`from_month`](BoundedAbsInterval::from_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsInterval::month_after_duration_from_date(
    ///     "2026-02-27".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-03-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let date =
            checked_add_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?;

        let month = MonthInYear::try_from(date).or(Err(BoundedAbsIntervalCreationError::ComputationError))?;

        Self::from_month(month, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the month before a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError) if
    /// conversion of [`Date`] to a [`MonthInYear`] failed.
    ///
    /// Returns any error that
    /// [`from_month`](BoundedAbsInterval::from_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let interval = BoundedAbsInterval::month_before_duration_from_date(
    ///     "2026-03-02".parse::<Date>()?,
    ///     CalendarAnchorOffset::Days(5),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.start_time(),
    ///     "2026-02-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     interval.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let date =
            checked_sub_calendar_anchor_offset_to_date(calendar_anchor_offset, date).map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?;

        let month = MonthInYear::try_from(date).or(Err(BoundedAbsIntervalCreationError::ComputationError))?;

        Self::from_month(month, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the month after a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_after_duration_from_date`](BoundedAbsInterval::month_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let month = BoundedAbsInterval::month_after_duration_from_today(
    ///     CalendarAnchorOffset::Months(2),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn month_after_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::month_after_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the month before a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_before_duration_from_date`](BoundedAbsInterval::month_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let month = BoundedAbsInterval::month_before_duration_from_today(
    ///     CalendarAnchorOffset::Months(2),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn month_before_duration_from_today(
        calendar_anchor_offset: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::month_before_duration_from_date(date_today(tz.clone()), calendar_anchor_offset, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the current month in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError) if
    /// conversion of today's [`Date`] to a [`MonthInYear`] failed.
    ///
    /// Return any error that
    /// [`from_month`](BoundedAbsInterval::from_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let month = BoundedAbsInterval::this_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn this_month(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        let month =
            MonthInYear::try_from(date_today(tz.clone())).or(Err(BoundedAbsIntervalCreationError::ComputationError))?;

        Self::from_month(month, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the next month in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_after_duration_from_today`](BoundedAbsInterval::month_after_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let month = BoundedAbsInterval::next_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn next_month(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::month_after_duration_from_today(CalendarAnchorOffset::Months(1), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the previous month in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`month_before_duration_from_today`](BoundedAbsInterval::month_before_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let month = BoundedAbsInterval::previous_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn previous_month(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::month_before_duration_from_today(CalendarAnchorOffset::Months(1), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] from the given year in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if
    /// the year's first day is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let year = BoundedAbsInterval::from_year(2026, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     year.start_time(),
    ///     "2026-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     year.end_time(),
    ///     "2027-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_year(year: i16, tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        let first_day_of_year = Date::new(year, 1, 1).or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?;
        let last_day_of_year = first_day_of_year.last_of_year();

        Self::from_inclusive_date_range(first_day_of_year, last_day_of_year, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] from the provided inclusive
    /// year range in the given timezone
    ///
    /// If the given years are not in chronological order, they are swapped.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart) if
    /// the first day of the start year is out of range.
    ///
    /// Returns [`OutOfRangeEnd`](BoundedAbsIntervalCreationError::OutOfRangeEnd) if
    /// the last day of the end year is out of range.
    ///
    /// Returns any error that
    /// [`from_inclusive_date_range`](BoundedAbsInterval::from_inclusive_date_range)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let years =
    ///     BoundedAbsInterval::from_inclusive_year_range(2025, 2030, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     years.start_time(),
    ///     "2025-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(years.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     years.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        if start_year > end_year {
            std::mem::swap(&mut start_year, &mut end_year);
        }

        let first_day_of_start_year =
            Date::new(start_year, 1, 1).or(Err(BoundedAbsIntervalCreationError::OutOfRangeStart))?;

        let last_day_of_end_year = Date::new(end_year, 1, 1)
            .or(Err(BoundedAbsIntervalCreationError::OutOfRangeEnd))?
            .last_of_year();

        Self::from_inclusive_date_range(first_day_of_start_year, last_day_of_end_year, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the year after a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_year`](BoundedAbsInterval::from_year)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsInterval::year_after_duration_from_date(
    ///     "2026-05-05".parse::<Date>()?,
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     year.start_time(),
    ///     "2027-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     year.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let year = checked_add_calendar_anchor_offset_to_date(calendar_anchor_offset, date)
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?
            .year();

        Self::from_year(year, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the year before a given
    /// [`CalendarAnchorOffset`] relative to the given date in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](BoundedAbsIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    ///
    /// Returns [`OutOfRangeStart`](BoundedAbsIntervalCreationError::OutOfRangeStart)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`from_year`](BoundedAbsInterval::from_year)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsInterval::year_before_duration_from_date(
    ///     "2026-05-05".parse::<Date>()?,
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     year.start_time(),
    ///     "2025-01-01 00:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(
    ///     year.end_time(),
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
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        let year = checked_sub_calendar_anchor_offset_to_date(calendar_anchor_offset, date)
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => BoundedAbsIntervalCreationError::ComputationError,
                CalendarAnchorOffsetDateError::OutOfRangeResult => BoundedAbsIntervalCreationError::OutOfRangeStart,
            })?
            .year();

        Self::from_year(year, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the year after a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_after_duration_from_date`](BoundedAbsInterval::year_after_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsInterval::year_after_duration_from_today(
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn year_after_duration_from_today(
        duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::year_after_duration_from_date(date_today(tz.clone()), duration, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the year before a given
    /// [`CalendarAnchorOffset`] relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_before_duration_from_date`](BoundedAbsInterval::year_before_duration_from_date)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// # use periodical::time::CalendarAnchorOffset;
    /// let year = BoundedAbsInterval::year_before_duration_from_today(
    ///     CalendarAnchorOffset::Months(15),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn year_before_duration_from_today(
        duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::year_before_duration_from_date(date_today(tz.clone()), duration, tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the current year in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that [`from_year`](BoundedAbsInterval::from_year)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let year = BoundedAbsInterval::this_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn this_year(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::from_year(date_today(tz.clone()).year(), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the next year in the given
    /// timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_after_duration_from_today`](BoundedAbsInterval::year_after_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let year = BoundedAbsInterval::next_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn next_year(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::year_after_duration_from_today(CalendarAnchorOffset::Years(1), tz)
    }

    /// Creates a new [`BoundedAbsInterval`] of the previous year in the
    /// given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that
    /// [`year_before_duration_from_today`](BoundedAbsInterval::year_before_duration_from_today)
    /// may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let year = BoundedAbsInterval::next_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn previous_year(tz: TimeZone) -> Result<Self, BoundedAbsIntervalCreationError> {
        Self::year_before_duration_from_today(CalendarAnchorOffset::Years(1), tz)
    }
}

//! Convenience methods for [`BoundedAbsoluteInterval`]

use jiff::civil::Weekday;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
use crate::time::CalendarAnchorOffset;

impl BoundedAbsoluteInterval {
    /// Creates a new [`BoundedAbsoluteInterval`] of the given date in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`StartInTimeGap`](BoundedAbsoluteIntervalCreationError::StartInTimeGap) if the given date
    /// at midnight in the given timezone is positioned inside a time gap[^1].
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if the day after
    /// the given date is out of range.
    ///
    /// Returns [`EndInTimeGap`](BoundedAbsoluteIntervalCreationError::EndInTimeGap) if the day after the given date
    /// at midnight in the given timezone is positioned inside a time gap[^1].
    ///
    /// [^1]: See [`MappedLocalTime::None`](chrono::offset::LocalResult::None)
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use chrono::{DateTime, Duration, Utc, Date, FixedOffset};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let date = Date::from_ymd_opt(2026, 1, 5).ok_or(DateFromYmdError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::from_date(date, offset_tz)?;
    ///
    /// assert_eq!(interval.start_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), "2026-01-05 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn from_date(naive_date: Date, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let start = naive_date
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz.clone())
            .earliest()
            .ok_or(BoundedAbsoluteIntervalCreationError::StartInTimeGap)?;

        let next_day = naive_date
            .checked_add_days(Days::new(1))
            .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?;
        let end = next_day
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz)
            .latest()
            .ok_or(BoundedAbsoluteIntervalCreationError::EndInTimeGap)?;

        Ok(Self::unchecked_new_with_inclusivity(
            start.with_timezone(&Utc),
            BoundInclusivity::Inclusive,
            end.with_timezone(&Utc),
            BoundInclusivity::Exclusive,
        ))
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day after a given [naive duration](NaiveDuration)
    /// relative to the given day in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_add_naive_duration_to_naive_date`](`checked_add_naive_duration_to_naive_date)
    /// returns [`None`].
    ///
    /// See [`from_date`](BoundedAbsoluteInterval::from_date) for more errors that could occur, as this method
    /// uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::day_after_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 4, 29).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Days(5),
    ///     offset_tz
    /// )?;
    ///
    /// assert_eq!(interval.start_time(), "2026-05-03 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), "2026-05-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn day_after_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_date(
            checked_add_naive_duration_to_naive_date(naive_date, naive_duration)
                .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day after a given [naive duration](NaiveDuration)
    /// relative to the given day in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_sub_naive_duration_to_naive_date`](`checked_sub_naive_duration_to_naive_date)
    /// returns [`None`].
    ///
    /// See [`from_date`](BoundedAbsoluteInterval::from_date) for more errors that could occur, as this method
    /// uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::day_before_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 4, 29).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Days(5),
    ///     offset_tz
    /// )?;
    ///
    /// assert_eq!(interval.start_time(), "2026-04-23 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), "2026-04-24 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn day_before_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_date(
            checked_sub_naive_duration_to_naive_date(naive_date, naive_duration)
                .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day after a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`day_after_naive_duration_from_naive_date`](BoundedAbsoluteInterval::day_after_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, Utc, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::day_after_naive_duration_from_today(
    ///     NaiveDuration::Days(5),
    ///     offset_tz
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn day_after_naive_duration_from_today<Tz>(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_after_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the day before a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`day_before_naive_duration_from_naive_date`](BoundedAbsoluteInterval::day_before_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, Utc, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::day_before_naive_duration_from_today(
    ///     NaiveDuration::Days(5),
    ///     offset_tz
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn day_before_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_before_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Returns the current day in the given [`TimeZone`] as a [`BoundedAbsoluteInterval`]
    ///
    /// Uses [`from_date`](BoundedAbsoluteInterval::from_date) with the current day.
    ///
    /// # Errors
    ///
    /// Returns [`StartInTimeGap`](BoundedAbsoluteIntervalCreationError::StartInTimeGap) if today at midnight
    /// in the given timezone is positioned inside a time gap[^1].
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if tomorrow's date
    /// is out of range.
    ///
    /// Returns [`EndInTimeGap`](BoundedAbsoluteIntervalCreationError::EndInTimeGap) if tomorrow at midnight
    /// in the given timezone is positioned inside a time gap[^1].
    ///
    /// [^1]: See [`MappedLocalTime::None`](chrono::offset::LocalResult::None)
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, Utc, Date, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let today = BoundedAbsoluteInterval::today(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn today(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_date(naive_date_today(&tz), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of tomorrow in the given timezone
    ///
    /// # Errors
    ///
    /// See [`day_after_naive_duration_from_today`](BoundedAbsoluteInterval::day_after_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, Utc, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let tomorrow = BoundedAbsoluteInterval::tomorrow(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn tomorrow(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_after_naive_duration_from_today(CalendarAnchorOffset::Days(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of yesterday in the given timezone
    ///
    /// # Errors
    ///
    /// See [`day_before_naive_duration_from_today`](BoundedAbsoluteInterval::day_before_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, Utc, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let yesterday = BoundedAbsoluteInterval::yesterday(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn yesterday(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::day_before_naive_duration_from_today(CalendarAnchorOffset::Days(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided inclusive date range in the given timezone
    ///
    /// Dates given in reverse chronological order are treated the same way as if they were provided
    /// in chronological order.
    ///
    /// # Errors
    ///
    /// Returns [`StartInTimeGap`](BoundedAbsoluteIntervalCreationError::StartInTimeGap) if the given start date
    /// at midnight in the given timezone is positioned inside a time gap[^1].
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if the day after
    /// the given end date is out of range.
    ///
    /// Returns [`EndInTimeGap`](BoundedAbsoluteIntervalCreationError::EndInTimeGap) if the day after
    /// the given end date at midnight in the given timezone is positioned inside a time gap[^1].
    ///
    /// [^1]: See [`MappedLocalTime::None`](chrono::offset::LocalResult::None)
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, Utc, Date, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let start = Date::from_ymd_opt(2026, 1, 5).ok_or(DateFromYmdError)?;
    /// let end = Date::from_ymd_opt(2026, 1, 10).ok_or(DateFromYmdError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_date_range(start, end, offset_tz)?;
    ///
    /// assert_eq!(interval.start_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), "2026-01-10 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
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
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz.clone())
            .earliest()
            .ok_or(BoundedAbsoluteIntervalCreationError::StartInTimeGap)?;

        let end = end_date
            .checked_add_days(Days::new(1))
            .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz)
            .latest()
            .ok_or(BoundedAbsoluteIntervalCreationError::EndInTimeGap)?;

        Ok(Self::unchecked_new_with_inclusivity(
            start.with_timezone(&Utc),
            BoundInclusivity::Inclusive,
            end.with_timezone(&Utc),
            BoundInclusivity::Exclusive,
        ))
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided week in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the week's first date is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the week's last date is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let week = Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?.week(Weekday::Tue);
    ///
    /// let week_interval = BoundedAbsoluteInterval::from_week(week, offset_tz)?;
    ///
    /// assert_eq!(week_interval.start_time(), "2026-04-27 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week_interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week_interval.end_time(), "2026-05-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week_interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_week(week: NaiveWeek, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_inclusive_date_range(
            week.checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            week.checked_last_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided inclusive week range in the given timezone
    ///
    /// Weeks given in reverse chronological order are treated the same way as if they were provided
    /// in chronological order.
    ///
    /// Note that the given start/end weeks can have different start days, so the resulting interval may not
    /// always be a multiple of 7 days.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the start week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the end week's last day is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Datelike, DateTime, Duration, FixedOffset, Date, NaiveWeek, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let start = Date::from_ymd_opt(2026, 1, 7).ok_or(DateFromYmdError)?.week(Weekday::Mon);
    /// let end = Date::from_ymd_opt(2026, 3, 17).ok_or(DateFromYmdError)?.week(Weekday::Sat);
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_week_range(start, end, offset_tz)?;
    ///
    /// assert_eq!(interval.start_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), "2026-03-20 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_week_range<Tz>(
        mut start: NaiveWeek,
        mut end: NaiveWeek,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if start.checked_first_day() > end.checked_first_day() {
            std::mem::swap(&mut start, &mut end);
        }

        Self::from_inclusive_date_range(
            start.checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            end.checked_last_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the week after a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_add_naive_duration_to_naive_date`](`checked_add_naive_duration_to_naive_date)
    /// returns [`None`].
    ///
    /// See [`from_week`](BoundedAbsoluteInterval::from_week) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let week = BoundedAbsoluteInterval::week_after_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Weeks(Weekday::Mon, 2),
    ///     Weekday::Mon,
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(week.start_time(), "2026-05-10 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.end_time(), "2026-05-17 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn week_after_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        week_start: Weekday,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let week = checked_add_naive_duration_to_naive_date(naive_date, naive_duration)
            .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?
            .week(week_start);

        Self::from_week(week, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the week before a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_sub_naive_duration_to_naive_date`](`checked_sub_naive_duration_to_naive_date)
    /// returns [`None`].
    ///
    /// See [`from_week`](BoundedAbsoluteInterval::from_week) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let week = BoundedAbsoluteInterval::week_before_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Weeks(Weekday::Mon, 2),
    ///     Weekday::Mon,
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(week.start_time(), "2026-04-12 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.end_time(), "2026-04-19 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn week_before_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        week_start: Weekday,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let week = checked_sub_naive_duration_to_naive_date(naive_date, naive_duration)
            .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?
            .week(week_start);

        Self::from_week(week, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the week after a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`week_after_naive_duration_from_naive_date`](BoundedAbsoluteInterval::week_after_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let week = BoundedAbsoluteInterval::week_after_naive_duration_from_today(
    ///     NaiveDuration::Months(2),
    ///     Weekday::Mon,
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn week_after_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        week_start: Weekday,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::week_after_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, week_start, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the week before a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`week_before_naive_duration_from_naive_date`](BoundedAbsoluteInterval::week_before_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let week = BoundedAbsoluteInterval::week_before_naive_duration_from_today(
    ///     NaiveDuration::Months(2),
    ///     Weekday::Mon,
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn week_before_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        week_start: Weekday,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::week_before_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, week_start, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the current week in the given timezone
    ///
    /// Since the definition of a _week_ changes from place to place, this method requires the day of the week
    /// to consider as the start of a week.
    ///
    /// If you want a stable _week_ definition, use [`this_iso_week`](BoundedAbsoluteInterval::this_iso_week),
    /// which uses [ISO weeks](https://en.wikipedia.org/w/index.php?title=ISO_week_date&oldid=1334192696).
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the week's start is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the week's end is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let this_week = BoundedAbsoluteInterval::this_week(
    ///     Weekday::Mon,
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn this_week(week_start: Weekday, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let this_week = naive_date_today(&tz).week(week_start);

        Self::from_inclusive_date_range(
            this_week
                .checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            this_week
                .checked_last_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the next week in the given timezone
    ///
    /// Since the definition of a _week_ changes from place to place, this method requires the day of the week
    /// to consider as the start of a week.
    ///
    /// If you want a stable _week_ definition, use [`next_iso_week`](BoundedAbsoluteInterval::next_iso_week),
    /// which uses [ISO weeks](https://en.wikipedia.org/w/index.php?title=ISO_week_date&oldid=1334192696).
    ///
    /// # Errors
    ///
    /// See [`week_after_naive_duration_from_today`](BoundedAbsoluteInterval::week_after_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let next_week = BoundedAbsoluteInterval::next_week(
    ///     Weekday::Mon,
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn next_week(week_start: Weekday, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::week_after_naive_duration_from_today(CalendarAnchorOffset::Weeks(week_start, 1), week_start, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the previous week in the given timezone
    ///
    /// Since the definition of a _week_ changes from place to place, this method requires the day of the week
    /// to consider as the start of a week.
    ///
    /// If you want a stable _week_ definition, use [`previous_iso_week`](BoundedAbsoluteInterval::previous_iso_week),
    /// which uses [ISO weeks](https://en.wikipedia.org/w/index.php?title=ISO_week_date&oldid=1334192696).
    ///
    /// # Errors
    ///
    /// See [`week_before_naive_duration_from_today`](BoundedAbsoluteInterval::week_before_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let previous_week = BoundedAbsoluteInterval::previous_week(
    ///     Weekday::Mon,
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn previous_week(week_start: Weekday, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::week_before_naive_duration_from_today(CalendarAnchorOffset::Weeks(week_start, 1), week_start, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided ISO week in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the week's first date is out of range.
    ///
    /// See [`from_week`](BoundedAbsoluteInterval::from_week) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Datelike, DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    /// let iso_week = Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?.iso_week();
    ///
    /// let iso_week_interval = BoundedAbsoluteInterval::from_iso_week(iso_week, offset_tz)?;
    ///
    /// assert_eq!(iso_week_interval.start_time(), "2026-04-26 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week_interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(iso_week_interval.end_time(), "2026-05-03 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week_interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_iso_week(iso_week: IsoWeek, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_week(
            Date::from_isoywd_opt(iso_week.year(), iso_week.week(), Weekday::Mon)
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?
                .week(Weekday::Mon),
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided inclusive ISO week range in the given timezone
    ///
    /// Weeks given in reverse chronological order are treated the same way as if they were provided
    /// in chronological order.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the start week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the end week's last day is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Datelike, DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// // Currently chrono has no public constructor for IsoWeek yet
    /// let start = Date::from_ymd_opt(2026, 1, 7).ok_or(DateFromYmdError)?.iso_week();
    /// let end = Date::from_ymd_opt(2026, 3, 17).ok_or(DateFromYmdError)?.iso_week();
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(start, end, offset_tz)?;
    ///
    /// assert_eq!(interval.start_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), "2026-03-22 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_iso_week_range(
        mut start: IsoWeek,
        mut end: IsoWeek,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if start.year() > end.year() || (start.year() == end.year() && start.week() > end.week()) {
            std::mem::swap(&mut start, &mut end);
        }

        Self::from_inclusive_date_range(
            Date::from_isoywd_opt(start.year(), start.week(), Weekday::Mon)
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            Date::from_isoywd_opt(end.year(), end.week(), Weekday::Sun)
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the given week from the ISO year and week numbers
    /// in the given timezone
    ///
    /// Weeks given in reverse chronological order are treated the same way as if they were provided
    /// in chronological order.
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// the provided ISO year and week numbers are invalid.
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the week's last day is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let iso_week = BoundedAbsoluteInterval::week_from_iso_year_week(2026, 5, offset_tz)?;
    ///
    /// assert_eq!(iso_week.start_time(), "2026-01-25 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(iso_week.end_time(), "2026-02-01 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn week_from_iso_year_week(
        year: i32,
        week: u8,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let iso_week = Date::from_isoywd_opt(year, u32::from(week), Weekday::Mon)
            .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?
            .week(Weekday::Mon);

        Self::from_inclusive_date_range(
            iso_week
                .checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            iso_week
                .checked_last_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the ISO week after a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// See [`week_after_naive_duration_from_naive_date`](BoundedAbsoluteInterval::week_after_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let week = BoundedAbsoluteInterval::iso_week_after_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::IsoWeeks(2),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(week.start_time(), "2026-05-10 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.end_time(), "2026-05-17 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn iso_week_after_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::week_after_naive_duration_from_naive_date(naive_date, naive_duration, Weekday::Mon, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the ISO week before a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// See [`week_before_naive_duration_from_naive_date`](BoundedAbsoluteInterval::week_before_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let week = BoundedAbsoluteInterval::iso_week_before_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::IsoWeeks(2),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(week.start_time(), "2026-04-12 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.end_time(), "2026-04-19 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn iso_week_before_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::week_before_naive_duration_from_naive_date(naive_date, naive_duration, Weekday::Mon, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the ISO week after a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`iso_week_after_naive_duration_from_naive_date`](BoundedAbsoluteInterval::iso_week_after_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let iso_week = BoundedAbsoluteInterval::iso_week_after_naive_duration_from_today(
    ///     NaiveDuration::Months(2),
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn iso_week_after_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::iso_week_after_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the ISO week before a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`iso_week_before_naive_duration_from_naive_date`](BoundedAbsoluteInterval::iso_week_before_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let iso_week = BoundedAbsoluteInterval::iso_week_before_naive_duration_from_today(
    ///     NaiveDuration::Months(2),
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn iso_week_before_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::iso_week_before_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the current ISO week in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// the current ISO week has a week number that doesn't fit in an [`u8`], which is not normally possible.
    ///
    /// See [`week_from_iso_year_week`](BoundedAbsoluteInterval::week_from_iso_year_week) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let iso_week = BoundedAbsoluteInterval::this_iso_week(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn this_iso_week(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let this_iso_week = naive_date_today(&tz).iso_week();

        Self::week_from_iso_year_week(
            this_iso_week.year(),
            u8::try_from(this_iso_week.week()).or(Err(BoundedAbsoluteIntervalCreationError::DateOperationError))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the next ISO week in the given timezone
    ///
    /// # Errors
    ///
    /// See [`iso_week_after_naive_duration_from_today`](BoundedAbsoluteInterval::iso_week_after_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let iso_week = BoundedAbsoluteInterval::next_iso_week(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn next_iso_week(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::iso_week_after_naive_duration_from_today(CalendarAnchorOffset::IsoWeeks(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the previous ISO week in the given timezone
    ///
    /// # Errors
    ///
    /// See [`iso_week_before_naive_duration_from_today`](BoundedAbsoluteInterval::iso_week_before_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let iso_week = BoundedAbsoluteInterval::previous_iso_week(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn previous_iso_week(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::iso_week_before_naive_duration_from_today(CalendarAnchorOffset::IsoWeeks(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the given month in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the first day of the month is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the last day of the month is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Month, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveMonth;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::from_month(
    ///     NaiveMonth::new(2026, Month::May),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(month.start_time(), "2026-04-30 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(month.end_time(), "2026-05-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_month(month: MonthInYear, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_inclusive_date_range(
            month
                .checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            month
                .checked_last_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided inclusive month range in the given timezone
    ///
    /// Months given in reverse chronological order are treated the same way as if they were provided
    /// in chronological order.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the start month's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the end month's last day is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Month, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveMonth;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_month_range(
    ///     NaiveMonth::new(2026, Month::January),
    ///     NaiveMonth::new(2026, Month::May),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(interval.start_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.end_time(), "2026-05-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_month_range(
        mut start: MonthInYear,
        mut end: MonthInYear,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if start > end {
            std::mem::swap(&mut start, &mut end);
        }

        Self::start_inclusive_date_range(
            start.checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            end.checked_last_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month after a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_add_naive_duration_to_naive_date`](`checked_add_naive_duration_to_naive_date)
    /// returns [`None`], or if conversion of today's [`Date`] to a [`NaiveMonth`] failed.
    ///
    /// See [`from_month`](BoundedAbsoluteInterval::from_month) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::month_after_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 5).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Months(2),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(month.start_time(), "2026-06-30 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(month.end_time(), "2026-07-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn month_after_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let day = checked_add_naive_duration_to_naive_date(naive_date, naive_duration)
            .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?;

        Self::from_month(
            MonthInYear::try_from(day).or(Err(BoundedAbsoluteIntervalCreationError::DateOperationError))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month before a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_sub_naive_duration_to_naive_date`](`checked_sub_naive_duration_to_naive_date)
    /// returns [`None`], or if conversion of today's [`Date`] to a [`NaiveMonth`] failed.
    ///
    /// See [`from_month`](BoundedAbsoluteInterval::from_month) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::month_before_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 5).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Months(2),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(month.start_time(), "2026-02-28 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(month.end_time(), "2026-03-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn month_before_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let day = checked_sub_naive_duration_to_naive_date(naive_date, naive_duration)
            .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?;

        Self::from_month(
            MonthInYear::try_from(day).or(Err(BoundedAbsoluteIntervalCreationError::DateOperationError))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month after a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`month_after_naive_duration_from_naive_date`](BoundedAbsoluteInterval::month_after_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::month_after_naive_duration_from_today(
    ///     NaiveDuration::Months(2),
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn month_after_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_after_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the month after a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`month_before_naive_duration_from_naive_date`](BoundedAbsoluteInterval::month_before_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::month_before_naive_duration_from_today(
    ///     NaiveDuration::Months(2),
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn month_before_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_before_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the current month in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// conversion of today's [`Date`] to a [`NaiveMonth`] failed.
    ///
    /// See [`from_month`](BoundedAbsoluteInterval::from_month) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::this_month(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn this_month(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_month(
            MonthInYear::try_from(naive_date_today(&tz))
                .or(Err(BoundedAbsoluteIntervalCreationError::DateOperationError))?,
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the next month in the given timezone
    ///
    /// # Errors
    ///
    /// See [`month_after_naive_duration_from_today`](BoundedAbsoluteInterval::month_after_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::next_month(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn next_month(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_after_naive_duration_from_today(CalendarAnchorOffset::Months(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the previous month in the given timezone
    ///
    /// # Errors
    ///
    /// See [`month_before_naive_duration_from_today`](BoundedAbsoluteInterval::month_before_naive_duration_from_today)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let month = BoundedAbsoluteInterval::previous_month(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn previous_month(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::month_before_naive_duration_from_today(CalendarAnchorOffset::Months(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the given year in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the year's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the year's last day is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::from_year(2026, offset_tz)?;
    ///
    /// assert_eq!(year.start_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(year.end_time(), "2026-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_year(year: i32, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let first_day_of_year =
            Date::from_yo_opt(year, 1).ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?;

        let last_day_of_year = Date::from_yo_opt(
            year,
            if first_day_of_year.leap_year() {
                u32::from(DAYS_IN_LEAP_YEAR)
            } else {
                u32::from(DAYS_IN_COMMON_YEAR)
            },
        )
        .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?;

        Self::from_inclusive_date_range(first_day_of_year, last_day_of_year, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] from the provided inclusive year range in the given timezone
    ///
    /// Years given in reverse chronological order are treated the same way as if they were provided
    /// in chronological order.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the first day of `start_year` is out of range.
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// the first day of `end_year` is out of range (needed in order to determine if the year is a leap year).
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the last day of `end_year` is out of range.
    ///
    /// See [`from_inclusive_date_range`](BoundedAbsoluteInterval::from_inclusive_date_range) for more errors
    /// that could occur, as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let years = BoundedAbsoluteInterval::from_inclusive_year_range(2025, 2030, offset_tz)?;
    ///
    /// assert_eq!(years.start_time(), "2024-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(years.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(years.end_time(), "2030-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(years.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_year_range(
        mut start_year: i32,
        mut end_year: i32,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if start_year > end_year {
            std::mem::swap(&mut start_year, &mut end_year);
        }

        let first_day_of_start_year =
            Date::from_yo_opt(start_year, 1).ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?;

        let first_day_of_end_year =
            Date::from_yo_opt(end_year, 1).ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?;

        let last_day_of_end_year = Date::from_yo_opt(
            end_year,
            if first_day_of_end_year.leap_year() {
                u32::from(DAYS_IN_LEAP_YEAR)
            } else {
                u32::from(DAYS_IN_COMMON_YEAR)
            },
        )
        .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?;

        Self::from_inclusive_date_range(first_day_of_start_year, last_day_of_end_year, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year after a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_add_naive_duration_to_naive_date`](`checked_add_naive_duration_to_naive_date)
    /// returns [`None`].
    ///
    /// See [`from_year`](BoundedAbsoluteInterval::from_year) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::year_after_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 5).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Months(15),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(year.start_time(), "2026-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(year.end_time(), "2027-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn year_after_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_year(
            checked_add_naive_duration_to_naive_date(naive_date, naive_duration)
                .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?
                .year(),
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year before a given [naive duration](NaiveDuration)
    /// relative to the given date in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// [`time::checked_sub_naive_duration_to_naive_date`](`checked_sub_naive_duration_to_naive_date)
    /// returns [`None`].
    ///
    /// See [`from_year`](BoundedAbsoluteInterval::from_year) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # struct DateFromYmdError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     DateFromYmdError(DateFromYmdError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// #     ParseError(chrono::format::ParseError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<DateFromYmdError> for ExampleError {
    /// #     fn from(value: DateFromYmdError) -> Self {
    /// #         ExampleError::DateFromYmdError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<chrono::format::ParseError> for ExampleError {
    /// #     fn from(value: chrono::format::ParseError) -> Self {
    /// #         ExampleError::ParseError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::year_before_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 5, 5).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Months(15),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(year.start_time(), "2024-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.start_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(year.end_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.end_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn year_before_naive_duration_from_naive_date(
        naive_date: Date,
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_year(
            checked_sub_naive_duration_to_naive_date(naive_date, naive_duration)
                .ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?
                .year(),
            tz,
        )
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year after a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`year_after_naive_duration_from_naive_date`](BoundedAbsoluteInterval::year_after_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::year_after_naive_duration_from_today(
    ///     NaiveDuration::Months(15),
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn year_after_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_after_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the year before a given [naive duration](NaiveDuration)
    /// relative to today in the given timezone
    ///
    /// # Errors
    ///
    /// See [`year_before_naive_duration_from_naive_date`](BoundedAbsoluteInterval::year_before_naive_duration_from_naive_date)
    /// for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// # use periodical::time::NaiveDuration;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::year_before_naive_duration_from_today(
    ///     NaiveDuration::Months(15),
    ///     offset_tz,
    /// )?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn year_before_naive_duration_from_today(
        naive_duration: CalendarAnchorOffset,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_before_naive_duration_from_naive_date(naive_date_today(&tz), naive_duration, tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the current year in the given timezone
    ///
    /// # Errors
    ///
    /// See [`from_year`](BoundedAbsoluteInterval::from_year) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::this_year(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn this_year(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::from_year(naive_date_today(&tz).year(), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the next year in the given timezone
    ///
    /// # Errors
    ///
    /// See [`from_year`](BoundedAbsoluteInterval::from_year) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, BoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     BoundedAbsoluteIntervalCreationError(BoundedAbsoluteIntervalCreationError),
    /// # }
    /// #
    /// # impl From<TryFromIntError> for ExampleError {
    /// #     fn from(value: TryFromIntError) -> Self {
    /// #         ExampleError::TryFromIntError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<FixedOffsetError> for ExampleError {
    /// #     fn from(value: FixedOffsetError) -> Self {
    /// #         ExampleError::FixedOffsetError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<BoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: BoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::BoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::next_year(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn next_year(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_after_naive_duration_from_today(CalendarAnchorOffset::Years(1), tz)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] of the previous year in the given timezone
    ///
    /// # Errors
    ///
    /// See [`from_year`](BoundedAbsoluteInterval::from_year) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let year = BoundedAbsoluteInterval::previous_year(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn previous_year(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_before_naive_duration_from_today(CalendarAnchorOffset::Years(1), tz)
    }
}

//! Convenience methods for [`HalfBoundedAbsoluteInterval`]

impl HalfBoundedAbsoluteInterval {
    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans from now on
    ///
    /// The given inclusivity refers to whether we should include or exclude the current time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let from_now_on = HalfBoundedAbsoluteInterval::since_now(BoundInclusivity::Inclusive);
    /// ```
    #[must_use]
    pub fn since_now(inclusivity: BoundInclusivity) -> Self {
        Self::new_with_inclusivity(Timestamp::now(), inclusivity, OpeningDirection::ToFuture)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until now
    ///
    /// The given inclusivity refers to whether we should include or exclude the current time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let until_now = HalfBoundedAbsoluteInterval::until_now(BoundInclusivity::Inclusive);
    /// ```
    #[must_use]
    pub fn until_now(inclusivity: BoundInclusivity) -> Self {
        Self::new_with_inclusivity(Timestamp::now(), inclusivity, OpeningDirection::ToPast)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the start of the given day in the given timezone
    ///
    /// The start of the resulting interval is [inclusive](BoundInclusivity::Inclusive).
    ///
    /// # Errors
    ///
    /// Returns [`ReferenceTimeInTimeGap`](HalfBoundedAbsoluteIntervalCreationError::ReferenceTimeInTimeGap) if
    /// the given date's start (midnight) is positioned inside a time gap[^1].
    ///
    /// [^1]: See [`MappedLocalTime::None`](chrono::offset::LocalResult::None)
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
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
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let from_first_of_may = HalfBoundedAbsoluteInterval::since_date(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?,
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(from_first_of_may.reference_time(), "2026-04-30 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(from_first_of_may.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(from_first_of_may.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_date(date: Date, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let reference_time = date
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz)
            .earliest()
            .ok_or(HalfBoundedAbsoluteIntervalCreationError::ReferenceTimeInTimeGap)?
            .with_timezone(&Utc);

        Ok(Self::new(reference_time, OpeningDirection::ToFuture))
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the start of the given day in the given timezone
    ///
    /// The end of the resulting interval is [exclusive](BoundInclusivity::Exclusive).
    ///
    /// # Errors
    ///
    /// Returns [`ReferenceTimeInTimeGap`](HalfBoundedAbsoluteIntervalCreationError::ReferenceTimeInTimeGap) if
    /// the given date's start (midnight) is positioned inside a time gap[^1].
    ///
    /// [^1]: See [`MappedLocalTime::None`](chrono::offset::LocalResult::None)
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
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
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let until_first_of_may = HalfBoundedAbsoluteInterval::until_date(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?,
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(until_first_of_may.reference_time(), "2026-04-30 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(until_first_of_may.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(until_first_of_may.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_date(date: Date, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let reference_time = date
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz)
            .earliest()
            .ok_or(HalfBoundedAbsoluteIntervalCreationError::ReferenceTimeInTimeGap)?
            .with_timezone(&Utc);

        Ok(Self::new_with_inclusivity(
            reference_time,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ))
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since today in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_today = HalfBoundedAbsoluteInterval::since_today(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_today(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(date_today(&tz), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until today in the given timezone
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Errors
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let until_today = HalfBoundedAbsoluteInterval::until_today(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_today(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(date_today(&tz), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since tomorrow in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// [`checked_add_duration_to_date`] returns [`None`].
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_tomorrow = HalfBoundedAbsoluteInterval::since_tomorrow(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_tomorrow(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            checked_add_duration_to_date(date_today(&tz), CalendarAnchorOffset::Days(1))
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until tomorrow in the given timezone
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// [`checked_add_duration_to_date`] returns [`None`].
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let until_tomorrow = HalfBoundedAbsoluteInterval::until_tomorrow(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_tomorrow(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            checked_add_duration_to_date(date_today(&tz), CalendarAnchorOffset::Days(1))
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since yesterday in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// [`checked_sub_duration_to_date`] returns [`None`].
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_yesterday = HalfBoundedAbsoluteInterval::since_yesterday(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_yesterday(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            checked_sub_duration_to_date(date_today(&tz), CalendarAnchorOffset::Days(1))
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until yesterday in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// [`checked_sub_duration_to_date`] returns [`None`].
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let until_yesterday = HalfBoundedAbsoluteInterval::until_yesterday(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_yesterday(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            checked_sub_duration_to_date(date_today(&tz), CalendarAnchorOffset::Days(1))
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the given week in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the week's first day is out of range.
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
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
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let interval = HalfBoundedAbsoluteInterval::since_week(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?.week(Weekday::Mon),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(interval.reference_time(), "2026-04-26 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_week(week: NaiveWeek, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            week.checked_first_day()
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the given week in the given timezone
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the week's first day is out of range.
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
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
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let interval = HalfBoundedAbsoluteInterval::until_week(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?.week(Weekday::Mon),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(interval.reference_time(), "2026-04-26 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_week(week: NaiveWeek, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            week.checked_first_day()
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the current week in the given timezone
    ///
    /// See [`since_week`](HalfBoundedAbsoluteInterval::since_week) for more details.
    ///
    /// # Errors
    ///
    /// See [`since_week`](HalfBoundedAbsoluteInterval::since_week) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_this_week = HalfBoundedAbsoluteInterval::since_this_week(Weekday::Mon, offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_this_week(week_start: Weekday, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_week(date_today(&tz).week(week_start), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the current week in the given timezone
    ///
    /// See [`until_week`](HalfBoundedAbsoluteInterval::until_week) for more details.
    ///
    /// # Errors
    ///
    /// See [`until_week`](HalfBoundedAbsoluteInterval::until_week) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let until_this_week = HalfBoundedAbsoluteInterval::until_this_week(Weekday::Mon, offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    pub fn until_this_week(week_start: Weekday, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_week(date_today(&tz).week(week_start), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the given ISO week in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the week's first day is out of range.
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Datelike, DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
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
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let interval = HalfBoundedAbsoluteInterval::since_iso_week(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?.iso_week(),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(interval.reference_time(), "2026-04-26 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_iso_week(iso_week: IsoWeek, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            Date::from_isoywd_opt(iso_week.year(), iso_week.week(), Weekday::Mon)
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the given ISO week in the given timezone
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the week's first day is out of range.
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Datelike, DateTime, Duration, FixedOffset, Date, Utc, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
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
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let interval = HalfBoundedAbsoluteInterval::until_iso_week(
    ///     Date::from_ymd_opt(2026, 5, 1).ok_or(DateFromYmdError)?.iso_week(),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(interval.reference_time(), "2026-04-26 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_iso_week(iso_week: IsoWeek, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            Date::from_isoywd_opt(iso_week.year(), iso_week.week(), Weekday::Mon)
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the current ISO week in the given timezone
    ///
    /// See [`since_iso_week`](HalfBoundedAbsoluteInterval::since_iso_week) for more details.
    ///
    /// # Errors
    ///
    /// See [`since_iso_week`](HalfBoundedAbsoluteInterval::since_iso_week) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_this_iso_week = HalfBoundedAbsoluteInterval::since_this_iso_week(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_this_iso_week(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_iso_week(date_today(&tz).iso_week(), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the current ISO week in the given timezone
    ///
    /// See [`until_iso_week`](HalfBoundedAbsoluteInterval::until_iso_week) for more details.
    ///
    /// # Errors
    ///
    /// See [`until_iso_week`](HalfBoundedAbsoluteInterval::until_iso_week) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let until_this_iso_week = HalfBoundedAbsoluteInterval::until_this_iso_week(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_this_iso_week(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_iso_week(date_today(&tz).iso_week(), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the given month in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the month's first day is out of range.
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Month, Utc};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::time::NaiveMonth;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let since_month = HalfBoundedAbsoluteInterval::since_month(
    ///     NaiveMonth::new(2026, Month::March),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(since_month.reference_time(), "2026-02-28 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(since_month.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(since_month.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_month(month: MonthInYear, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            month
                .checked_first_day()
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the given month in the given timezone
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the month's first day is out of range.
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Month, Utc};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::time::NaiveMonth;
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let until_month = HalfBoundedAbsoluteInterval::until_month(
    ///     NaiveMonth::new(2026, Month::March),
    ///     offset_tz,
    /// )?;
    ///
    /// assert_eq!(until_month.reference_time(), "2026-02-28 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(until_month.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(until_month.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_month(month: MonthInYear, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            month
                .checked_first_day()
                .ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the current month in the given timezone
    ///
    /// See [`since_month`](HalfBoundedAbsoluteInterval::since_month) for more details.
    ///
    /// # Errors
    ///
    /// See [`since_month`](HalfBoundedAbsoluteInterval::since_month) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_this_month = HalfBoundedAbsoluteInterval::since_this_month(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_this_month(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_month(
            MonthInYear::try_from(date_today(&tz))
                .or(Err(HalfBoundedAbsoluteIntervalCreationError::DateOperationError))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the current month in the given timezone
    ///
    /// See [`until_month`](HalfBoundedAbsoluteInterval::until_month) for more details.
    ///
    /// # Errors
    ///
    /// See [`until_month`](HalfBoundedAbsoluteInterval::until_month) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let until_this_month = HalfBoundedAbsoluteInterval::until_this_month(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_this_month(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_month(
            MonthInYear::try_from(date_today(&tz))
                .or(Err(HalfBoundedAbsoluteIntervalCreationError::DateOperationError))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the given year in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the year's first day is out of range.
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Month, Utc};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let since_year = HalfBoundedAbsoluteInterval::since_year(2026, offset_tz)?;
    ///
    /// assert_eq!(since_year.reference_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(since_year.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(since_year.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_year(year: i32, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            Date::from_yo_opt(year, 1).ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the given year in the given timezone
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// the year's first day is out of range.
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more errors that could occur,
    /// as this method uses it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{DateTime, Duration, FixedOffset, Month, Utc};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
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
    /// let until_year = HalfBoundedAbsoluteInterval::until_year(2026, offset_tz)?;
    ///
    /// assert_eq!(until_year.reference_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(until_year.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(until_year.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_year(year: i32, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            Date::from_yo_opt(year, 1).ok_or(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate)?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the current year in the given timezone
    ///
    /// See [`since_year`](HalfBoundedAbsoluteInterval::since_year) for more details.
    ///
    /// # Errors
    ///
    /// See [`since_year`](HalfBoundedAbsoluteInterval::since_year) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_this_year = HalfBoundedAbsoluteInterval::since_this_year(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn since_this_year(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_year(date_today(&tz).year(), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the current year in the given timezone
    ///
    /// See [`until_year`](HalfBoundedAbsoluteInterval::until_year) for more details.
    ///
    /// # Errors
    ///
    /// See [`until_year`](HalfBoundedAbsoluteInterval::until_year) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::num::TryFromIntError;
    /// # use chrono::{Duration, FixedOffset, Weekday};
    /// # use periodical::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # struct FixedOffsetError;
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     TryFromIntError(TryFromIntError),
    /// #     FixedOffsetError(FixedOffsetError),
    /// #     HalfBoundedAbsoluteIntervalCreationError(HalfBoundedAbsoluteIntervalCreationError),
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
    /// # impl From<HalfBoundedAbsoluteIntervalCreationError> for ExampleError {
    /// #     fn from(value: HalfBoundedAbsoluteIntervalCreationError) -> Self {
    /// #         ExampleError::HalfBoundedAbsoluteIntervalCreationError(value)
    /// #     }
    /// # }
    /// // UTC+02:00
    /// let offset_tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
    ///
    /// let since_this_year = HalfBoundedAbsoluteInterval::until_this_year(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn until_this_year(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_year(date_today(&tz).year(), tz)
    }
}

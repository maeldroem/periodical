
/// A bounded absolute interval
///
/// An interval with a set start and end. Like all specific absolute interval types, it conserves the invariant
/// of its bounds being in chronological order and if the bounds have the same time, they must be inclusive.
///
/// However, like the other specific interval types, it conserves an additional invariant:
/// Its [openness](Openness) cannot change. That is to say a bounded interval must remain a bounded interval.
/// It cannot mutate from being a bounded interval to a half-bounded interval.
///
/// Instead, if you are looking for an absolute interval that doesn't keep the [openness](Openness) invariant,
/// see [`AbsoluteBounds`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct BoundedAbsoluteInterval {
    from: Timestamp,
    to: Timestamp,
    from_inclusivity: BoundInclusivity,
    to_inclusivity: BoundInclusivity,
}

impl BoundedAbsoluteInterval {
    /// Creates a new [`BoundedAbsoluteInterval`] without checking if it violates the invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Even though the times are not in chronological order
    /// let bounded_interval = BoundedAbsoluteInterval::unchecked_new(from_time, to_time);
    ///
    /// // They remain that way
    /// assert_eq!(bounded_interval.from_time(), from_time);
    /// assert_eq!(bounded_interval.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn unchecked_new(from: Timestamp, to: Timestamp) -> Self {
        BoundedAbsoluteInterval {
            from,
            to,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with default bound inclusivities
    ///
    /// If the from time is past the to time, it swaps them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Times that are not in chronological order
    /// let bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // Are swapped
    /// assert_eq!(bounded_interval.from_time(), to_time);
    /// assert_eq!(bounded_interval.to_time(), from_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new(mut from: Timestamp, mut to: Timestamp) -> Self {
        if from > to {
            std::mem::swap(&mut from, &mut to);
        }

        Self::unchecked_new(from, to)
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with the given bound inclusivities without checking
    /// if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Same time, not doubly inclusive
    /// let bounded_interval = BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
    ///     time,
    ///     BoundInclusivity::Inclusive,
    ///     time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn unchecked_new_with_inclusivity(
        from: Timestamp,
        from_inclusivity: BoundInclusivity,
        to: Timestamp,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        BoundedAbsoluteInterval {
            from,
            to,
            from_inclusivity,
            to_inclusivity,
        }
    }

    /// Creates a new [`BoundedAbsoluteInterval`] with the given bound inclusivities
    ///
    /// If the given times are not in chronological order, we swap them so they are in chronological order.
    ///
    /// If the given times are equal but have bound inclusivities other than inclusive,
    /// we set them to [`Inclusive`](BoundInclusivity::Inclusive).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// // Same time, not doubly inclusive
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     time,
    ///     BoundInclusivity::Inclusive,
    ///     time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// // Therefore gets reset to inclusive for both bounds
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Inclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        from: Timestamp,
        from_inclusivity: BoundInclusivity,
        to: Timestamp,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        match from.cmp(&to) {
            Ordering::Less => Self::unchecked_new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            Ordering::Equal => Self::unchecked_new(from, to),
            Ordering::Greater => Self::unchecked_new_with_inclusivity(to, to_inclusivity, from, from_inclusivity),
        }
    }

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
    /// let date = Date::from_ymd_opt(2026, 1, 5).ok_or(DateFromYmdError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::from_date(date, offset_tz)?;
    ///
    /// assert_eq!(interval.from_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.to_time(), "2026-01-05 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_date(naive_date: Date, tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        let from = naive_date
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz.clone())
            .earliest()
            .ok_or(BoundedAbsoluteIntervalCreationError::StartInTimeGap)?;

        let next_day = naive_date
            .checked_add_days(Days::new(1))
            .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?;
        let to = next_day
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz)
            .latest()
            .ok_or(BoundedAbsoluteIntervalCreationError::EndInTimeGap)?;

        Ok(Self::unchecked_new_with_inclusivity(
            from.with_timezone(&Utc),
            BoundInclusivity::Inclusive,
            to.with_timezone(&Utc),
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
    /// let interval = BoundedAbsoluteInterval::day_after_naive_duration_from_naive_date(
    ///     Date::from_ymd_opt(2026, 4, 29).ok_or(DateFromYmdError)?,
    ///     NaiveDuration::Days(5),
    ///     offset_tz
    /// )?;
    ///
    /// assert_eq!(interval.from_time(), "2026-05-03 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.to_time(), "2026-05-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
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
    /// assert_eq!(interval.from_time(), "2026-04-23 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.to_time(), "2026-04-24 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// Returns [`StartInTimeGap`](BoundedAbsoluteIntervalCreationError::StartInTimeGap) if the given from date
    /// at midnight in the given timezone is positioned inside a time gap[^1].
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if the day after
    /// the given to date is out of range.
    ///
    /// Returns [`EndInTimeGap`](BoundedAbsoluteIntervalCreationError::EndInTimeGap) if the day after
    /// the given to date at midnight in the given timezone is positioned inside a time gap[^1].
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
    /// let from = Date::from_ymd_opt(2026, 1, 5).ok_or(DateFromYmdError)?;
    /// let to = Date::from_ymd_opt(2026, 1, 10).ok_or(DateFromYmdError)?;
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_date_range(from, to, offset_tz)?;
    ///
    /// assert_eq!(interval.from_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.to_time(), "2026-01-10 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_date_range(
        mut from_date: Date,
        mut to_date: Date,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if from_date > to_date {
            std::mem::swap(&mut from_date, &mut to_date);
        }

        let from = from_date
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz.clone())
            .earliest()
            .ok_or(BoundedAbsoluteIntervalCreationError::StartInTimeGap)?;

        let to = to_date
            .checked_add_days(Days::new(1))
            .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?
            .and_time(NAIVE_TIME_MIDNIGHT)
            .and_local_timezone(tz)
            .latest()
            .ok_or(BoundedAbsoluteIntervalCreationError::EndInTimeGap)?;

        Ok(Self::unchecked_new_with_inclusivity(
            from.with_timezone(&Utc),
            BoundInclusivity::Inclusive,
            to.with_timezone(&Utc),
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
    /// assert_eq!(week_interval.from_time(), "2026-04-27 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week_interval.to_time(), "2026-05-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week_interval.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// Note that the given from/to weeks can have different start days, so the resulting interval may not
    /// always be a multiple of 7 days.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeStartDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate) if
    /// the from week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the to week's last day is out of range.
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
    /// let from = Date::from_ymd_opt(2026, 1, 7).ok_or(DateFromYmdError)?.week(Weekday::Mon);
    /// let to = Date::from_ymd_opt(2026, 3, 17).ok_or(DateFromYmdError)?.week(Weekday::Sat);
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_week_range(from, to, offset_tz)?;
    ///
    /// assert_eq!(interval.from_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.to_time(), "2026-03-20 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_week_range<Tz>(
        mut from: NaiveWeek,
        mut to: NaiveWeek,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if from.checked_first_day() > to.checked_first_day() {
            std::mem::swap(&mut from, &mut to);
        }

        Self::from_inclusive_date_range(
            from.checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            to.checked_last_day()
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
    /// assert_eq!(week.from_time(), "2026-05-10 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.to_time(), "2026-05-17 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(week.from_time(), "2026-04-12 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.to_time(), "2026-04-19 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(iso_week_interval.from_time(), "2026-04-26 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(iso_week_interval.to_time(), "2026-05-03 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week_interval.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// the from week's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the to week's last day is out of range.
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
    /// let from = Date::from_ymd_opt(2026, 1, 7).ok_or(DateFromYmdError)?.iso_week();
    /// let to = Date::from_ymd_opt(2026, 3, 17).ok_or(DateFromYmdError)?.iso_week();
    ///
    /// let interval = BoundedAbsoluteInterval::from_inclusive_iso_week_range(from, to, offset_tz)?;
    ///
    /// assert_eq!(interval.from_time(), "2026-01-04 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.to_time(), "2026-03-22 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_iso_week_range(
        mut from: IsoWeek,
        mut to: IsoWeek,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if from.year() > to.year() || (from.year() == to.year() && from.week() > to.week()) {
            std::mem::swap(&mut from, &mut to);
        }

        Self::from_inclusive_date_range(
            Date::from_isoywd_opt(from.year(), from.week(), Weekday::Mon)
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            Date::from_isoywd_opt(to.year(), to.week(), Weekday::Sun)
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
    /// assert_eq!(iso_week.from_time(), "2026-01-25 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(iso_week.to_time(), "2026-02-01 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(iso_week.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(week.from_time(), "2026-05-10 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.to_time(), "2026-05-17 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(week.from_time(), "2026-04-12 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(week.to_time(), "2026-04-19 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(week.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(month.from_time(), "2026-04-30 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(month.to_time(), "2026-05-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// the from month's first day is out of range.
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the to month's last day is out of range.
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
    /// assert_eq!(interval.from_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.to_time(), "2026-05-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_month_range(
        mut from: MonthInYear,
        mut to: MonthInYear,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if from > to {
            std::mem::swap(&mut from, &mut to);
        }

        Self::from_inclusive_date_range(
            from.checked_first_day()
                .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?,
            to.checked_last_day()
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
    /// assert_eq!(month.from_time(), "2026-06-30 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(month.to_time(), "2026-07-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(month.from_time(), "2026-02-28 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(month.to_time(), "2026-03-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(month.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(year.from_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(year.to_time(), "2026-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// the first day of `from_year` is out of range.
    ///
    /// Returns [`DateOperationError`](BoundedAbsoluteIntervalCreationError::DateOperationError) if
    /// the first day of `to_year` is out of range (needed in order to determine if the year is a leap year).
    ///
    /// Returns [`OutOfRangeEndDate`](BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate) if
    /// the last day of `to_year` is out of range.
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
    /// assert_eq!(years.from_time(), "2024-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(years.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(years.to_time(), "2030-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(years.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn from_inclusive_year_range(
        mut from_year: i32,
        mut to_year: i32,
        tz: TimeZone,
    ) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        if from_year > to_year {
            std::mem::swap(&mut from_year, &mut to_year);
        }

        let first_day_of_from_year =
            Date::from_yo_opt(from_year, 1).ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeStartDate)?;

        let first_day_of_to_year =
            Date::from_yo_opt(to_year, 1).ok_or(BoundedAbsoluteIntervalCreationError::DateOperationError)?;

        let last_day_of_to_year = Date::from_yo_opt(
            to_year,
            if first_day_of_to_year.leap_year() {
                u32::from(DAYS_IN_LEAP_YEAR)
            } else {
                u32::from(DAYS_IN_COMMON_YEAR)
            },
        )
        .ok_or(BoundedAbsoluteIntervalCreationError::OutOfRangeEndDate)?;

        Self::from_inclusive_date_range(first_day_of_from_year, last_day_of_to_year, tz)
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
    /// assert_eq!(year.from_time(), "2026-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(year.to_time(), "2027-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// assert_eq!(year.from_time(), "2024-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(year.to_time(), "2025-12-31 22:00:00Z".parse::<Timestamp>()?);
    /// assert_eq!(year.to_inclusivity(), BoundInclusivity::Exclusive);
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
    /// let year = BoundedAbsoluteInterval::previous_year(offset_tz)?;
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn previous_year(tz: TimeZone) -> Result<Self, BoundedAbsoluteIntervalCreationError> {
        Self::year_before_naive_duration_from_today(CalendarAnchorOffset::Years(1), tz)
    }

    /// Returns the start time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_inclusivity = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// assert_eq!(bounded_inclusivity.from_time(), from_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn from_time(&self) -> Timestamp {
        self.from
    }

    /// Returns the end time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_inclusivity = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// assert_eq!(bounded_inclusivity.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn to_time(&self) -> Timestamp {
        self.to
    }

    /// Returns the inclusivity of the start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     from_time,
    ///     BoundInclusivity::Exclusive,
    ///     to_time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn from_inclusivity(&self) -> BoundInclusivity {
        self.from_inclusivity
    }

    /// Returns the inclusivity of the end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let bounded_interval = BoundedAbsoluteInterval::new_with_inclusivity(
    ///     from_time,
    ///     BoundInclusivity::Exclusive,
    ///     to_time,
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn to_inclusivity(&self) -> BoundInclusivity {
        self.to_inclusivity
    }

    /// Sets the from time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New from is not in chronological order
    /// let new_from_time = "2025-01-01 17:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.unchecked_set_from(new_from_time);
    ///
    /// // And yet is stays that way
    /// assert_eq!(bounded_interval.from_time(), new_from_time);
    /// assert_eq!(bounded_interval.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_from(&mut self, new_from: Timestamp) {
        self.from = new_from;
    }

    /// Sets the to time without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New to is not in chronological order
    /// let new_to_time = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    ///
    /// bounded_interval.unchecked_set_to(new_to_time);
    ///
    /// // And yet is stays that way
    /// assert_eq!(bounded_interval.from_time(), from_time);
    /// assert_eq!(bounded_interval.to_time(), new_to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_to(&mut self, new_to: Timestamp) {
        self.to = new_to;
    }

    /// Sets the from time
    ///
    /// Returns whether the operation was successful and the from time modified.
    /// If the given new from time violates the invariants, the method simply returns `false`
    /// without changing the from time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New from is not in chronological order
    /// let new_from_time = "2025-01-01 17:00:00Z".parse::<Timestamp>()?;
    ///
    /// let was_successful = bounded_interval.set_from(new_from_time);
    ///
    /// // Therefore gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.from_time(), from_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_from(&mut self, new_from: Timestamp) -> bool {
        match new_from.cmp(&self.to) {
            Ordering::Less => {
                self.unchecked_set_from(new_from);
                true
            },
            Ordering::Equal => {
                if self.from_inclusivity != BoundInclusivity::Inclusive
                    || self.to_inclusivity != BoundInclusivity::Inclusive
                {
                    return false;
                }

                self.unchecked_set_from(new_from);
                true
            },
            Ordering::Greater => false,
        }
    }

    /// Sets the to time
    ///
    /// Returns whether the operation was successful and the to time modified.
    /// If the given new to time violates the invariants, the method simply returns `false`
    /// without changing the to time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let from_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let to_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(from_time, to_time);
    ///
    /// // New to is not in chronological order
    /// let new_to_time = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    ///
    /// let was_successful = bounded_interval.set_to(new_to_time);
    ///
    /// // Therefore gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.to_time(), to_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_to(&mut self, new_to: Timestamp) -> bool {
        match self.from.cmp(&new_to) {
            Ordering::Less => {
                self.unchecked_set_to(new_to);
                true
            },
            Ordering::Equal => {
                if self.from_inclusivity != BoundInclusivity::Inclusive
                    || self.to_inclusivity != BoundInclusivity::Inclusive
                {
                    return false;
                }

                self.unchecked_set_to(new_to);
                true
            },
            Ordering::Greater => false,
        }
    }

    /// Sets the inclusivity of the start bound
    ///
    /// Returns whether the operation was successful and the start bound's inclusivity modified.
    /// If the given new start bound inclusivity violates the invariants, the method simply returns `false`
    /// without changing the start bound's inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(time, time);
    ///
    /// // Interval has same times, therefore cannot be other than doubly inclusive
    /// let was_successful = bounded_interval.set_from_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Therefore new inclusivity gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.from == self.to && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.from_inclusivity = new_inclusivity;
        true
    }

    /// Sets the inclusivity of the end bound
    ///
    /// Returns whether the operation was successful and the end bound's inclusivity modified.
    /// If the given new end bound inclusivity violates the invariants, the method simply returns `false`
    /// without changing the end bound's inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut bounded_interval = BoundedAbsoluteInterval::new(time, time);
    ///
    /// // Interval has same times, therefore cannot be other than doubly inclusive
    /// let was_successful = bounded_interval.set_to_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Therefore new inclusivity gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Inclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.from == self.to && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.to_inclusivity = new_inclusivity;
        true
    }
}

/// Errors that can occur when creating a new [`BoundedAbsoluteInterval`]
///
/// Those errors are mostly created by convenience methods, such as [`BoundedAbsoluteInterval::today`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalCreationError {
    /// Start date could not be created as it was out of range
    OutOfRangeStartDate,
    /// End date could not be created as it was out of range
    OutOfRangeEndDate,
    /// Start time could not be created as positioned in a time gap
    ///
    /// Time gaps are often created by daylight savings time (DST), where a given duration can be skipped,
    /// therefore creating either a fold or a gap in time.
    StartInTimeGap,
    /// End time could not be created as positioned in a time gap
    ///
    /// Time gaps are often created by daylight savings time (DST), where a given duration can be skipped,
    /// therefore creating either a fold or a gap in time.
    EndInTimeGap,
    /// Something went wrong when computing a date
    ///
    /// This does not mean that the resulting date was out of range, but rather that something failed
    /// in the process of calculating a date.
    ///
    /// An example would be subtracting a large value from a date's year (`chrono` stores years in [`i32`]):
    /// Removing `i64::from(i32::MAX + 10)` from [`i32::MAX`] can be represented by an [`i32`],
    /// but the computation may use `.checked_sub(i32::try_from(x))`, which would fail as `i64::from(i32::MAX + 10)`
    /// cannot be stored in an [`i32`].
    DateOperationError,
}

impl Display for BoundedAbsoluteIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeStartDate => write!(f, "Start date could not be created as it was out of range"),
            Self::OutOfRangeEndDate => write!(f, "End date could not be created as it was out of range"),
            Self::StartInTimeGap => write!(f, "Start time could not be created as positioned in a time gap"),
            Self::EndInTimeGap => write!(f, "End time could not be created as positioned in a time gap"),
            Self::DateOperationError => write!(f, "Something went wrong when computing a date"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalCreationError {}

impl Interval for BoundedAbsoluteInterval {}

impl HasOpenness for BoundedAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::Bounded
    }
}

impl HasRelativity for BoundedAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for BoundedAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(
            self.to - self.from,
            Epsilon::from((self.from_inclusivity(), self.to_inclusivity())),
        )
    }
}

impl HasAbsoluteBounds for BoundedAbsoluteInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::unchecked_new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            self.from,
            self.from_inclusivity,
        ))
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(self.to, self.to_inclusivity))
    }
}

impl From<(Timestamp, Timestamp)> for BoundedAbsoluteInterval {
    fn from((from, to): (Timestamp, Timestamp)) -> Self {
        BoundedAbsoluteInterval::new(from, to)
    }
}

impl From<((Timestamp, BoundInclusivity), (Timestamp, BoundInclusivity))> for BoundedAbsoluteInterval {
    fn from(
        ((from, from_inclusivity), (to, to_inclusivity)): (
            (Timestamp, BoundInclusivity),
            (Timestamp, BoundInclusivity),
        ),
    ) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity)
    }
}

/// Converts `((Timestamp, bool), (Timestamp, bool))` into [`BoundedAbsoluteInterval`]
///
/// The booleans in the original structure are to be interpreted as _is it inclusive?_
impl From<((Timestamp, bool), (Timestamp, bool))> for BoundedAbsoluteInterval {
    fn from(
        ((from, is_from_inclusive), (to, is_to_inclusive)): ((Timestamp, bool), (Timestamp, bool)),
    ) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            from,
            BoundInclusivity::from(is_from_inclusive),
            to,
            BoundInclusivity::from(is_to_inclusive),
        )
    }
}

impl From<Range<Timestamp>> for BoundedAbsoluteInterval {
    fn from(range: Range<Timestamp>) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<Timestamp>> for BoundedAbsoluteInterval {
    fn from(range: RangeInclusive<Timestamp>) -> Self {
        BoundedAbsoluteInterval::new_with_inclusivity(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

/// Errors that can occur when trying to convert [`AbsoluteBounds`] into [`BoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalFromAbsoluteBoundsError {
    NotBoundedInterval,
}

impl Display for BoundedAbsoluteIntervalFromAbsoluteBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotBoundedInterval => write!(f, "Not a bounded interval"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalFromAbsoluteBoundsError {}

impl TryFrom<AbsoluteBounds> for BoundedAbsoluteInterval {
    type Error = BoundedAbsoluteIntervalFromAbsoluteBoundsError;

    fn try_from(value: AbsoluteBounds) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
                Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity(),
                    finite_end.time(),
                    finite_end.inclusivity(),
                ))
            },
            _ => Err(Self::Error::NotBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`AbsoluteInterval`] into [`BoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedAbsoluteIntervalFromAbsoluteIntervalError {
    WrongVariant,
}

impl Display for BoundedAbsoluteIntervalFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for BoundedAbsoluteIntervalFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for BoundedAbsoluteInterval {
    type Error = BoundedAbsoluteIntervalFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Bounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

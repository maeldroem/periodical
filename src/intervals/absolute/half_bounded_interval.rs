
/// A half-bounded absolute interval
///
/// An interval with a set reference time and an [opening direction](OpeningDirection).
/// Like all specific absolute interval types, it conserves the invariant of its bounds being
/// in chronological order[^chrono_order_invariant] and if the interval has a length of zero,
/// they must be inclusive[^doubly_inclusive_invariant].
///
/// However, like the other specific interval types, it conserves an additional invariant:
/// Its [openness](Openness) cannot change. That is to say a half-bounded interval must remain a half-bounded interval.
/// It cannot mutate from being a half-bounded interval to a bounded interval.
///
/// [^chrono_order_invariant]: This invariant is automatically guaranteed in this structure
///     since it only has one bound.
/// [^doubly_inclusive_invariant]: This invariant is automatically guaranteed in this structure
///     since the reference time is finite and therefore cannot reach the opposite end of the half-bounded interval,
///     since the opposite end is infinite.
///
/// Instead, if you are looking for an absolute interval that doesn't keep the [openness](Openness) invariant,
/// see [`AbsoluteBounds`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct HalfBoundedAbsoluteInterval {
    reference_time: Timestamp,
    opening_direction: OpeningDirection,
    reference_inclusivity: BoundInclusivity,
}

impl HalfBoundedAbsoluteInterval {
    /// Creates a new [`HalfBoundedAbsoluteInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new(reference_time: Timestamp, opening_direction: OpeningDirection) -> Self {
        HalfBoundedAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] with the given bound inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        reference_time: Timestamp,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfBoundedAbsoluteInterval {
            reference_time,
            opening_direction,
            reference_inclusivity: reference_time_inclusivity,
        }
    }

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
    pub fn since_date(naive_date: Date, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let reference_time = naive_date
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
    pub fn until_date(naive_date: Date, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let reference_time = naive_date
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
        Self::since_date(naive_date_today(&tz), tz)
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
        Self::until_date(naive_date_today(&tz), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since tomorrow in the given timezone
    ///
    /// See [`since_date`](HalfBoundedAbsoluteInterval::since_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReferenceDate`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReferenceDate) if
    /// [`checked_add_naive_duration_to_naive_date`] returns [`None`].
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
            checked_add_naive_duration_to_naive_date(naive_date_today(&tz), CalendarAnchorOffset::Days(1))
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
    /// [`checked_add_naive_duration_to_naive_date`] returns [`None`].
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
            checked_add_naive_duration_to_naive_date(naive_date_today(&tz), CalendarAnchorOffset::Days(1))
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
    /// [`checked_sub_naive_duration_to_naive_date`] returns [`None`].
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
            checked_sub_naive_duration_to_naive_date(naive_date_today(&tz), CalendarAnchorOffset::Days(1))
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
    /// [`checked_sub_naive_duration_to_naive_date`] returns [`None`].
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
            checked_sub_naive_duration_to_naive_date(naive_date_today(&tz), CalendarAnchorOffset::Days(1))
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
        Self::since_week(naive_date_today(&tz).week(week_start), tz)
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
        Self::until_week(naive_date_today(&tz).week(week_start), tz)
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
        Self::since_iso_week(naive_date_today(&tz).iso_week(), tz)
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
        Self::until_iso_week(naive_date_today(&tz).iso_week(), tz)
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
            MonthInYear::try_from(naive_date_today(&tz))
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
            MonthInYear::try_from(naive_date_today(&tz))
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
        Self::since_year(naive_date_today(&tz).year(), tz)
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
        Self::until_year(naive_date_today(&tz).year(), tz)
    }

    /// Returns the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), ref_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn reference_time(&self) -> Timestamp {
        self.reference_time
    }

    /// Returns the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference time
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
    ///     ref_time,
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference_inclusivity
    }

    /// Sets the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// let new_ref_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// half_bounded_interval.set_reference_time(new_ref_time);
    ///
    /// assert_eq!(half_bounded_interval.reference_time(), new_ref_time);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_reference_time(&mut self, new_reference_time: Timestamp) {
        self.reference_time = new_reference_time;
    }

    /// Sets the inclusivity of the reference time
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded_interval.set_reference_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_reference_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_inclusivity = new_inclusivity;
    }

    /// Sets the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let ref_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     ref_time,
    ///     OpeningDirection::ToFuture,
    /// );
    ///
    /// half_bounded_interval.set_opening_direction(OpeningDirection::ToPast);
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        self.opening_direction = new_opening_direction;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalCreationError {
    /// Reference date could not be created as it was out of range
    OutOfRangeReferenceDate,
    /// Reference time could not be created as positioned in a time gap
    ///
    /// Time gaps are often created by daylight savings time (DST), where a given duration can be skipped,
    /// therefore creating either a fold or a gap in time.
    ReferenceTimeInTimeGap,
    /// Something went wrong when computing a date
    ///
    /// This does not mean that the resulting date was out of range, but rather that something failed
    /// in the process of calculating a date.
    DateOperationError,
}

impl Display for HalfBoundedAbsoluteIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeReferenceDate => write!(f, "Reference date could not be created as it was out of range"),
            Self::ReferenceTimeInTimeGap => {
                write!(f, "Reference time could not be created as positioned in a time gap")
            },
            Self::DateOperationError => write!(f, "Something went wrong when computing a date"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalCreationError {}

impl Interval for HalfBoundedAbsoluteInterval {}

impl HasOpenness for HalfBoundedAbsoluteInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedAbsoluteInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl HasDuration for HalfBoundedAbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasAbsoluteBounds for HalfBoundedAbsoluteInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteStartBound::InfinitePast,
            OpeningDirection::ToFuture => AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                self.reference_time,
                self.reference_inclusivity,
            )),
        }
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        match self.opening_direction {
            OpeningDirection::ToPast => AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                self.reference_time,
                self.reference_inclusivity,
            )),
            OpeningDirection::ToFuture => AbsoluteEndBound::InfiniteFuture,
        }
    }
}

impl From<(Timestamp, OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from((time, direction): (Timestamp, OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new(time, direction)
    }
}

/// Converts `(Timestamp, bool)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean is interpreted as _is it going to future?_
impl From<(Timestamp, bool)> for HalfBoundedAbsoluteInterval {
    fn from((time, goes_to_future): (Timestamp, bool)) -> Self {
        HalfBoundedAbsoluteInterval::new(time, OpeningDirection::from(goes_to_future))
    }
}

impl From<((Timestamp, BoundInclusivity), OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from(((time, inclusivity), direction): ((Timestamp, BoundInclusivity), OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(time, inclusivity, direction)
    }
}

/// Converts `((Timestamp, BoundInclusivity), bool)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean is interpreted as _is it going to future?_
impl From<((Timestamp, BoundInclusivity), bool)> for HalfBoundedAbsoluteInterval {
    fn from(((time, inclusivity), goes_to_future): ((Timestamp, BoundInclusivity), bool)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(time, inclusivity, OpeningDirection::from(goes_to_future))
    }
}

/// Converts `((Timestamp, bool), OpeningDirection)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean is interpreted as _is it inclusive?_
impl From<((Timestamp, bool), OpeningDirection)> for HalfBoundedAbsoluteInterval {
    fn from(((time, is_inclusive), direction): ((Timestamp, bool), OpeningDirection)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(time, BoundInclusivity::from(is_inclusive), direction)
    }
}

/// Converts `((Timestamp, bool), bool)` into [`HalfBoundedAbsoluteInterval`]
///
/// The boolean of the first tuple element is interpreted as _is it inclusive?_
///
/// The boolean of the second tuple element is interpreted as _is it going to future?_
impl From<((Timestamp, bool), bool)> for HalfBoundedAbsoluteInterval {
    fn from(((time, is_inclusive), goes_to_future): ((Timestamp, bool), bool)) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            time,
            BoundInclusivity::from(is_inclusive),
            OpeningDirection::from(goes_to_future),
        )
    }
}

impl From<RangeFrom<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeFrom<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeTo<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<Timestamp>> for HalfBoundedAbsoluteInterval {
    fn from(range: RangeToInclusive<Timestamp>) -> Self {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

/// Errors that can occur when trying to convert [`AbsoluteBounds`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError {
    NotHalfBoundedInterval,
}

impl Display for HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotHalfBoundedInterval => write!(f, "Not a half-bounded interval"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError {}

impl TryFrom<AbsoluteBounds> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalFromAbsoluteBoundsError;

    fn try_from(value: AbsoluteBounds) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(finite_end)) => {
                Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    finite_end.time(),
                    finite_end.inclusivity(),
                    OpeningDirection::ToPast,
                ))
            },
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::InfiniteFuture) => {
                Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity(),
                    OpeningDirection::ToFuture,
                ))
            },
            _ => Err(Self::Error::NotHalfBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`AbsoluteInterval`] into [`HalfBoundedAbsoluteInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {
    WrongVariant,
}

impl Display for HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for HalfBoundedAbsoluteInterval {
    type Error = HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::HalfBounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

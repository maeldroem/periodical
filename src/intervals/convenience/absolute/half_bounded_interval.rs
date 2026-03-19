//! Convenience methods for [`HalfBoundedAbsoluteInterval`]

use jiff::Timestamp;
use jiff::civil::Date;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{HalfBoundedAbsoluteInterval, HalfBoundedAbsoluteIntervalCreationError};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::time::{CalendarAnchorOffset, CalendarAnchorOffsetDateError, MonthInYear, OffsetIsoWeek, checked_add_calendar_anchor_offset_to_date, checked_sub_calendar_anchor_offset_to_date, date_today};

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
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference)
    /// if [`Date::to_zoned`] returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let from_first_of_may = HalfBoundedAbsoluteInterval::since_date(
    ///     "2026-05-01".parse::<Date>()?,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     from_first_of_may.reference(),
    ///     "2026-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(from_first_of_may.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(from_first_of_may.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_date(date: Date, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let reference = date
            .to_zoned(tz)
            .or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?
            .timestamp();

        Ok(Self::new(reference, OpeningDirection::ToFuture))
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the start of the given day in the given timezone
    ///
    /// The end of the resulting interval is [exclusive](BoundInclusivity::Exclusive).
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference)
    /// if [`Date::to_zoned`] returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::civil::Date;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let until_first_of_may = HalfBoundedAbsoluteInterval::until_date(
    ///     "2026-05-01".parse::<Date>()?,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     until_first_of_may.reference(),
    ///     "2026-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(until_first_of_may.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(until_first_of_may.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_date(date: Date, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let reference = date
            .to_zoned(tz)
            .or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?
            .timestamp();

        Ok(Self::new_with_inclusivity(
            reference,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ))
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that [`since_date`](HalfBoundedAbsoluteInterval::since_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let since_today = HalfBoundedAbsoluteInterval::since_today(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_today(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(date_today(tz.clone()), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until today in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that [`until_date`](HalfBoundedAbsoluteInterval::until_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let until_today = HalfBoundedAbsoluteInterval::until_today(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_today(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(date_today(tz.clone()), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since tomorrow in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](HalfBoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    /// 
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`since_date`](HalfBoundedAbsoluteInterval::since_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let since_tomorrow = HalfBoundedAbsoluteInterval::since_tomorrow(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_tomorrow(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let date = checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(1), date_today(tz.clone()))
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => {
                    HalfBoundedAbsoluteIntervalCreationError::ComputationError
                },
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference
                },
            })?;

        Self::since_date(date, tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until tomorrow in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](HalfBoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    /// 
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference)
    /// if [`checked_add_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`until_date`](HalfBoundedAbsoluteInterval::until_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let until_tomorrow = HalfBoundedAbsoluteInterval::until_tomorrow(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_tomorrow(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let date = checked_add_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(1), date_today(tz.clone()))
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => {
                    HalfBoundedAbsoluteIntervalCreationError::ComputationError
                },
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference
                },
            })?;

        Self::until_date(date, tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since yesterday in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](HalfBoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    /// 
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`since_date`](HalfBoundedAbsoluteInterval::since_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let since_yesterday = HalfBoundedAbsoluteInterval::since_yesterday(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_yesterday(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let date = checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(1), date_today(tz.clone()))
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => {
                    HalfBoundedAbsoluteIntervalCreationError::ComputationError
                },
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference
                },
            })?;
        
        Self::since_date(date, tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until yesterday in the given timezone
    ///
    /// See [`until_date`](HalfBoundedAbsoluteInterval::until_date) for more details.
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](HalfBoundedAbsoluteIntervalCreationError::ComputationError)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge).
    /// 
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference)
    /// if [`checked_sub_calendar_anchor_offset_to_date`]
    /// returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult).
    ///
    /// Returns any error that [`until_date`](HalfBoundedAbsoluteInterval::until_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let until_yesterday = HalfBoundedAbsoluteInterval::until_yesterday(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_yesterday(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        let date = checked_sub_calendar_anchor_offset_to_date(CalendarAnchorOffset::Days(1), date_today(tz.clone()))
            .map_err(|err| match err {
                CalendarAnchorOffsetDateError::OffsetTooLarge => {
                    HalfBoundedAbsoluteIntervalCreationError::ComputationError
                },
                CalendarAnchorOffsetDateError::OutOfRangeResult => {
                    HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference
                },
            })?;
        
        Self::until_date(date, tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the given [`OffsetIsoWeek`]
    /// in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference) if
    /// the week's first day is out of range.
    ///
    /// Returns any error that [`since_date`](HalfBoundedAbsoluteInterval::since_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::time::OffsetIsoWeek;
    /// let interval = HalfBoundedAbsoluteInterval::since_week(
    ///     OffsetIsoWeek::new(5, 2026)?,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.reference(),
    ///     "2026-01-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_week(week: OffsetIsoWeek, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            week.first_day().or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the given week in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference) if
    /// the week's first day is out of range.
    ///
    /// Returns any error that [`until_date`](HalfBoundedAbsoluteInterval::until_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::time::OffsetIsoWeek;
    /// let interval = HalfBoundedAbsoluteInterval::until_week(
    ///     OffsetIsoWeek::new(5, 2026)?,
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     interval.reference(),
    ///     "2026-01-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_week(week: OffsetIsoWeek, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            week.first_day().or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the given month in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference) if
    /// the month's first day is out of range.
    ///
    /// Returns any error that [`since_date`](HalfBoundedAbsoluteInterval::since_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::time::Month;
    /// let since_month = HalfBoundedAbsoluteInterval::since_month(
    ///     Month::March.with_year(2026),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     since_month.reference(),
    ///     "2026-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(since_month.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(since_month.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_month(month: MonthInYear, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            month.first_day().or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the given month in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference) if
    /// the month's first day is out of range.
    ///
    /// Returns any error that [`until_date`](HalfBoundedAbsoluteInterval::until_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::time::Month;
    /// let until_month = HalfBoundedAbsoluteInterval::until_month(
    ///     Month::March.with_year(2026),
    ///     TimeZone::get("Europe/Oslo")?,
    /// )?;
    ///
    /// assert_eq!(
    ///     until_month.reference(),
    ///     "2026-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(until_month.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(until_month.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_month(month: MonthInYear, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            month.first_day().or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the current month in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](HalfBoundedAbsoluteIntervalCreationError::ComputationError) if
    /// the corresponding [`MonthInYear`] could not be determined.
    ///
    /// Returns any error that [`since_month`](HalfBoundedAbsoluteInterval::since_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let since_this_month = HalfBoundedAbsoluteInterval::since_this_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_this_month(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_month(
            MonthInYear::try_from(date_today(tz.clone()))
                .or(Err(HalfBoundedAbsoluteIntervalCreationError::ComputationError))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the current month in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`ComputationError`](HalfBoundedAbsoluteIntervalCreationError::ComputationError) if
    /// the corresponding [`MonthInYear`] could not be determined.
    ///
    /// Returns any error that [`until_month`](HalfBoundedAbsoluteInterval::until_month) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let until_this_month = HalfBoundedAbsoluteInterval::until_this_month(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_this_month(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_month(
            MonthInYear::try_from(date_today(tz.clone()))
                .or(Err(HalfBoundedAbsoluteIntervalCreationError::ComputationError))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the given year in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference) if
    /// the year is out of range.
    ///
    /// Returns any error that [`since_date`](HalfBoundedAbsoluteInterval::since_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let since_year = HalfBoundedAbsoluteInterval::since_year(2026, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     since_year.reference(),
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(since_year.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(since_year.opening_direction(), OpeningDirection::ToFuture);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_year(year: i16, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_date(
            Date::new(year, 1, 1).or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the given year in the given timezone
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeReference`](HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference) if
    /// the year is out of range.
    ///
    /// Returns any error that [`until_date`](HalfBoundedAbsoluteInterval::until_date) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// let until_year = HalfBoundedAbsoluteInterval::until_year(2026, TimeZone::get("Europe/Oslo")?)?;
    ///
    /// assert_eq!(
    ///     until_year.reference(),
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// assert_eq!(until_year.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(until_year.opening_direction(), OpeningDirection::ToPast);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_year(year: i16, tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_date(
            Date::new(year, 1, 1).or(Err(HalfBoundedAbsoluteIntervalCreationError::OutOfRangeReference))?,
            tz,
        )
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans since the current year in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that [`since_year`](HalfBoundedAbsoluteInterval::since_year) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let since_this_year = HalfBoundedAbsoluteInterval::since_this_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn since_this_year(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::since_year(date_today(tz.clone()).year(), tz)
    }

    /// Creates a new [`HalfBoundedAbsoluteInterval`] that spans until the current year in the given timezone
    ///
    /// # Errors
    ///
    /// Returns any error that [`until_year`](HalfBoundedAbsoluteInterval::until_year) may return.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// let until_this_year = HalfBoundedAbsoluteInterval::until_this_year(TimeZone::get("Europe/Oslo")?)?;
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn until_this_year(tz: TimeZone) -> Result<Self, HalfBoundedAbsoluteIntervalCreationError> {
        Self::until_year(date_today(tz.clone()).year(), tz)
    }
}

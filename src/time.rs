//! Time-related values and structures
//!
//! This module contains constants referring to various time-related data such
//! as days in a week, the number of ISO weeks in a _long year_, etc.
//!
//! It also contains structures to represent [offset ISO weeks](OffsetIsoWeek),
//! [individual months](Month), [a month within a year](MonthInYear), but also
//! [calendar anchor offsets](CalendarAnchorOffset), which is used for
//! representing _naive_ durations anchored to their calendar unit (e.g. ISO
//! week, month).

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use jiff::civil::{Date, ISOWeekDate, Weekday};
use jiff::tz::TimeZone;
use jiff::{Error as JiffError, Span, Timestamp};

/// Number of days in a week
///
/// A _week_ here is interpreted as a duration.
///
/// _Anchored_ ISO weeks and traditionally-numbered weeks may contain different
/// amounts of days.
pub const DAYS_IN_WEEK: u8 = 7;

/// Amount of ISO weeks in a short year
///
/// Minimum amount of ISO weeks in a year
pub const ISO_WEEKS_IN_SHORT_YEAR: u8 = 52;

/// Amount of ISO weeks in a long year
///
/// Maximum amount of ISO weeks in a year
pub const ISO_WEEKS_IN_LONG_YEAR: u8 = 53;

/// Number of months in a year
///
/// Per the Gregorian calendar.
/// [Other calendars](https://en.wikipedia.org/w/index.php?title=Month&oldid=1344356659#Months_in_various_calendars)
/// may use other amounts of months.
pub const MONTHS_IN_YEAR: u8 = 12;

/// Number of days in a common year
///
/// Per Gregorian calendar. A common year is a non-leap year.
pub const DAYS_IN_COMMON_YEAR: u16 = 365;

/// Number of days in a leap year
///
/// Per Gregorian calendar.
pub const DAYS_IN_LEAP_YEAR: u16 = 366;

/// Gets today's [`Date`] in the given [`TimeZone`]
///
/// # Panics
///
/// Panics if [`Timestamp::now`] panics.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::tz::TimeZone;
/// # use periodical::time::date_today;
/// let today_date = date_today(TimeZone::get("Europe/Oslo")?);
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[must_use]
pub fn date_today(tz: TimeZone) -> Date {
    Timestamp::now().to_zoned(tz).date()
}

/// Returns the number of ISO weeks in a given year
///
/// # Errors
///
/// If the year is out of range, the corresponding [`Error`](JiffError) is
/// returned.
///
/// # Examples
///
/// ```
/// # use jiff::Error as JiffError;
/// # use periodical::time::{ISO_WEEKS_IN_LONG_YEAR, ISO_WEEKS_IN_SHORT_YEAR, iso_weeks_in_year};
/// assert_eq!(iso_weeks_in_year(2025)?, ISO_WEEKS_IN_SHORT_YEAR); // 52
/// assert_eq!(iso_weeks_in_year(2026)?, ISO_WEEKS_IN_LONG_YEAR); // 53
/// # Ok::<(), JiffError>(())
/// ```
pub fn iso_weeks_in_year(year: i16) -> Result<u8, JiffError> {
    let start_of_year = Date::new(year, 1, 1)?;

    // https://en.wikipedia.org/w/index.php?title=ISO_week_date&oldid=1345029647#Weeks_per_year
    let is_long_year = start_of_year.weekday() == Weekday::Thursday
        || (start_of_year.in_leap_year() && start_of_year.weekday() == Weekday::Wednesday);

    if is_long_year {
        Ok(ISO_WEEKS_IN_LONG_YEAR)
    } else {
        Ok(ISO_WEEKS_IN_SHORT_YEAR)
    }
}

/// An offset ISO week
///
/// Represents an ISO week with an offset in the range of `-6..=6`.
///
/// This structure is particularly useful for representing whole ISO weeks in
/// general, but also useful for representing weeks starting on weekdays other
/// than monday.
///
/// This avoids the use of traditional week numbering, which varies wildly
/// across regions and may introduce weeks that are less than 7 days long.
///
/// If one wishes to keep the ISO week numbering system but have weeks starting
/// on sunday, one can create an [`OffsetIsoWeek`] with an offset of `-1`
/// (Monday = `0`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OffsetIsoWeek {
    week: u8,
    year: i16,
    week_start_offset: i8,
}

impl OffsetIsoWeek {
    /// No week start offset
    ///
    /// With this offset (or lack thereof), an [`OffsetIsoWeek`] becomes
    /// equivalent to a regular ISO week.
    pub const ISO_OFFSET: i8 = 0;

    /// Creates a new [`OffsetIsoWeek`] without an offset
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeYear`](OffsetIsoWeekCreationError::OutOfRangeYear)
    /// if the given year is out of the range that [`Date`] can support.
    ///
    /// Returns [`OutOfRangeWeek`](OffsetIsoWeekCreationError::OutOfRangeWeek)
    /// if the given week is 0 or is greater than the amount of ISO weeks
    /// that year.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::time::{OffsetIsoWeek, OffsetIsoWeekCreationError};
    /// let first_iso_week_of_2026 = OffsetIsoWeek::new(1, 2026)?;
    /// # Ok::<(), OffsetIsoWeekCreationError>(())
    /// ```
    pub fn new(week: u8, year: i16) -> Result<Self, OffsetIsoWeekCreationError> {
        Self::new_with_offset(week, year, Self::ISO_OFFSET)
    }

    /// Creates a new [`OffsetIsoWeek`] with the given week start offset
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeYear`](OffsetIsoWeekCreationError::OutOfRangeYear)
    /// if the given year is out of the range that [`Date`] can support.
    ///
    /// Returns [`OutOfRangeWeek`](OffsetIsoWeekCreationError::OutOfRangeWeek)
    /// if the given week is 0 or is greater than the amount of ISO weeks
    /// that year.
    ///
    /// Returns [`OutOfRangeOffset`](OffsetIsoWeekCreationError::OutOfRangeOffset) if the given offset
    /// is less than `-6` or greater than `6`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::time::{OffsetIsoWeek, OffsetIsoWeekCreationError};
    /// let first_iso_week_on_sunday_of_2026 = OffsetIsoWeek::new_with_offset(1, 2026, -1)?;
    /// # Ok::<(), OffsetIsoWeekCreationError>(())
    /// ```
    pub fn new_with_offset(week: u8, year: i16, week_start_offset: i8) -> Result<Self, OffsetIsoWeekCreationError> {
        let iso_weeks_in_year = iso_weeks_in_year(year).or(Err(OffsetIsoWeekCreationError::OutOfRangeYear))?;

        if !(1..=iso_weeks_in_year).contains(&week) {
            return Err(OffsetIsoWeekCreationError::OutOfRangeWeek);
        }

        if !(-6i8..=6i8).contains(&week_start_offset) {
            return Err(OffsetIsoWeekCreationError::OutOfRangeOffset);
        }

        Ok(OffsetIsoWeek {
            week,
            year,
            week_start_offset,
        })
    }

    /// Returns the week number
    #[must_use]
    pub fn week(&self) -> u8 {
        self.week
    }

    /// Returns the year
    #[must_use]
    pub fn year(&self) -> i16 {
        self.year
    }

    /// Returns the week start offset
    #[must_use]
    pub fn week_start_offset(&self) -> i8 {
        self.week_start_offset
    }

    /// Returns the offset first day of the week
    ///
    /// # Errors
    ///
    /// Returns [`OffsetIsoWeekDateError`] if something went wrong during
    /// computation, usually due to the computation resulting in an
    /// out-of-range date.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::Error as JiffError;
    /// # use jiff::civil::Date;
    /// # use periodical::time::{OffsetIsoWeek, OffsetIsoWeekDateError, OffsetIsoWeekCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     OffsetIsoWeekCreationError(OffsetIsoWeekCreationError),
    /// #     OffsetIsoWeekDateError(OffsetIsoWeekDateError),
    /// #     JiffError(JiffError),
    /// # }
    /// #
    /// # impl From<OffsetIsoWeekCreationError> for ExampleError {
    /// #     fn from(value: OffsetIsoWeekCreationError) -> Self {
    /// #         Self::OffsetIsoWeekCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<OffsetIsoWeekDateError> for ExampleError {
    /// #     fn from(value: OffsetIsoWeekDateError) -> Self {
    /// #         Self::OffsetIsoWeekDateError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<JiffError> for ExampleError {
    /// #     fn from(value: JiffError) -> Self {
    /// #         Self::JiffError(value)
    /// #     }
    /// # }
    /// let first_iso_week_on_sunday_of_2026 = OffsetIsoWeek::new_with_offset(1, 2026, -1)?;
    ///
    /// assert_eq!(first_iso_week_on_sunday_of_2026.first_day()?, "2025-12-28".parse::<Date>()?);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn first_day(&self) -> Result<Date, OffsetIsoWeekDateError> {
        let iso_week_first_day = ISOWeekDate::new(
            self.year(),
            i8::try_from(self.week()).or(Err(OffsetIsoWeekDateError))?,
            Weekday::Monday,
        )
        .or(Err(OffsetIsoWeekDateError))?
        .date();

        iso_week_first_day
            .checked_add(
                Span::new()
                    .try_days(self.week_start_offset())
                    .or(Err(OffsetIsoWeekDateError))?,
            )
            .or(Err(OffsetIsoWeekDateError))
    }

    /// Returns the offset last day of the week
    ///
    /// # Errors
    ///
    /// Returns [`OffsetIsoWeekDateError`] if something went wrong during
    /// computation, usually due to the computation resulting in an
    /// out-of-range date.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::Error as JiffError;
    /// # use jiff::civil::Date;
    /// # use periodical::time::{OffsetIsoWeek, OffsetIsoWeekDateError, OffsetIsoWeekCreationError};
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     OffsetIsoWeekCreationError(OffsetIsoWeekCreationError),
    /// #     OffsetIsoWeekDateError(OffsetIsoWeekDateError),
    /// #     JiffError(JiffError),
    /// # }
    /// #
    /// # impl From<OffsetIsoWeekCreationError> for ExampleError {
    /// #     fn from(value: OffsetIsoWeekCreationError) -> Self {
    /// #         Self::OffsetIsoWeekCreationError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<OffsetIsoWeekDateError> for ExampleError {
    /// #     fn from(value: OffsetIsoWeekDateError) -> Self {
    /// #         Self::OffsetIsoWeekDateError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<JiffError> for ExampleError {
    /// #     fn from(value: JiffError) -> Self {
    /// #         Self::JiffError(value)
    /// #     }
    /// # }
    /// let first_iso_week_on_sunday_of_2026 = OffsetIsoWeek::new_with_offset(1, 2026, -1)?;
    ///
    /// assert_eq!(first_iso_week_on_sunday_of_2026.last_day()?, "2026-01-03".parse::<Date>()?);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn last_day(&self) -> Result<Date, OffsetIsoWeekDateError> {
        let iso_week_last_day = ISOWeekDate::new(
            self.year(),
            i8::try_from(self.week()).or(Err(OffsetIsoWeekDateError))?,
            Weekday::Sunday,
        )
        .or(Err(OffsetIsoWeekDateError))?
        .date();

        iso_week_last_day
            .checked_add(
                Span::new()
                    .try_days(self.week_start_offset())
                    .or(Err(OffsetIsoWeekDateError))?,
            )
            .or(Err(OffsetIsoWeekDateError))
    }
}

/// Errors produced by creation methods of [`OffsetIsoWeek`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OffsetIsoWeekCreationError {
    OutOfRangeYear,
    OutOfRangeWeek,
    OutOfRangeOffset,
}

impl Display for OffsetIsoWeekCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeYear => write!(f, "Out of range year"),
            Self::OutOfRangeWeek => write!(f, "Out of range week number"),
            Self::OutOfRangeOffset => write!(f, "Out of range week start offset"),
        }
    }
}

impl Error for OffsetIsoWeekCreationError {}

/// Error produced by methods attempting to convert an [`OffsetIsoWeek`] to a
/// [`Date`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OffsetIsoWeekDateError;

impl Display for OffsetIsoWeekDateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Conversion of the OffsetIsoWeek to a Date failed")
    }
}

impl Error for OffsetIsoWeekDateError {}

/// An individual month
///
/// Per the Gregorian calendar.
/// [Other calendars](https://en.wikipedia.org/w/index.php?title=Month&oldid=1344356659#Months_in_various_calendars)
/// may use other amounts of months and other names for them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Month {
    January,
    February,
    March,
    April,
    May,
    June,
    July,
    August,
    September,
    October,
    November,
    December,
}

impl Month {
    /// Converts a 0-offset number into a [`Month`]
    ///
    /// # Errors
    ///
    /// Returns [`MonthTryFromNumberError`] if the number is greater than 11.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::time::{Month, MonthTryFromNumberError};
    /// assert_eq!(Month::try_from_zero_offset(5)?, Month::June);
    /// # Ok::<(), MonthTryFromNumberError>(())
    /// ```
    pub fn try_from_zero_offset(x: u8) -> Result<Self, MonthTryFromNumberError> {
        match x {
            0 => Ok(Self::January),
            1 => Ok(Self::February),
            2 => Ok(Self::March),
            3 => Ok(Self::April),
            4 => Ok(Self::May),
            5 => Ok(Self::June),
            6 => Ok(Self::July),
            7 => Ok(Self::August),
            8 => Ok(Self::September),
            9 => Ok(Self::October),
            10 => Ok(Self::November),
            11 => Ok(Self::December),
            _ => Err(MonthTryFromNumberError),
        }
    }

    /// Converts a 1-offset number into a [`Month`]
    ///
    /// # Errors
    ///
    /// Returns [`MonthTryFromNumberError`] if the number is 0 or is greater
    /// than 12.
    ///
    /// ```
    /// # use periodical::time::{Month, MonthTryFromNumberError};
    /// assert_eq!(Month::try_from_one_offset(6)?, Month::June);
    /// # Ok::<(), MonthTryFromNumberError>(())
    /// ```
    pub fn try_from_one_offset(x: u8) -> Result<Self, MonthTryFromNumberError> {
        Self::try_from_zero_offset(x.checked_sub(1).ok_or(MonthTryFromNumberError)?)
    }

    /// Associates a year to the [`Month`]
    ///
    /// Converts the [`Month`] to a [`MonthInYear`], consuming `self` in the
    /// process.
    ///
    /// Equivalent to [`MonthInYear::new`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::time::Month;
    /// let may_2026 = Month::May.with_year(2026);
    ///
    /// assert_eq!(may_2026.month(), Month::May);
    /// assert_eq!(may_2026.year(), 2026);
    /// ```
    #[must_use]
    pub fn with_year(self, year: i16) -> MonthInYear {
        MonthInYear::new(self, year)
    }

    /// Returns the 0-offset number of the [`Month`]
    ///
    /// January is 0, February is 1, and so on.
    #[must_use]
    pub fn zero_offset_number(&self) -> u8 {
        match self {
            Self::January => 0,
            Self::February => 1,
            Self::March => 2,
            Self::April => 3,
            Self::May => 4,
            Self::June => 5,
            Self::July => 6,
            Self::August => 7,
            Self::September => 8,
            Self::October => 9,
            Self::November => 10,
            Self::December => 11,
        }
    }

    /// Returns the 1-offset number of the [`Month`]d
    ///
    /// January is 1, February is 2, and so on.
    #[must_use]
    pub fn one_offset_number(&self) -> u8 {
        self.zero_offset_number().saturating_add(1)
    }
}

impl From<MonthInYear> for Month {
    fn from(value: MonthInYear) -> Self {
        value.month()
    }
}

/// Error produced by conversion methods from a number to a [`Month`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MonthTryFromNumberError;

impl Display for MonthTryFromNumberError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Conversion from a number to a Month failed")
    }
}

impl Error for MonthTryFromNumberError {}

/// A [`Month`] within a year
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MonthInYear {
    year: i16,
    month: Month,
}

impl MonthInYear {
    /// Creates a new [`MonthInYear`] from the given year and month
    #[must_use]
    pub fn new(month: Month, year: i16) -> Self {
        Self {
            year,
            month,
        }
    }

    /// Returns the year
    #[must_use]
    pub fn year(&self) -> i16 {
        self.year
    }

    /// Returns the [`Month`]
    #[must_use]
    pub fn month(&self) -> Month {
        self.month
    }

    /// Returns the first day of this month of the year
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeMonth`](MonthInYearDateError::OutOfRangeMonth) if
    /// conversion of the [1-offset month number](Month::one_offset_number)
    /// fails to be converted to [`i8`], which should reasonably never
    /// happen.
    ///
    /// Returns [`OutOfRangeYear`](MonthInYearDateError::OutOfRangeYear) if the
    /// stored year is out of range for a [`Date`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::Error as JiffError;
    /// # use jiff::civil::Date;
    /// # use periodical::time::{Month, MonthInYear, MonthInYearDateError};
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     MonthInYearDateError(MonthInYearDateError),
    /// #     JiffError(JiffError),
    /// # }
    /// #
    /// # impl From<MonthInYearDateError> for ExampleError {
    /// #     fn from(value: MonthInYearDateError) -> Self {
    /// #         Self::MonthInYearDateError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<JiffError> for ExampleError {
    /// #     fn from(value: JiffError) -> Self {
    /// #         Self::JiffError(value)
    /// #     }
    /// # }
    /// let may_2026 = MonthInYear::new(Month::May, 2026);
    ///
    /// assert_eq!(may_2026.first_day()?, "2026-05-01".parse::<Date>()?);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn first_day(&self) -> Result<Date, MonthInYearDateError> {
        Date::new(
            self.year(),
            i8::try_from(self.month().one_offset_number()).or(Err(MonthInYearDateError::OutOfRangeMonth))?,
            1,
        )
        .or(Err(MonthInYearDateError::OutOfRangeYear))
    }

    /// Returns the last day of this month of the year
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeMonth`](MonthInYearDateError::OutOfRangeMonth) if
    /// conversion of the [1-offset month number](Month::one_offset_number)
    /// fails to be converted to [`i8`], which should reasonably never
    /// happen.
    ///
    /// Returns [`OutOfRangeYear`](MonthInYearDateError::OutOfRangeYear) if the
    /// stored year is out of range for a [`Date`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::Error as JiffError;
    /// # use jiff::civil::Date;
    /// # use periodical::time::{Month, MonthInYear, MonthInYearDateError};
    /// #
    /// # #[derive(Debug)]
    /// # enum ExampleError {
    /// #     MonthInYearDateError(MonthInYearDateError),
    /// #     JiffError(JiffError),
    /// # }
    /// #
    /// # impl From<MonthInYearDateError> for ExampleError {
    /// #     fn from(value: MonthInYearDateError) -> Self {
    /// #         Self::MonthInYearDateError(value)
    /// #     }
    /// # }
    /// #
    /// # impl From<JiffError> for ExampleError {
    /// #     fn from(value: JiffError) -> Self {
    /// #         Self::JiffError(value)
    /// #     }
    /// # }
    /// let may_2026 = MonthInYear::new(Month::May, 2026);
    ///
    /// assert_eq!(may_2026.last_day()?, "2026-05-31".parse::<Date>()?);
    /// # Ok::<(), ExampleError>(())
    /// ```
    pub fn last_day(&self) -> Result<Date, MonthInYearDateError> {
        self.first_day().map(Date::last_of_month)
    }
}

/// Errors produced by methods converting a [`Month`] to a [`Date`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MonthInYearDateError {
    OutOfRangeYear,
    OutOfRangeMonth,
}

impl Display for MonthInYearDateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeYear => write!(f, "Out of range year"),
            Self::OutOfRangeMonth => write!(f, "Out of range month"),
        }
    }
}

impl Error for MonthInYearDateError {}

impl PartialOrd for MonthInYear {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MonthInYear {
    fn cmp(&self, other: &Self) -> Ordering {
        self.year()
            .cmp(&other.year())
            .then_with(|| self.month().cmp(&other.month()))
    }
}

impl TryFrom<Date> for MonthInYear {
    type Error = MonthTryFromNumberError;

    fn try_from(value: Date) -> Result<Self, Self::Error> {
        Ok(MonthInYear::new(
            Month::try_from_one_offset(value.month().unsigned_abs())?,
            value.year(),
        ))
    }
}

/// A calendar anchor offset
///
/// # What is a calendar anchor
///
/// A _calendar anchor_ is any subdivision of the Gregorian calendar, e.g. days,
/// weeks, months, years.
///
/// As other naive units, it is not a precise amount, rather an abstract value
/// that we often use in common speech.
///
/// The goal of this structure is to represent calendar offsets that can be
/// applied to naive structures such as [`Date`s](Date).
///
/// # Why can't calendar anchor offsets be combined in one value?
///
/// The reason [`CalendarAnchorOffset`]s can't be combined into one structure
/// (as in you can't add two instances together) as the order in which they are
/// applied to a naive structure such as [`Date`] matters.
///
/// # How it works
///
/// A calendar anchor offset is very different from how [`Span`]s work, as it
/// interprets calendar offsets by the absolute position of its anchor.
///
/// The _absolute position_ of a calendar anchor is based on where the anchors
/// are placed in the calendar, rather than their actual duration.
/// Therefore, a week is not equal to 7 days, it instead represents "What is the
/// nth week compared to X".
///
/// For example, if we want the month that happens in 2 months when observing
/// the calendar, and the current date is `2026-04-15`, then it would return
/// June of 2026, as if we only observe the month on the calendar, it is the
/// second month that happens from this month (April of 2026).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CalendarAnchorOffset {
    /// N days calendar anchor offset
    Days(i64),
    /// N weeks with custom week start calendar anchor offset
    Weeks(i64, Weekday),
    /// N ISO weeks calendar anchor offset
    ///
    /// Equivalent to [`CalendarAnchorOffset::Weeks`] using
    /// [monday](Weekday::Monday) as the week start.
    IsoWeeks(i64),
    /// N months calendar anchor offset
    Months(i64),
    /// N years calendar anchor offset
    Years(i32),
}

impl CalendarAnchorOffset {
    /// Whether the calendar offset duration is zero
    ///
    /// This does **not** mean that after applying the [`CalendarAnchorOffset`]
    /// to another naive structure will result in the same value as the
    /// original naive structure.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(x, _) | Self::IsoWeeks(x) | Self::Months(x) => *x == 0,
            Self::Years(x) => *x == 0,
        }
    }

    /// Whether the stored naive duration is positive (`> 0`)
    ///
    /// This does **not** mean that after applying the [`CalendarAnchorOffset`]
    /// to another naive structure will result in a value greater than the
    /// original naive structure.
    #[must_use]
    pub fn is_positive(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(x, _) | Self::IsoWeeks(x) | Self::Months(x) => x.is_positive(),
            Self::Years(x) => x.is_positive(),
        }
    }

    /// Whether the stored naive duration is negative (`< 0`)
    ///
    /// This does **not** mean that after applying the [`CalendarAnchorOffset`]
    /// to another naive structure will result in a value less than the
    /// original naive structure.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(x, _) | Self::IsoWeeks(x) | Self::Months(x) => x.is_negative(),
            Self::Years(x) => x.is_negative(),
        }
    }
}

impl PartialOrd for CalendarAnchorOffset {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Days(x), Self::Days(y))
            | (Self::Weeks(x, _), Self::Weeks(y, _))
            | (Self::Months(x), Self::Months(y)) => Some(x.cmp(y)),
            (Self::Years(x), Self::Years(y)) => Some(x.cmp(y)),
            _ => None,
        }
    }
}

/// Checked addition of a calendar week offset to a [`Date`]
///
/// This operations results in a [`Date`] on the start of the week, regardless
/// of the week offset.
///
/// This means that if you provide a week offset of `1` with a week start on
/// [monday](Weekday::Monday), and the given date is `2026-03-01` (a sunday),
/// the resulting date will be `2026-03-02`, as it is the first day of the next
/// week compared to the given date's week.
///
/// This method is mostly used by
/// [`checked_add_calendar_anchor_offset_to_date`].
///
/// # Errors
///
/// Returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge) if
/// the provided week offset cannot fit in a [`Span`].
///
/// Returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult) if the computed result
/// is out of range for a [`Date`].
///
/// # Examples
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::{Date, Weekday};
/// # use periodical::time::{CalendarAnchorOffsetDateError, checked_add_calendar_week_offset_to_date};
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         Self::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         Self::JiffError(value)
/// #     }
/// # }
/// let date = "2026-03-04".parse::<Date>()?;
///
/// assert_eq!(
///     checked_add_calendar_week_offset_to_date(2, Weekday::Sunday, date)?,
///     "2026-03-15".parse::<Date>()?,
/// );
/// assert_eq!(
///     checked_add_calendar_week_offset_to_date(-2, Weekday::Sunday, date)?,
///     "2026-02-15".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
pub fn checked_add_calendar_week_offset_to_date(
    weeks_offset: i64,
    week_start: Weekday,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    date.checked_sub(Span::new().days(week_start.until(date.weekday())))
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
        .checked_add(
            Span::new()
                .try_weeks(weeks_offset)
                .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
        )
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))
}

/// Checked subtraction of a calendar week offset to a [`Date`]
///
/// This operations results in a [`Date`] on the start of the week, regardless
/// of the week offset.
///
/// This means that if you provide a week offset of `1` with a week start on
/// [monday](Weekday::Monday), and the given date is `2026-03-08` (a sunday),
/// the resulting date will be `2026-03-02`, as it is the first day of the
/// previous week compared to the given date's week.
///
/// This method is mostly used by
/// [`checked_sub_calendar_anchor_offset_to_date`].
///
/// # Errors
///
/// Returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge) if
/// the provided week offset cannot fit in a [`Span`].
///
/// Returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult) if the computed result
/// is out of range for a [`Date`].
///
/// # Examples
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::{Date, Weekday};
/// # use periodical::time::{CalendarAnchorOffsetDateError, checked_sub_calendar_week_offset_to_date};
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         Self::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         Self::JiffError(value)
/// #     }
/// # }
/// let date = "2026-03-04".parse::<Date>()?;
///
/// assert_eq!(
///     checked_sub_calendar_week_offset_to_date(2, Weekday::Sunday, date)?,
///     "2026-02-15".parse::<Date>()?,
/// );
/// assert_eq!(
///     checked_sub_calendar_week_offset_to_date(-2, Weekday::Sunday, date)?,
///     "2026-03-15".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
pub fn checked_sub_calendar_week_offset_to_date(
    weeks_offset: i64,
    week_start: Weekday,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    date.checked_sub(Span::new().days(week_start.until(date.weekday())))
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
        .checked_sub(
            Span::new()
                .try_weeks(weeks_offset)
                .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
        )
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))
}

/// Checked addition of a [`CalendarAnchorOffset`] to a [`Date`]
///
/// This operation results in a [`Date`] on the start of anchor (e.g. day, week,
/// month).
///
/// # Errors
///
/// Returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge) if
/// the provided [`CalendarAnchorOffset`] contains an offset too large to fit in
/// a [`Span`].
///
/// Returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult) if the computed result
/// is out of range for a [`Date`].
///
/// # Examples
///
/// ## Getting the next day
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::Date;
/// # use periodical::time::{
/// #     CalendarAnchorOffset, CalendarAnchorOffsetDateError, checked_add_calendar_anchor_offset_to_date,
/// # };
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         ExampleError::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         ExampleError::JiffError(value)
/// #     }
/// # }
/// assert_eq!(
///     checked_add_calendar_anchor_offset_to_date(
///         CalendarAnchorOffset::Days(1),
///         "2026-03-02".parse::<Date>()?,
///     )?,
///     "2026-03-03".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
///
/// ## Getting the date of 3 months from the end of the month
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::Date;
/// # use periodical::time::{
/// #     CalendarAnchorOffset, CalendarAnchorOffsetDateError, checked_add_calendar_anchor_offset_to_date,
/// # };
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         ExampleError::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         ExampleError::JiffError(value)
/// #     }
/// # }
/// assert_eq!(
///     checked_add_calendar_anchor_offset_to_date(
///         CalendarAnchorOffset::Months(3),
///         "2026-03-05".parse::<Date>()?,
///     )?,
///     "2026-06-01".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
///
/// ## Previous year's start
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::Date;
/// # use periodical::time::{
/// #     CalendarAnchorOffset, CalendarAnchorOffsetDateError, checked_add_calendar_anchor_offset_to_date,
/// # };
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         ExampleError::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         ExampleError::JiffError(value)
/// #     }
/// # }
/// assert_eq!(
///     checked_add_calendar_anchor_offset_to_date(
///         CalendarAnchorOffset::Years(-1),
///         "2026-03-05".parse::<Date>()?,
///     )?,
///     "2025-01-01".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
pub fn checked_add_calendar_anchor_offset_to_date(
    calendar_anchor_offset: CalendarAnchorOffset,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    match calendar_anchor_offset {
        CalendarAnchorOffset::Days(days_offset) => date
            .checked_add(
                Span::new()
                    .try_days(days_offset)
                    .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
            )
            .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult)),
        CalendarAnchorOffset::Weeks(weeks_offset, week_start) => {
            checked_add_calendar_week_offset_to_date(weeks_offset, week_start, date)
        },
        CalendarAnchorOffset::IsoWeeks(weeks_offset) => {
            checked_add_calendar_week_offset_to_date(weeks_offset, Weekday::Monday, date)
        },
        CalendarAnchorOffset::Months(months_offset) => Ok(date
            .checked_add(
                Span::new()
                    .try_months(months_offset)
                    .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
            )
            .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
            .first_of_month()),
        CalendarAnchorOffset::Years(years_offset) => Ok(date
            .checked_add(
                Span::new()
                    .try_years(years_offset)
                    .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
            )
            .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
            .first_of_year()),
    }
}

/// Checked subtraction of a [`CalendarAnchorOffset`] to a [`Date`]
///
/// This operation results in a [`Date`] on the start of anchor (e.g. day, week,
/// month).
///
/// # Errors
///
/// Returns [`OffsetTooLarge`](CalendarAnchorOffsetDateError::OffsetTooLarge) if
/// the provided [`CalendarAnchorOffset`] contains an offset too large to fit in
/// a [`Span`].
///
/// Returns [`OutOfRangeResult`](CalendarAnchorOffsetDateError::OutOfRangeResult) if the computed result
/// is out of range for a [`Date`].
///
/// # Examples
///
/// ## Getting the previous day
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::Date;
/// # use periodical::time::{
/// #     CalendarAnchorOffset, CalendarAnchorOffsetDateError, checked_sub_calendar_anchor_offset_to_date,
/// # };
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         ExampleError::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         ExampleError::JiffError(value)
/// #     }
/// # }
/// assert_eq!(
///     checked_sub_calendar_anchor_offset_to_date(
///         CalendarAnchorOffset::Days(1),
///         "2026-03-02".parse::<Date>()?,
///     )?,
///     "2026-03-01".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
///
/// ## Getting the month for 3 months in the past
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::Date;
/// # use periodical::time::{
/// #     CalendarAnchorOffset, CalendarAnchorOffsetDateError, checked_sub_calendar_anchor_offset_to_date,
/// # };
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         ExampleError::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         ExampleError::JiffError(value)
/// #     }
/// # }
/// assert_eq!(
///     checked_sub_calendar_anchor_offset_to_date(
///         CalendarAnchorOffset::Months(3),
///         "2026-05-10".parse::<Date>()?,
///     )?,
///     "2026-02-01".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
///
/// ## Previous year's start
///
/// ```
/// # use jiff::Error as JiffError;
/// # use jiff::civil::Date;
/// # use periodical::time::{
/// #     CalendarAnchorOffset, CalendarAnchorOffsetDateError, checked_sub_calendar_anchor_offset_to_date,
/// # };
/// #
/// # #[derive(Debug)]
/// # enum ExampleError {
/// #     CalendarAnchorOffsetDateError(CalendarAnchorOffsetDateError),
/// #     JiffError(JiffError),
/// # }
/// #
/// # impl From<CalendarAnchorOffsetDateError> for ExampleError {
/// #     fn from(value: CalendarAnchorOffsetDateError) -> Self {
/// #         ExampleError::CalendarAnchorOffsetDateError(value)
/// #     }
/// # }
/// #
/// # impl From<JiffError> for ExampleError {
/// #     fn from(value: JiffError) -> Self {
/// #         ExampleError::JiffError(value)
/// #     }
/// # }
/// assert_eq!(
///     checked_sub_calendar_anchor_offset_to_date(
///         CalendarAnchorOffset::Years(1),
///         "2026-03-05".parse::<Date>()?,
///     )?,
///     "2025-01-01".parse::<Date>()?,
/// );
/// # Ok::<(), ExampleError>(())
/// ```
pub fn checked_sub_calendar_anchor_offset_to_date(
    calendar_anchor_offset: CalendarAnchorOffset,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    match calendar_anchor_offset {
        CalendarAnchorOffset::Days(days_offset) => date
            .checked_sub(
                Span::new()
                    .try_days(days_offset)
                    .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
            )
            .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult)),
        CalendarAnchorOffset::Weeks(weeks_offset, week_start) => {
            checked_sub_calendar_week_offset_to_date(weeks_offset, week_start, date)
        },
        CalendarAnchorOffset::IsoWeeks(weeks_offset) => {
            checked_sub_calendar_week_offset_to_date(weeks_offset, Weekday::Monday, date)
        },
        CalendarAnchorOffset::Months(months_offset) => Ok(date
            .checked_sub(
                Span::new()
                    .try_months(months_offset)
                    .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
            )
            .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
            .first_of_month()),
        CalendarAnchorOffset::Years(years_offset) => Ok(date
            .checked_sub(
                Span::new()
                    .try_years(years_offset)
                    .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?,
            )
            .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
            .first_of_year()),
    }
}

/// Errors produced by methods converting a [`CalendarAnchorOffset`] to a
/// [`Date`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CalendarAnchorOffsetDateError {
    OffsetTooLarge,
    OutOfRangeResult,
}

impl Display for CalendarAnchorOffsetDateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OffsetTooLarge => write!(f, "Calendar anchor offset was too large to be applied"),
            Self::OutOfRangeResult => write!(f, "Out of range result"),
        }
    }
}

impl Error for CalendarAnchorOffsetDateError {}

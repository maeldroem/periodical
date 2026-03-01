//! Time-related values and structures
//!
//! This module contains constants to refer to midnight, noon, and other similar values.
//!
//! It also contains structures to represent naive durations, used for convenience.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use jiff::{Error as JiffError, Span, Timestamp};
use jiff::civil::{Date, ISOWeekDate, Weekday};
use jiff::tz::TimeZone;

/// Number of days in a week
pub const DAYS_IN_WEEK: u8 = 7;

/// Minimum amount of weeks in a year
pub const WEEKS_IN_SHORT_YEAR: u8 = 52;

/// Maximum amount of weeks in a year
pub const WEEKS_IN_LONG_YEAR: u8 = 53;

/// Number of months in a year
pub const MONTHS_IN_YEAR: u8 = 12;

/// Number of days in a common year
pub const DAYS_IN_COMMON_YEAR: u16 = 365;

/// Number of days in a leap year
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
/// # use jiff::TimeZone;
/// # use periodical::time::naive_date_today;
/// let today_date = naive_date_today();
/// ```
pub fn naive_date_today(tz: &TimeZone) -> Date {
    tz.to_datetime(Timestamp::now()).date()
}

/// Returns the number of ISO weeks in a given year
pub fn iso_weeks_in_year(year: i16) -> Result<u8, JiffError> {
    let start_of_year = Date::new(year, 1, 1)?;

    // https://en.wikipedia.org/wiki/ISO_week_date?useskin=vector#Weeks_per_year
    let is_long_year = start_of_year.weekday() == Weekday::Thursday
        || (start_of_year.in_leap_year() && start_of_year.weekday() == Weekday::Wednesday);
    
    if is_long_year {
        Ok(WEEKS_IN_LONG_YEAR)
    } else {
        Ok(WEEKS_IN_SHORT_YEAR)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OffsetIsoWeek {
    week: u8,
    year: i16,
    week_start_offset: i8,
}

impl OffsetIsoWeek {
    /// Creates a new [`OffsetIsoWeek`] without an offset
    pub fn new(week: u8, year: i16) -> Result<Self, OffsetIsoWeekCreationError> {
        Self::new_with_offset(week, year, 0)
    }

    /// Creates a new [`OffsetIsoWeek`] with the given week start offset
    /// 
    /// # Errors
    /// 
    /// If the year is out of range, [`OutOfRangeYear`](OffsetIsoWeekCreationError::OutOfRangeYear) is returned.
    /// 
    /// If the week start offset is outside the `-6..=6` range,
    /// [`OutOfRangeOffset`](OffsetIsoWeekCreationError::OutOfRangeOffset) is returned.
    pub fn new_with_offset(
        week: u8,
        year: i16,
        week_start_offset: i8,
    ) -> Result<Self, OffsetIsoWeekCreationError> {
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
    pub fn first_day(&self) -> Result<Date, OffsetIsoWeekDateError> {
        let iso_week_first_day = ISOWeekDate::new(
            self.year(),
            i8::try_from(self.week()).or(Err(OffsetIsoWeekDateError))?,
            Weekday::Monday,
        )
            .or(Err(OffsetIsoWeekDateError))?
            .date();

        iso_week_first_day
            .checked_add(Span::new().try_days(self.week_start_offset()).or(Err(OffsetIsoWeekDateError))?)
            .or(Err(OffsetIsoWeekDateError))
    }

    /// Returns the offset last day of the week
    pub fn last_day(&self) -> Result<Date, OffsetIsoWeekDateError> {
        let iso_week_last_day = ISOWeekDate::new(
            self.year(),
            i8::try_from(self.week()).or(Err(OffsetIsoWeekDateError))?,
            Weekday::Sunday,
        )
            .or(Err(OffsetIsoWeekDateError))?
            .date();

        iso_week_last_day
            .checked_add(Span::new().try_days(self.week_start_offset()).or(Err(OffsetIsoWeekDateError))?)
            .or(Err(OffsetIsoWeekDateError))
    }
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OffsetIsoWeekDateError;

impl Display for OffsetIsoWeekDateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Conversion of the OffsetIsoWeek to a Date failed")
    }
}

impl Error for OffsetIsoWeekDateError {}

/// Month representation
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
    /// If the number is greater than 11, [`MonthTryFromNumberError`] is returned.
    #[must_use]
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
    /// If the number is 0 or is greater than 12, [`MonthTryFromNumberError`] is returned.
    #[must_use]
    pub fn try_from_one_offset(x: u8) -> Result<Self, MonthTryFromNumberError> {
        Self::try_from_zero_offset(x.checked_sub(1).ok_or(MonthTryFromNumberError)?)
    }

    /// Associates a year to the [`Month`]
    /// 
    /// TODO
    #[must_use]
    pub fn with_year(self, year: i16) -> NaiveMonthInYear {
        NaiveMonthInYear::new(self, year)
    }

    /// Returns the 0-offset number of the [`Month`]
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

    /// Returns the 1-offset number of the [`Month`]
    #[must_use]
    pub fn one_offset_number(&self) -> u8 {
        self.zero_offset_number().saturating_add(1)
    }
}

impl From<NaiveMonthInYear> for Month {
    fn from(value: NaiveMonthInYear) -> Self {
        value.month()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MonthTryFromNumberError;

impl Display for MonthTryFromNumberError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Conversion from a number to a Month failed")
    }
}

impl Error for MonthTryFromNumberError {}

/// Naive month within a year
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NaiveMonthInYear {
    year: i16,
    month: Month,
}

impl NaiveMonthInYear {
    /// Creates a new [`NaiveMonthInYear`] from the given year and month
    #[must_use]
    pub fn new(month: Month, year: i16) -> Self {
        Self { year, month }
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
    #[must_use]
    pub fn first_day(&self) -> Result<Date, NaiveMonthInYearDayError> {
        Date::new(
            self.year(),
            i8::try_from(self.month().one_offset_number()).or(Err(NaiveMonthInYearDayError::OutOfRangeMonth))?,
            1,
        )
            .or(Err(NaiveMonthInYearDayError::OutOfRangeYear))
    }

    /// Returns the last day of this month of the year
    #[must_use]
    pub fn last_day(&self) -> Result<Date, NaiveMonthInYearDayError> {
        self.first_day().map(|day| day.last_of_month())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NaiveMonthInYearDayError {
    OutOfRangeYear,
    OutOfRangeMonth,
}

impl Display for NaiveMonthInYearDayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeYear => write!(f, "Out of range year"),
            Self::OutOfRangeMonth => write!(f, "Out of range month"),
        }
    }
}

impl Error for NaiveMonthInYearDayError {}

impl PartialOrd for NaiveMonthInYear {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NaiveMonthInYear {
    fn cmp(&self, other: &Self) -> Ordering {
        self.year()
            .cmp(&other.year())
            .then_with(|| self.month().cmp(&other.month()))
    }
}

impl TryFrom<Date> for NaiveMonthInYear {
    type Error = NaiveMonthTryFromNaiveDateError;

    fn try_from(value: Date) -> Result<Self, Self::Error> {
        todo!()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NaiveMonthTryFromNaiveDateError;

impl Display for NaiveMonthTryFromNaiveDateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error when trying to convert a `NaiveDate` into a `NaiveMonth`")
    }
}

impl Error for NaiveMonthTryFromNaiveDateError {}

/// A calendar anchor offset
/// 
/// # What is a calendar anchor
/// 
/// A _calendar anchor_ is any subdivision of the Gregorian calendar, e.g. days, weeks, months, years.
///
/// As other naive units, it is not a precise amount, rather an abstract value that we often use
/// in common speech.
///
/// The goal of this structure is to represent calendar offsets that can be applied to naive structures
/// such as [`Date`s](Date).
/// 
/// # Why can't calendar anchor offsets be combined in one value?
///
/// The reason [`CalendarAnchorOffset`]s can't be combined into one structure (as in you can't add
/// two instances together) as the order in which they are applied to a naive structure such as [`Date`]
/// matters.
/// 
/// # How it works
/// 
/// A calendar anchor offset is very different from how [`Span`]s work, as it interprets calendar offsets
/// by the absolute position of its anchor.
/// 
/// The _absolute position_ of a calendar anchor is based on where the anchors are placed in the calendar,
/// rather than their actual duration.
/// Therefore, a week is not equal to 7 days, it instead represents "What is the nth week compared to X".
/// 
/// For example, if we want the month that happens in 2 months when observing the calendar,
/// and the current date is `2026-04-15`, then it would return June of 2026, as if we only observe the month
/// on the calendar, it is the second month that happens from this month (April of 2026).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CalendarAnchorOffset {
    /// N days calendar anchor offset
    Days(i64),
    /// N weeks with custom week start calendar anchor offset
    Weeks(i64, Weekday),
    /// N ISO weeks calendar anchor offset
    ///
    /// Equivalent to [`CalendarAnchorOffset::Weeks`] using [monday](Weekday::Monday) as the week start.
    IsoWeeks(i64),
    /// N months calendar anchor offset
    Months(i64),
    /// N years calendar anchor offset
    Years(i32),
}

impl CalendarAnchorOffset {
    /// Whether the calendar offset duration is zero
    ///
    /// This does **not** mean that after applying the [`CalendarAnchorOffset`] to another naive structure
    /// will result in the same value as the original naive structure.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(x, _) | Self::IsoWeeks(x) | Self::Months(x) => *x == 0,
            Self::Years(x) => *x == 0,
        }
    }

    /// Whether the stored naive duration is positive (`> 0`)
    ///
    /// This does **not** mean that after applying the [`CalendarAnchorOffset`] to another naive structure
    /// will result in a value greater than the original naive structure.
    #[must_use]
    pub fn is_positive(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(x, _) | Self::IsoWeeks(x) | Self::Months(x) => x.is_positive(),
            Self::Years(x) => x.is_positive(),
        }
    }

    /// Whether the stored naive duration is negative (`< 0`)
    ///
    /// This does **not** mean that after applying the [`CalendarAnchorOffset`] to another naive structure
    /// will result in a value less than the original naive structure.
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

pub fn checked_add_calendar_week_offset_to_date(
    weeks_offset: i64,
    week_start: Weekday,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    date
        .checked_add(Span::new().days(date.weekday().until(week_start)))
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
        .checked_add(
            Span::new().try_weeks(
                weeks_offset.checked_sub(1).ok_or(CalendarAnchorOffsetDateError::OffsetTooLarge)?
            )
                .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
        )
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))
}

pub fn checked_sub_calendar_week_offset_to_date(
    weeks_offset: i64,
    week_start: Weekday,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    date
        .checked_add(Span::new().days(date.weekday().until(week_start)))
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
        .checked_sub(
            Span::new().try_weeks(
                weeks_offset.checked_sub(1).ok_or(CalendarAnchorOffsetDateError::OffsetTooLarge)?
            )
                .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
        )
        .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))
}

pub fn checked_add_calendar_anchor_offset_to_date(
    calendar_anchor_offset: CalendarAnchorOffset,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    match calendar_anchor_offset {
        CalendarAnchorOffset::Days(days_offset) => {
            date
                .checked_add(
                    Span::new()
                        .try_days(days_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))
        },
        CalendarAnchorOffset::Weeks(weeks_offset, week_start) => {
            checked_add_calendar_week_offset_to_date(weeks_offset, week_start, date)
        },
        CalendarAnchorOffset::IsoWeeks(weeks_offset) => {
            checked_add_calendar_week_offset_to_date(weeks_offset, Weekday::Monday, date)
        },
        CalendarAnchorOffset::Months(months_offset) => {
            Ok(date
                .checked_add(
                    Span::new()
                        .try_months(months_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_month())
        },
        CalendarAnchorOffset::Years(years_offset) => {
            Ok(date
                .checked_add(
                    Span::new()
                        .try_years(years_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_year())
        },
    }
}

pub fn checked_sub_calendar_anchor_offset_to_date(
    calendar_anchor_offset: CalendarAnchorOffset,
    date: Date,
) -> Result<Date, CalendarAnchorOffsetDateError> {
    match calendar_anchor_offset {
        CalendarAnchorOffset::Days(days_offset) => {
            date
                .checked_sub(
                    Span::new()
                        .try_days(days_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))
        },
        CalendarAnchorOffset::Weeks(weeks_offset, week_start) => {
            checked_sub_calendar_week_offset_to_date(weeks_offset, week_start, date)
        },
        CalendarAnchorOffset::IsoWeeks(weeks_offset) => {
            checked_sub_calendar_week_offset_to_date(weeks_offset, Weekday::Monday, date)
        },
        CalendarAnchorOffset::Months(months_offset) => {
            Ok(date
                .checked_sub(
                    Span::new()
                        .try_months(months_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_month())
        },
        CalendarAnchorOffset::Years(years_offset) => {
            Ok(date
                .checked_sub(
                    Span::new()
                        .try_years(years_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_year())
        },
    }
}

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

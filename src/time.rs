//! Time-related values and structures
//!
//! This module contains constants to refer to midnight, noon, and other similar values.
//!
//! It also contains structures to represent naive durations, used for convenience.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use jiff::{Error as JiffError, Span, Timestamp};
use jiff::civil::{Date, Weekday};
use jiff::tz::TimeZone;

/// Number of days in a week
pub const DAYS_IN_WEEK: u8 = 7;

/// Minimum amount of weeks in a year
pub const MIN_WEEKS_IN_YEAR: u8 = 52;

/// Maximum amount of weeks in a year
pub const MAX_WEEKS_IN_YEAR: u8 = 53;

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

/// Returns the amount of weeks in a given year
/// 
/// Since weeks can start on different days, this function takes a [`Weekday`].
/// 
/// # Errors
/// 
/// Returns [`Error`](JiffError) if the given year is out of range.
/// 
/// TEST THIS THOROUGHLY
pub fn weeks_in_year(year: i16, week_start: Weekday) -> Result<u8, JiffError> {
    let start_of_year = Date::new(year, 1, 1)?;
    let first_weekday = start_of_year.weekday();
    let leftover_days = i8::from(start_of_year.days_in_year() % DAYS_IN_WEEK);
    
    // Logic: if the amount of days to reach `week_start` from `first_weekday` is greater than the leftover days,
    // this means that we have "entered" a new multiple of 7, a week, therefore there will be no space at
    // the end of the year to store an extra week start.
    if week_start.until(first_weekday) > leftover_days {
        Ok(MIN_WEEKS_IN_YEAR)
    } else {
        Ok(MAX_WEEKS_IN_YEAR)
    }
}

/// Naive week with a week start [`Weekday`]
/// 
/// Represents a given week within an unspecified year, starting on a given [`Weekday`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NaiveWeek {
    week_number: u8, // 1-offset
    week_start: Weekday,
}

impl NaiveWeek {
    /// Creates a new [`NaiveWeek`] from a given week number and week start [`Weekday`]
    /// 
    /// The given week number is expressed as a 1-offset number, so week 1 is the first week.
    /// 
    /// TODO ERRORS
    #[must_use]
    pub fn new(week_number: u8, week_start: Weekday) -> Result<Self, NaiveWeekCreationError> {
        if week_number == 0 || week_number > MAX_WEEKS_IN_YEAR {
            return Err(NaiveWeekCreationError::OutOfRangeWeekNumber);
        }

        Ok(NaiveWeek { week_number, week_start })
    }

    /// Returns the 1-offset week number
    /// 
    /// The returned week number is expressed as a 1-offset number, so week 1 is the first week.
    #[must_use]
    pub fn week_number(&self) -> u8 {
        self.week_number
    }

    /// Returns the week start [`Weekday`]
    #[must_use]
    pub fn week_start(&self) -> Weekday {
        self.week_start
    }

    /// Associates a given year with the week
    /// 
    /// TODO ERRORS
    /// 
    /// # Examples
    /// 
    /// TODO
    #[must_use]
    pub fn with_year(self, year: i16) -> Result<NaiveWeekInYear, NaiveWeekInYearCreationError> {
        NaiveWeekInYear::from_naive_week(self, year)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NaiveWeekCreationError {
    OutOfRangeWeekNumber,
}

impl Display for NaiveWeekCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeWeekNumber => write!(f, "Out of range week number"),
        }
    }
}

impl Error for NaiveWeekCreationError {}

impl TryFrom<NaiveWeekInYear> for NaiveWeek {
    type Error = NaiveWeekCreationError;

    fn try_from(value: NaiveWeekInYear) -> Result<Self, Self::Error> {
        NaiveWeek::new(value.week_number(), value.week_start())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NaiveWeekInYear {
    week_number: u8, // 1-offset
    week_start: Weekday,
    year: i16,
}

impl NaiveWeekInYear {
    /// Creates a new [`NaiveWeekInYear`] from a week number, week start, and year
    /// 
    /// The given week number is expressed as a 1-offset number, so week 1 is the first week.
    /// 
    /// TODO ERRORS
    #[must_use]
    pub fn new(week_number: u8, week_start: Weekday, year: i16) -> Result<Self, NaiveWeekInYearCreationError> {
        if week_number == 0
            || week_number > weeks_in_year(year, week_start).or(Err(NaiveWeekInYearCreationError::OutOfRangeYear))?
        {
            return Err(NaiveWeekInYearCreationError::OutOfRangeWeekNumber);
        }

        Ok(NaiveWeekInYear { week_number, week_start, year })
    }

    /// Creates a new [`NaiveWeekInYear`] from a [`NaiveWeek`] and a year
    /// 
    /// # Examples
    /// 
    /// TODO
    #[must_use]
    pub fn from_naive_week(naive_week: NaiveWeek, year: i16) -> Result<Self, NaiveWeekInYearCreationError> {
        NaiveWeekInYear::new(naive_week.week_number(), naive_week.week_start(), year)
    }

    /// Returns the 1-offset week number
    /// 
    /// The returned week number is expressed as a 1-offset number, so week 1 is the first week.
    #[must_use]
    pub fn week_number(&self) -> u8 {
        self.week_number
    }

    /// Returns the week start [`Weekday`]
    #[must_use]
    pub fn week_start(&self) -> Weekday {
        self.week_start
    }

    /// Returns the year
    #[must_use]
    pub fn year(&self) -> i16 {
        self.year
    }

    /// Returns the first day of the week
    #[must_use]
    pub fn first_day(&self) -> Result<Date, NaiveWeekDayError> {
        let start_of_year = Date::new(self.year(), 1, 1).or(Err(NaiveWeekDayError::OutOfRangeYear))?;

        let days_from_first_day = u16::from(
            weeks_in_year(self.year(), self.week_start())
                .or(Err(NaiveWeekDayError::OutOfRangeYear))?
        )
            .strict_mul(u16::from(DAYS_IN_WEEK))
            .strict_add(u16::from(start_of_year.weekday().until(self.week_start()).unsigned_abs()));

        start_of_year
            .checked_add(Span::new().days(days_from_first_day))
            .or(Err(NaiveWeekDayError::OutOfRangeResult))
    }

    /// Returns the last day of the week
    #[must_use]
    pub fn last_day(&self) -> Result<Date, NaiveWeekDayError> {
        self
            .first_day()
            .and_then(|day| day
                .checked_add(Span::new().days(DAYS_IN_WEEK - 1))
                .or(Err(NaiveWeekDayError::OutOfRangeResult))
            )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NaiveWeekInYearCreationError {
    OutOfRangeYear,
    OutOfRangeWeekNumber,
}

impl Display for NaiveWeekInYearCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeYear => write!(f, "Out of range year"),
            Self::OutOfRangeWeekNumber => write!(f, "Out of range week number"),
        }
    }
}

impl Error for NaiveWeekInYearCreationError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NaiveWeekDayError {
    OutOfRangeYear,
    OutOfRangeResult,
}

impl Display for NaiveWeekDayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeYear => write!(f, "Out of range year"),
            Self::OutOfRangeResult => write!(f, "Out of range result"),
        }
    }
}

impl Error for NaiveWeekDayError {}

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
            date
                .checked_add(
                    Span::new()
                        .try_months(months_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_month()
        },
        CalendarAnchorOffset::Years(years_offset) => {
            date
                .checked_add(
                    Span::new()
                        .try_years(years_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_year()
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
            date
                .checked_sub(
                    Span::new()
                        .try_months(months_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_month()
        },
        CalendarAnchorOffset::Years(years_offset) => {
            date
                .checked_sub(
                    Span::new()
                        .try_years(years_offset)
                        .or(Err(CalendarAnchorOffsetDateError::OffsetTooLarge))?
                )
                .or(Err(CalendarAnchorOffsetDateError::OutOfRangeResult))?
                .first_of_year()
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

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

pub const DAYS_IN_COMMON_YEAR: u16 = 365;

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
/// TEST THIS THOROUGHLY
pub fn weeks_in_year(year: i16, week_start: Weekday) -> Result<u8, JiffError> {
    let start_of_year = Date::new(year, 1, 1)?;
    let first_weekday = start_of_year.clone().weekday();
    let leftover_days = start_of_year.days_in_year() % DAYS_IN_WEEK;
    
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

impl From<NaiveWeekInYear> for NaiveWeek {
    fn from(value: NaiveWeekInYear) -> Self {
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
    pub fn from_naive_week(naive_week: NaiveWeek, year: i16) -> Self {
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

    #[must_use]
    pub fn first_day(&self) -> Result<Date, ()> {
        let start_of_year = Date::new(self.year(), 1, 1)?;

        let days_from_first_day = u16::from(weeks_in_year(self.year(), self.week_start())?)
            .strict_mul(u16::from(DAYS_IN_WEEK))
            .strict_add(start_of_year.clone().weekday().until(self.week_start()));

        start_of_year.checked_add(Span::new().days(days_from_first_day))?
    }

    #[must_use]
    pub fn last_day(&self) -> Result<Date, ()> {
        self.first_day().and_then(|day| day.checked_add(Span::new().days(DAYS_IN_WEEK - 1)))
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
    pub fn new(year: i16, month: Month) -> Self {
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
    pub fn first_day(&self) -> Result<Date, ()> {
        Date::new(self.year(), i8::try_from(self.month().one_offset_number()), 1)
    }

    /// Returns the last day of this month of the year
    #[must_use]
    pub fn last_day(&self) -> Result<Date, ()> {
        self.first_day().map(|day| day.last_of_month())
    }
}

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

/// A naive duration
///
/// As other naive units, it is not a precise amount, rather an abstract value that we often use
/// in common speech.
///
/// The goal of this structure is to represent naive durations that can be applied to naive structures
/// such as [`Date`s](Date).
///
/// The reason [`NaiveDuration`]s can't be combined into one structure (as in you can't add
/// two instances together) as the order in which they are applied to a naive structure such as [`Date`]
/// matters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NaiveDuration {
    /// Naive days duration
    Days(i64),
    /// Naive weeks duration
    ///
    /// The naive week is defined using a given [`Weekday`] as its start day.
    ///
    /// <div class="warning">
    ///
    /// Moving 2 weeks away **does not mean 14 naive days**.
    ///
    /// Instead, it refers to the second week to come after the current one.
    ///
    /// </div>
    Weeks(Weekday, i64),
    /// Naive ISO weeks duration
    ///
    /// Equivalent to [`NaiveDuration::Weeks`] using [monday](Weekday::Monday) as the week start.
    IsoWeeks(i64),
    /// Naive months duration
    ///
    /// <div class="warning">
    ///
    /// Moving 1 month away **does not mean 30/31 naive days**.
    ///
    /// Instead, it refers to the first month to come after the current one.
    ///
    /// </div>
    Months(i64),
    /// Naive years duration
    ///
    /// <div class="warning">
    ///
    /// Moving 1 year away **does not mean 365 naive days**.
    ///
    /// Instead, it refers to the first year to come after the current one.
    ///
    /// </div>
    Years(i32),
}

impl NaiveDuration {
    /// Whether the stored naive duration is zero
    ///
    /// This does **not** mean that after applying the [`NaiveDuration`] to another naive structure
    /// will result in the same naive structure.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(_, x) | Self::IsoWeeks(x) | Self::Months(x) => *x == 0,
            Self::Years(x) => *x == 0,
        }
    }

    /// Whether the stored naive duration is positive (`> 0`)
    ///
    /// This does **not** mean that after applying the [`NaiveDuration`] to another naive structure
    /// will result in a naive structure that go after the original one.
    #[must_use]
    pub fn is_positive(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(_, x) | Self::IsoWeeks(x) | Self::Months(x) => x.is_positive(),
            Self::Years(x) => x.is_positive(),
        }
    }

    /// Whether the stored naive duration is negative (`< 0`)
    ///
    /// This does **not** mean that after applying the [`NaiveDuration`] to another naive structure
    /// will result in a naive structure that precedes the original one.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        match self {
            Self::Days(x) | Self::Weeks(_, x) | Self::IsoWeeks(x) | Self::Months(x) => x.is_negative(),
            Self::Years(x) => x.is_negative(),
        }
    }
}

impl PartialOrd for NaiveDuration {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Days(x), Self::Days(y))
            | (Self::Weeks(_, x), Self::Weeks(_, y))
            | (Self::Months(x), Self::Months(y)) => Some(x.cmp(y)),
            (Self::Years(x), Self::Years(y)) => Some(x.cmp(y)),
            _ => None,
        }
    }
}

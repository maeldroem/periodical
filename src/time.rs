//! Time-related values and structures
//!
//! This module contains constants to refer to midnight, noon, and other similar values.
//!
//! It also contains structures to represent naive durations, used for convenience.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use jiff::Timestamp;
use jiff::civil::{Date, Weekday};
use jiff::tz::TimeZone;

/// Number of days in a week
pub const DAYS_IN_WEEK: u8 = 7;

/// Number of months in a year
pub const MONTHS_IN_YEAR: u8 = 12;

pub const DAYS_IN_COMMON_YEAR: u16 = 365;

pub const DAYS_IN_LEAP_YEAR: u16 = 366;

/// Gets the [`NaiveDate`] for today
///
/// # Examples
///
/// ```
/// # use std::num::TryFromIntError;
/// # use chrono::{Duration, FixedOffset, NaiveDate};
/// # use periodical::time::naive_date_today;
/// #
/// # #[derive(Debug)]
/// # struct FixedOffsetError;
/// #
/// # #[derive(Debug)]
/// # enum ExampleErr {
/// #     TryFromIntError(TryFromIntError),
/// #     FixedOffsetError(FixedOffsetError),
/// # }
/// #
/// # impl From<TryFromIntError> for ExampleErr {
/// #     fn from(value: TryFromIntError) -> Self {
/// #         ExampleErr::TryFromIntError(value)
/// #     }
/// # }
/// #
/// # impl From<FixedOffsetError> for ExampleErr {
/// #     fn from(value: FixedOffsetError) -> Self {
/// #         ExampleErr::FixedOffsetError(value)
/// #     }
/// # }
/// let tz = FixedOffset::east_opt(Duration::hours(2).num_seconds().try_into()?).ok_or(FixedOffsetError)?;
/// let today_date = naive_date_today(&tz);
/// # Ok::<(), ExampleErr>(())
/// ```
pub fn naive_date_today(tz: &TimeZone) -> Date {
    tz.to_datetime(Timestamp::now()).date()
}

/// Naive week with a week start [`Weekday`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NaiveWeek {
    week: u8,
    week_start: Weekday,
}

impl NaiveWeek {
    pub fn new(week: u8, week_start: Weekday) -> Self {
        NaiveWeek { week, week_start }
    }
}

/// Naive ISO week
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NaiveIsoWeek {
    week: u8,
}

impl NaiveIsoWeek {
    pub fn new(week: u8) -> Self {
        NaiveIsoWeek { week }
    }
}

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
        Ok(NaiveMonthInYear::new(
            value.year(),
            Month::try_from(u8::try_from(value.month()).or(Err(NaiveMonthTryFromNaiveDateError))?)
                .or(Err(NaiveMonthTryFromNaiveDateError))?,
        ))
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
/// For example, _a day_ is ambiguous. It can either refer to what we would call a _naive day_
/// or a duration of 24 hours.
/// A _naive day_ is often made of 24 hours, **but not always**, as if the day goes over
/// a daylight savings time change, the _naive day_ could be made up of 25 hours or 23 hours.
/// This is the key difference that requires the use of naive structures.
///
/// The goal of this structure is to represent naive durations that can be applied to naive structures
/// such as [`NaiveDate`s](NaiveDate).
///
/// The reason [`NaiveDuration`]s can't be combined into one structure (as in you can't add
/// two instances together) as the order in which they are applied to a naive structure such as [`NaiveDate`]
/// matters.
///
/// In the future, this may be the object of a PR to the [`chrono`] crate and therefore may move.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NaiveDuration {
    /// Naive days duration
    ///
    /// Equivalent to [`chrono::Days`].
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

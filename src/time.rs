//! Time-related values and structures
//!
//! This module contains constants to refer to midnight, noon, and other similar values.
//!
//! It also contains structures to represent naive durations, used for convenience.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use chrono::{Datelike, Month, NaiveDate, NaiveTime, TimeZone, Utc, Weekday};

/// Number of days in a week
pub const DAYS_IN_WEEK: u8 = 7;

/// Number of months in a year
pub const MONTHS_IN_YEAR: u8 = 12;

pub const DAYS_IN_COMMON_YEAR: u16 = 365;

pub const DAYS_IN_LEAP_YEAR: u16 = 366;

/// Represents midnight as a [`NaiveTime`]
pub const NAIVE_TIME_MIDNIGHT: NaiveTime =
    NaiveTime::from_hms_opt(0, 0, 0).expect("Provided valid hour/minute/second (hms) combination");

/// Represents noon as a [`NaiveTime`]
pub const NAIVE_TIME_NOON: NaiveTime =
    NaiveTime::from_hms_opt(12, 0, 0).expect("Provided valid hour/minute/second (hms) combination");

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
pub fn naive_date_today<Tz>(tz: &Tz) -> NaiveDate
where
    Tz: TimeZone,
{
    Utc::now().with_timezone(tz).date_naive()
}

/// Naive month within a year
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NaiveMonth {
    year: i32,
    month: Month,
}

impl NaiveMonth {
    /// Creates a new [`NaiveMonth`] from the given year and month
    #[must_use]
    pub fn new(year: i32, month: Month) -> Self {
        Self { year, month }
    }

    /// Returns the year of the [`NaiveMonth`]
    #[must_use]
    pub fn year(&self) -> i32 {
        self.year
    }

    /// Returns the [`Month`] of the [`NaiveMonth`]
    #[must_use]
    pub fn month(&self) -> Month {
        self.month
    }

    /// Returns the first day of the month
    ///
    /// Returns [`None`] if a [`NaiveDate`] cannot be created with the year and month, usually meaning
    /// the date is out of range, see [`NaiveDate::from_ymd_opt`].
    #[must_use]
    pub fn checked_first_day(&self) -> Option<NaiveDate> {
        NaiveDate::from_ymd_opt(self.year(), self.month().number_from_month(), 1)
    }

    /// Returns the first day of the month
    ///
    /// Returns [`None`] if a [`NaiveDate`] cannot be created with the year and month, usually meaning
    /// the date is out of range, see [`NaiveDate::from_ymd_opt`].
    #[must_use]
    pub fn checked_last_day(&self) -> Option<NaiveDate> {
        NaiveDate::from_ymd_opt(
            self.year(),
            self.month().number_from_month(),
            u32::from(self.month().num_days(self.year())?),
        )
    }
}

impl PartialOrd for NaiveMonth {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NaiveMonth {
    fn cmp(&self, other: &Self) -> Ordering {
        self.year()
            .cmp(&other.year())
            .then_with(|| self.month().cmp(&other.month()))
    }
}

impl TryFrom<NaiveDate> for NaiveMonth {
    type Error = NaiveMonthTryFromNaiveDateError;

    fn try_from(value: NaiveDate) -> Result<Self, Self::Error> {
        Ok(NaiveMonth::new(
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
/// Naive durations are similar to [`chrono::Duration`], but follow the same convention as
/// other naive structures from the [`chrono`] crate.
/// That is to say, it is not a precise amount, rather an abstract value that we often use
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
    /// Equivalent to [`NaiveDuration::Weeks`] using [monday](Weekday::Mon) as the week start.
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

/// Checked addition of a [`NaiveDuration`] to a [`NaiveDate`]
///
/// Adding [days](NaiveDuration::Days) to a [`NaiveDate`] simply uses [`NaiveDate::checked_add_days`].
///
/// For other naive durations, the standard behavior is to select the first day of the unit.
/// For example, adding one [naive week](NaiveDuration::Weeks) will result in the date of the start
/// of next week.
///
/// That also means that adding zero of some unit will result in the first day of that unit.
/// For example, adding zero [naive years](NaiveDuration::Years) will result in the first January
/// of the current year.
///
/// Returns [`None`] if the resulting date is out of range or if a duration to add during operations
/// overflows its container.
///
/// For example, if a [naive months duration](NaiveDuration::Months) such that the number of months divided
/// by the number of months in a year (12) is greater than what [i32] can store, i.e. [`i32::MAX`].
#[must_use]
pub fn checked_add_naive_duration_to_naive_date(
    naive_date: NaiveDate,
    naive_duration: NaiveDuration,
) -> Option<NaiveDate> {
    match naive_duration {
        NaiveDuration::Days(x) => {
            let duration = chrono::Days::new(x.unsigned_abs());

            if x >= 0 {
                naive_date.checked_add_days(duration)
            } else {
                naive_date.checked_sub_days(duration)
            }
        },
        NaiveDuration::Weeks(week_start, x) => checked_add_naive_weeks_to_naive_date(week_start, x, naive_date),
        NaiveDuration::IsoWeeks(x) => checked_add_naive_weeks_to_naive_date(Weekday::Mon, x, naive_date),
        NaiveDuration::Months(x) => {
            // How many years in the given amount of months
            let mut years_offset = x.unsigned_abs() / u64::from(MONTHS_IN_YEAR);
            // Removing the extra years in the duration, how many months are we actually offset from?
            let months_offset = u32::try_from(x.unsigned_abs() % u64::from(MONTHS_IN_YEAR)).ok()?;

            if x >= 0 {
                // Checks if after applying the month offset we get an additional year
                if months_offset > (u32::from(MONTHS_IN_YEAR) - naive_date.month()) {
                    years_offset += 1;
                }

                // Since for the first part of the computation we use 0-based months, we add 1 at the end
                let month = ((naive_date.month0() + months_offset) % u32::from(MONTHS_IN_YEAR)) + 1;

                NaiveDate::from_ymd_opt(
                    naive_date.year().checked_add(i32::try_from(years_offset).ok()?)?,
                    month,
                    1,
                )
            } else {
                // Checks if after applying the month offset we get an additional year
                // We use 0-based months to simplify the check
                if months_offset > naive_date.month0() {
                    years_offset += 1;
                }

                let month = (
                    (
                        // modulo subtraction
                        naive_date.month0()
                        + u32::from(MONTHS_IN_YEAR) // we add 12 to the 0-based month to prevent underflow
                        - months_offset
                        // subtract the computed offset
                    ) % u32::from(MONTHS_IN_YEAR)
                    // get the actual 0-based month
                ) + 1; // convert to 1-based month

                NaiveDate::from_ymd_opt(
                    naive_date.year().checked_sub(i32::try_from(years_offset).ok()?)?,
                    month,
                    1,
                )
            }
        },
        NaiveDuration::Years(x) => NaiveDate::from_ymd_opt(naive_date.year().checked_add(x)?, 1, 1),
    }
}

fn checked_add_naive_weeks_to_naive_date(
    week_start: Weekday,
    amount: i64,
    naive_date: NaiveDate,
) -> Option<NaiveDate> {
    // The absolute value of i64 is always storable in a u64, as we get rid of the sign bit
    let weeks = amount.unsigned_abs();
    // Since the now-removed sign bit isn't used, we can multiply the value by 2
    // so that we do make use of this last bit (as *2 = <<1).
    // We use the checked multiplication so that we still prevent potential panics, even though
    // they should not happen.
    let double_weeks = chrono::Days::new(weeks.checked_mul(2)?);
    // Shadow the weeks variable in order to store it in the structure chrono expects
    let weeks = chrono::Days::new(weeks);

    let week_first_day = naive_date.week(week_start).checked_first_day()?;

    // (3*2 + 1)*weeks = 7*weeks = weeks in days
    if amount >= 0 {
        week_first_day
            .checked_add_days(double_weeks)?
            .checked_add_days(double_weeks)?
            .checked_add_days(double_weeks)?
            .checked_add_days(weeks)
    } else {
        week_first_day
            .checked_sub_days(double_weeks)?
            .checked_sub_days(double_weeks)?
            .checked_sub_days(double_weeks)?
            .checked_sub_days(weeks)
    }
}

/// Checked subtraction of a [`NaiveDuration`] to a [`NaiveDate`]
///
/// Subtracting [days](NaiveDuration::Days) to a [`NaiveDate`] simply uses [`NaiveDate::checked_sub_days`].
///
/// For other naive durations, the standard behavior is to select the first day of the unit.
/// For example, subtracting one [naive week](NaiveDuration::Weeks) will result in the date of the start
/// of the previous week.
///
/// That also means that subtracting zero of some unit will result in the first day of that unit.
/// For example, subtracting zero [naive years](NaiveDuration::Years) will result in the first January
/// of the current year.
///
/// Returns [`None`] if the resulting date is out of range or if a duration to subtract during operations
/// overflows its container.
///
/// For example, if a [naive months duration](NaiveDuration::Months) such that the number of months divided
/// by the number of months in a year (12) is greater than what [i32] can store, i.e. [`i32::MAX`].
#[must_use]
pub fn checked_sub_naive_duration_to_naive_date(
    naive_date: NaiveDate,
    naive_duration: NaiveDuration,
) -> Option<NaiveDate> {
    // Most add/sub operations are reversed from `checked_add_naive_duration_to_naive_date`
    // We _could_ just make this function a wrapper of the aforementioned one, but that would require
    // flipping the sign of the stored naive duration quantity, which can't be done "safely" as
    // abs(i32::MIN) > abs(i32::MAX)
    match naive_duration {
        NaiveDuration::Days(x) => {
            let duration = chrono::Days::new(x.unsigned_abs());

            if x >= 0 {
                naive_date.checked_sub_days(duration)
            } else {
                naive_date.checked_add_days(duration)
            }
        },
        NaiveDuration::Weeks(week_start, x) => checked_sub_naive_weeks_to_naive_date(week_start, x, naive_date),
        NaiveDuration::IsoWeeks(x) => checked_sub_naive_weeks_to_naive_date(Weekday::Mon, x, naive_date),
        NaiveDuration::Months(x) => {
            // How many years in the given amount of months
            let mut years_offset = x.unsigned_abs() / u64::from(MONTHS_IN_YEAR);
            // Removing the extra years in the duration, how many months are we actually offset from?
            let months_offset = u32::try_from(x.unsigned_abs() % u64::from(MONTHS_IN_YEAR)).ok()?;

            if x >= 0 {
                // Checks if after applying the month offset we get an additional year
                // We use 0-based months to simplify the check
                if months_offset > naive_date.month0() {
                    years_offset += 1;
                }

                let month = (
                    (
                        // modulo subtraction
                        naive_date.month0()
                        + u32::from(MONTHS_IN_YEAR) // we add 12 to the 0-based month to prevent underflow
                        - months_offset
                        // subtract the computed offset
                    ) % u32::from(MONTHS_IN_YEAR)
                    // get the actual 0-based month
                ) + 1; // convert to 1-based month

                NaiveDate::from_ymd_opt(
                    naive_date.year().checked_sub(i32::try_from(years_offset).ok()?)?,
                    month,
                    1,
                )
            } else {
                // Checks if after applying the month offset we get an additional year
                if months_offset > (u32::from(MONTHS_IN_YEAR) - naive_date.month()) {
                    years_offset += 1;
                }

                // Since for the first part of the computation we use 0-based months, we add 1 at the end
                let month = ((naive_date.month0() + months_offset) % u32::from(MONTHS_IN_YEAR)) + 1;

                NaiveDate::from_ymd_opt(
                    naive_date.year().checked_add(i32::try_from(years_offset).ok()?)?,
                    month,
                    1,
                )
            }
        },
        NaiveDuration::Years(x) => NaiveDate::from_ymd_opt(naive_date.year().checked_sub(x)?, 1, 1),
    }
}

fn checked_sub_naive_weeks_to_naive_date(
    week_start: Weekday,
    amount: i64,
    naive_date: NaiveDate,
) -> Option<NaiveDate> {
    // The absolute value of i64 is always storable in a u64, as we get rid of the sign bit
    let weeks = amount.unsigned_abs();
    // Since the now-removed sign bit isn't used, we can multiply the value by 2
    // so that we do make use of this last bit (as *2 = <<1).
    // We use the checked multiplication so that we still prevent potential panics, even though
    // they should not happen.
    let double_weeks = chrono::Days::new(weeks.checked_mul(2)?);
    // Shadow the weeks variable in order to store it in the structure chrono expects
    let weeks = chrono::Days::new(weeks);

    let week_first_day = naive_date.week(week_start).checked_first_day()?;

    // (3*2 + 1)*weeks = 7*weeks = weeks in days
    if amount >= 0 {
        week_first_day
            .checked_sub_days(double_weeks)?
            .checked_sub_days(double_weeks)?
            .checked_sub_days(double_weeks)?
            .checked_sub_days(weeks)
    } else {
        week_first_day
            .checked_add_days(double_weeks)?
            .checked_add_days(double_weeks)?
            .checked_add_days(double_weeks)?
            .checked_add_days(weeks)
    }
}

/// Sequentially applies [`checked_add_naive_duration_to_naive_date`] on a [`NaiveDate`]
///
/// Returns [`None`] as soon as one [`checked_add_naive_duration_to_naive_date`] returns [`None`].
///
/// Returns [`None`] if the given list of [`NaiveDuration`s](NaiveDuration) is empty.
#[must_use]
pub fn checked_add_naive_durations_to_naive_date<I>(naive_date: NaiveDate, naive_durations: I) -> Option<NaiveDate>
where
    I: IntoIterator<Item = NaiveDuration>,
{
    naive_durations
        .into_iter()
        .try_fold(naive_date, checked_add_naive_duration_to_naive_date)
}

/// Sequentially applies [`checked_sub_naive_duration_to_naive_date`] on a [`NaiveDate`]
///
/// Returns [`None`] as soon as one [`checked_sub_naive_duration_to_naive_date`] returns [`None`].
///
/// Returns [`None`] if the given list of [`NaiveDuration`s](NaiveDuration) is empty.
#[must_use]
pub fn checked_sub_naive_durations_to_naive_date<I>(naive_date: NaiveDate, naive_durations: I) -> Option<NaiveDate>
where
    I: IntoIterator<Item = NaiveDuration>,
{
    naive_durations
        .into_iter()
        .try_fold(naive_date, checked_sub_naive_duration_to_naive_date)
}

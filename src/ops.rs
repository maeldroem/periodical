//! Generic operation-related structures
//!
//! This module contains [`Precision`], [`RunningResult`] and set operations result structures.
//!
//! Those structures are not part of [`intervals::ops`](crate::intervals::ops) as they are not related to intervals
//! and can be used in other contexts.

use std::error::Error;
use std::fmt::Display;
use std::time::Duration as StdDuration;

use jiff::tz::{AmbiguousZoned, TimeZone};
use jiff::{SignedDuration, Zoned};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Mode for applying a [`Precision`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum PrecisionMode {
    /// Rounds the given time(s) to the nearest multiple of the duration
    /// 
    /// In case of a tie, round up (to future).
    ToNearest,
    /// Ceils/Rounds up the given time(s) to the duration
    ToFuture,
    /// Floors/Rounds down the compared times to the duration
    ToPast,
}

impl PrecisionMode {
    /// Creates a [`Precision`] with the given precision without checking invariants
    /// 
    /// Equivalent to calling [`Precision::unchecked_new`] with `self` and the desired duration.
    #[must_use]
    pub fn unchecked_with_precision(self, precision: StdDuration) -> Precision {
        Precision::unchecked_new(precision, self)
    }

    /// Creates a [`Precision`] with the given precision
    /// 
    /// Equivalent to calling [`Precision::new`] with `self` and the desired duration.
    /// 
    /// # Errors
    /// 
    /// Returns [`PrecisionIsZero`](PrecisionCreationError::PrecisionIsZero) if the given precision
    /// is zero.
    pub fn with_precision(self, precision: StdDuration) -> Result<Precision, PrecisionCreationError> {
        Precision::new(precision, self)
    }
}

/// Precision to round times and intervals
///
/// Stores a [`PrecisionMode`] and a duration to apply a precision.
/// 
/// Rounding a time is useful in many cases, such as when a output time is expected to be a multiple
/// of a certain duration. In some companies, this is used to be able to convert work time into pay
/// without having to handle fractions.
///
/// Common rounding values such as 5 minutes, 15 minutes, 45 minutes, 1 hour, are all divisors of 24 hours,
/// which means that they all are modular with respect to 24 hours.
/// In other words: the instants to which all times within a day are rounded to, given the precision,
/// remain the same across days.
///
/// If you want to use other durations that may not exactly divide a day, you should keep in mind that the rounding
/// is always based on [the Unix epoch](https://en.wikipedia.org/w/index.php?title=Unix_time&oldid=1308795653).
///
/// To solve that problem, you can use another frame of reference for the rounding using the
/// [`precise_time_with_base_time`](Precision::precise_time_with_base_time) method.
///
/// Also, a time will never change if it is already a multiple of the precision duration.
/// For example, if we round up to every 5 minutes, `08:05:00` won't be rounded up.
/// But the instant you have even just a single microsecond more than that, it will be rounded up.
/// 
/// Rounding a time can also be ambiguous when the given day includes timezone-related offsets,
/// like daylight savings. How those issues are handled are explained in more details in
/// the relevant methods.
/// 
/// # Invariants
/// 
/// The stored precision must be positive.
///
/// # Examples
///
/// ## Rounding to the nearest 5 minutes
///
/// ```
/// # use std::error::Error;
/// # use std::time::Duration;
/// # use jiff::Zoned;
/// # use periodical::ops::{Precision, PrecisionMode};
/// let round_to_nearest_five_mins = Precision::new(Duration::from_mins(5), PrecisionMode::ToNearest)?;
///
/// let two_minutes_after_eight = "2025-01-01 08:02:11[Europe/Oslo]".parse::<Zoned>()?;
/// let fourteen_minutes_after_ten = "2025-01-01 10:14:21[Europe/Oslo]".parse::<Zoned>()?;
///
/// assert_eq!(
///     round_to_nearest_five_mins.precise_time(&two_minutes_after_eight)?.unambiguous()?,
///     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?,
/// );
///
/// assert_eq!(
///     round_to_nearest_five_mins.precise_time(&fourteen_minutes_after_ten)?.unambiguous()?,
///     "2025-01-01 10:15:00[Europe/Oslo]".parse::<Zoned>()?,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Rounding up every 35 minutes with a given base time
///
/// ```
/// # use std::error::Error;
/// # use std::time::Duration;
/// # use jiff::Zoned;
/// # use periodical::ops::{Precision, PrecisionMode};
/// let round_up_every_35_mins = Precision::new(Duration::from_mins(35), PrecisionMode::ToFuture)?;
///
/// let first_january_2025 = "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?;
/// let two_minutes_after_eight = "2025-01-01 08:02:11[Europe/Oslo]".parse::<Zoned>()?;
/// let fourteen_minutes_after_ten = "2025-01-01 10:14:21[Europe/Oslo]".parse::<Zoned>()?;
///
/// // 13 * 35m = 07:35
/// // 14 * 35m = 08:10
/// assert_eq!(
///     round_up_every_35_mins.precise_time_with_base_time(
///         &two_minutes_after_eight,
///         &first_january_2025,
///         None,
///     )?,
///     "2025-01-01 08:10:00[Europe/Oslo]".parse::<Zoned>()?,
/// );
///
/// // 17 * 35m = 09:55
/// // 18 * 35m = 10:30
/// assert_eq!(
///     round_up_every_35_mins.precise_time_with_base_time(
///         &fourteen_minutes_after_ten,
///         &first_january_2025,
///         None,
///     )?,
///     "2025-01-01 10:30:00[Europe/Oslo]".parse::<Zoned>()?,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct Precision {
    precision: StdDuration,
    mode: PrecisionMode,
}

impl Precision {
    /// Creates a new [`Precision`] without checking invariants
    #[must_use]
    pub fn unchecked_new(precision: StdDuration, mode: PrecisionMode) -> Self {
        Precision {
            precision,
            mode,
        }
    }

    /// Creates a new [`Precision`]
    /// 
    /// # Errors
    /// 
    /// Returns [`PrecisionIsZero`](PrecisionCreationError::PrecisionIsZero) if the given precision
    /// is zero.
    pub fn new(precision: StdDuration, mode: PrecisionMode) -> Result<Self, PrecisionCreationError> {
        if precision.is_zero() {
            return Err(PrecisionCreationError::PrecisionIsZero);
        }

        Ok(Self::unchecked_new(precision, mode))
    }

    /// Returns the precision duration
    #[must_use]
    pub fn precision(&self) -> StdDuration {
        self.precision
    }

    /// Returns the [`PrecisionMode`]
    #[must_use]
    pub fn mode(&self) -> PrecisionMode {
        self.mode
    }

    /// Applies the precision to a given [`u128`] representing a duration
    /// 
    /// This operation is mostly designed for use by [`precise_duration`](Precision::precise_duration).
    /// 
    /// # Panics
    /// 
    /// Panics if [`Precision`]'s invariants are not respected, i.e. the stored precision is zero.
    #[must_use]
    pub fn precise_unsigned_nanos(&self, duration: u128) -> u128 {
        let precision_nanos = self.precision().as_nanos();
        let timestamp_rem = duration % precision_nanos;

        if timestamp_rem == 0 { // Already rounded, no need to go to next anchor
            return duration;
        }

        let truncated_timestamp = duration - timestamp_rem;

        match self.mode() {
            PrecisionMode::ToNearest => {
                let precision_midpoint = precision_nanos / 2;

                if timestamp_rem.cmp(&precision_midpoint).is_ge() {
                    truncated_timestamp.saturating_add(precision_nanos)
                } else {
                    truncated_timestamp
                }
            },
            PrecisionMode::ToFuture => {
                truncated_timestamp.saturating_add(precision_nanos)
            },
            PrecisionMode::ToPast => {
                truncated_timestamp
            },
        }
    }

    /// Applies the precision to a given [`i128`] representing a duration
    /// 
    /// This operation is mostly designed for use by [`precise_signed_duration`](Precision::precise_signed_duration).
    /// 
    /// # Panics
    /// 
    /// Panics if [`Precision`]'s invariants are not respected, i.e. the stored precision is zero.
    #[must_use]
    pub fn precise_signed_nanos(&self, duration: i128) -> i128 {
        let precision_nanos = self.precision().as_nanos();
        let timestamp_rem = duration.unsigned_abs() % precision_nanos;

        if timestamp_rem == 0 { // Already rounded, no need to go to next anchor
            return duration;
        }

        // How much needs to be removed to get to the past anchor
        let timestamp_diff_to_past = match duration.signum() {
            1 => timestamp_rem,
            0 => 0,
            -1 => precision_nanos - timestamp_rem,
            _ => unreachable!("core::num::signum is guaranteed to return only in the range -1..=1"),
        };

        let truncated_timestamp = duration.saturating_sub_unsigned(timestamp_diff_to_past);

        match self.mode() {
            PrecisionMode::ToNearest => {
                let precision_midpoint = precision_nanos / 2;

                if timestamp_diff_to_past.cmp(&precision_midpoint).is_ge() {
                    truncated_timestamp.saturating_add_unsigned(precision_nanos)
                } else {
                    truncated_timestamp
                }
            },
            PrecisionMode::ToFuture => {
                truncated_timestamp.saturating_add_unsigned(precision_nanos)
            },
            PrecisionMode::ToPast => {
                truncated_timestamp
            },
        }
    }

    /// Applies the precision to a given [`Duration`](StdDuration)
    /// 
    /// Since a duration is relative, rounding is based on the multiple of the precision's duration.
    /// 
    /// # Errors
    /// 
    /// Returns [`OutOfRangeDate`](PrecisionError::OutOfRangeDate) if the computed new duration
    /// has an amount of seconds superior to what [`u64`] can store.
    /// 
    /// # Panics
    /// 
    /// Panics if [`Precision`]'s invariants are not respected, i.e. the stored precision is zero.
    /// 
    /// # Examples
    /// 
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// let precision = Precision::new(Duration::from_mins(15), PrecisionMode::ToPast)?;
    /// 
    /// assert_eq!(
    ///     precision.precise_duration(Duration::from_mins(77))?,
    ///     Duration::from_mins(75),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn precise_duration(&self, duration: StdDuration) -> Result<StdDuration, PrecisionError> {
        let new_timestamp = self.precise_unsigned_nanos(duration.as_nanos());

        // Polyfill for StdDuration::from_nanos_u128() to avoid bumping MSRV
        // & StdDuration::try_from_nanos_u128() doesn't yet exist
        let nanos_per_sec = StdDuration::from_secs(1).as_nanos();
        let secs_component = u64::try_from(new_timestamp / nanos_per_sec)
            .or(Err(PrecisionError::OutOfRangeDate))?;
        let nanos_component = u32::try_from(new_timestamp % nanos_per_sec)
            .or(Err(PrecisionError::OutOfRangeDate))?;

        Ok(StdDuration::new(secs_component, nanos_component))
    }

    /// Applies the precision to a given [`SignedDuration`]
    /// 
    /// Since a duration is relative, rounding is based on the multiple of the precision's duration.
    /// 
    /// # Errors
    /// 
    /// Returns [`OutOfRangeDate`](PrecisionError::OutOfRangeDate) if the computed new duration
    /// exceeded what [`i128`] can store.
    /// 
    /// # Panics
    /// 
    /// Panics if [`Precision`]'s invariants are not respected, i.e. the stored precision is zero.
    /// 
    /// # Examples
    /// 
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// let precision = Precision::new(Duration::from_mins(15), PrecisionMode::ToFuture)?;
    /// 
    /// assert_eq!(
    ///     precision.precise_signed_duration(SignedDuration::from_mins(-44))?,
    ///     SignedDuration::from_mins(-30),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn precise_signed_duration(&self, signed_duration: SignedDuration) -> Result<SignedDuration, PrecisionError> {
        Ok(SignedDuration::from_nanos_i128(self.precise_signed_nanos(signed_duration.as_nanos())))
    }

    /// Applies the precision to the given time
    ///
    /// If the precision is not a divisor of 24 hours, the rounded times would differ from one day to another,
    /// as the rounding would be based on the [Unix time][1], which begins on `1970-01-01`.
    /// 
    /// Instead, this method assumes this is not your intention and that you instead want to round
    /// the displayed clock time to the duration.
    /// See [`precise_time_with_base_time`](Precision::precise_time_with_base_time) if this is does not match
    /// your desired behavior.
    ///
    /// This method applies the rounding based on the time's date and temporarily assumes a linear timezone: UTC.
    /// This assumption is to avoid unexpected rounded values that would occur when taking into account
    /// the given time's timezone.
    /// 
    /// For example, if the time's date occurs the day the timezone _rolls back_ one hour, rounding based
    /// on a higher value than the timezone's change, e.g. 2 hours, would look weird: the rounded times
    /// would result in even hours before the timezone's change, then would result in odd hours.
    /// 
    /// This is precisely why this method returns an [`AmbiguousZoned`]: since we are applying
    /// the original timezone back on the rounded time (that was transferred to UTC), then we are not able
    /// to know if this time within the original timezone actually exists or whether it belongs to a time
    /// before/after a timezone change. We instead leave the disambiguation method up to the caller.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeDate`](PrecisionError::OutOfRangeDate) if the transfer to UTC would represent
    /// a timestamp too small to be stored correctly or if the resulting time would result in a time that
    /// cannot be stored in [`Zoned`].
    /// 
    /// # Panics
    /// 
    /// Panics if [`Precision`]'s invariants are not respected, i.e. the stored precision is zero.
    /// 
    /// # Examples
    /// 
    /// ## Simple rounding
    /// 
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// let precision = Precision::new(Duration::from_hours(2), PrecisionMode::ToFuture)?;
    /// let time = "2026-01-01 07:52:46[Europe/Oslo]".parse::<Zoned>()?;
    /// 
    /// assert_eq!(
    ///     precision.precise_time(&time)?.unambiguous()?,
    ///     "2026-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    /// 
    /// ## Rounding on a DST day
    /// 
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// let precision = Precision::new(Duration::from_mins(30), PrecisionMode::ToFuture)?;
    /// let ok_time = "2026-03-29 07:52:46[Europe/Oslo]".parse::<Zoned>()?;
    /// let gap_time = "2026-03-29 01:55:34[Europe/Oslo]".parse::<Zoned>()?;
    /// 
    /// assert_eq!(
    ///     precision.precise_time(&ok_time)?.unambiguous()?,
    ///     "2026-03-29 08:00:00[Europe/Oslo]".parse::<Zoned>()?,
    /// );
    /// 
    /// // since rounding 01:55:34 would end up at 02:00:00, which is when DST starts in this timezone,
    /// // trying to disambiguate the time using the reject strategy will return an error.
    /// assert!(precision.precise_time(&gap_time)?.unambiguous().is_err());
    /// // but if we really want a result, we can use the compatible strategy
    /// assert_eq!(
    ///     precision.precise_time(&gap_time)?.compatible()?,
    ///     // first time after DST time gap
    ///     "2026-03-29 03:00:00[Europe/Oslo]".parse::<Zoned>()?,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    /// 
    /// ## A time already rounded won't change
    /// 
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// let precision = Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?;
    /// let time = "2026-01-01 08:45:00[Europe/Oslo]".parse::<Zoned>()?;
    /// 
    /// assert_eq!(
    ///     precision.precise_time(&time)?.unambiguous()?,
    ///     time,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    ///
    /// [1]: https://en.wikipedia.org/w/index.php?title=Unix_time&useskin=vector
    pub fn precise_time(&self, zoned_time: &Zoned) -> Result<AmbiguousZoned, PrecisionError> {
        let utc_day_start = zoned_time
            .datetime()
            .start_of_day()
            .to_zoned(TimeZone::UTC)
            .or(Err(PrecisionError::OutOfRangeDate))?;
        let duration_diff = zoned_time
            .datetime()
            .to_zoned(TimeZone::UTC)
            .or(Err(PrecisionError::OutOfRangeDate))?
            .timestamp()
            .duration_since(utc_day_start.timestamp());
        let precised_datetime = utc_day_start
            .checked_add(self.precise_signed_duration(duration_diff)?)
            .or(Err(PrecisionError::OutOfRangeDate))?
            .datetime();

        Ok(zoned_time.time_zone().to_ambiguous_zoned(precised_datetime))
    }

    /// Applies the precision to the given time based on a given time base
    ///
    /// If the precision is not a divisor of 24 hours, the rounded times will differ from one day to another,
    /// as the rounding will be based on the [Unix time][1], which begins on `1970-01-01`.
    /// 
    /// Giving a base allows you to solve this issue by giving away control on which base time is actually
    /// used. It is also useful for dealing with timezone changes, as timezone changes can introduce/remove
    /// amounts of time from the used time scale, meaning that the rounded result could end up with
    /// an unexpected clock time, but duration-wise with regards to the given base would match the desired
    /// rounding.
    /// 
    /// If instead you want rounding based on clock time, see [`precise_time`](Precision::precise_time).
    /// 
    /// This method takes an timezone as an argument. This timezone will be used to convert the given
    /// time and base, as theoretically they could be in different timezones, which would lead to an ambiguous
    /// computation. Since this timezone argument is optional, if [`None`] is provided, the timezone of
    /// the given base time will be used.
    ///
    /// # Errors
    ///
    /// Returns [`OutOfRangeDate`](PrecisionError::OutOfRangeDate) if the resulting time would result in a time that
    /// cannot be stored in [`Zoned`].
    /// 
    /// # Panics
    /// 
    /// Panics if [`Precision`]'s invariants are not respected, i.e. the stored precision is zero.
    ///
    /// # Examples
    /// 
    /// ## Duration-wise rounding on a DST day
    /// 
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// let precision = Precision::new(Duration::from_hours(2), PrecisionMode::ToFuture)?;
    /// let time = "2026-03-29 07:55:02[Europe/Oslo]".parse::<Zoned>()?;
    /// let base = time.start_of_day()?;
    /// 
    /// assert_eq!(
    ///     precision.precise_time_with_base_time(&time, &base, None)?,
    ///     "2026-03-29 09:00:00[Europe/Oslo]".parse::<Zoned>()?,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    /// 
    /// ## Rounding using a non-24-hours divisor
    /// 
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// let precision = Precision::new(Duration::from_mins(22), PrecisionMode::ToFuture)?;
    /// let time = "2026-01-02 07:55:02[Europe/Oslo]".parse::<Zoned>()?;
    /// let base = "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?;
    /// 
    /// assert_eq!(
    ///     precision.precise_time_with_base_time(&time, &base, None)?,
    ///     "2026-01-02 08:16:00[Europe/Oslo]".parse::<Zoned>()?,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    ///
    /// [1]: https://en.wikipedia.org/w/index.php?title=Unix_time&useskin=vector
    pub fn precise_time_with_base_time(
        &self,
        time: &Zoned,
        base: &Zoned,
        tz: Option<TimeZone>,
    ) -> Result<Zoned, PrecisionError> {
        let tz = tz.unwrap_or_else(|| base.time_zone().clone());
        let time = time.with_time_zone(tz.clone());
        let base = base.with_time_zone(tz);

        dbg!(&time, &base);

        base
            .checked_add(self.precise_signed_duration(time.duration_since(&base))?)
            .map_err(|_| PrecisionError::OutOfRangeDate)
    }
}

/// Errors that can be produced when creating a [`Precision`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrecisionCreationError {
    /// Duration given as a precision is zero
    PrecisionIsZero,
}

impl Display for PrecisionCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PrecisionIsZero => write!(f, "Duration given as a precision is zero"),
        }
    }
}

impl Error for PrecisionCreationError {}

/// Errors that can be produced when using [`Precision`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrecisionError {
    /// An operation produced an out-of-range date
    OutOfRangeDate,
}

impl Display for PrecisionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRangeDate => write!(f, "Operation produced an out-of-range date"),
        }
    }
}

impl Error for PrecisionError {}

/// Represents a running result
///
/// If returning an unfinished result, for example from an iterator, is useful, this enumerator helps with
/// determining the state of the running result.
///
/// It is currently not used in `periodical` and therefore may be subject to deletion in the future.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RunningResult<R, D = R> {
    /// Result is unfinished
    ///
    /// Current progress is stored in this variant.
    Running(R),
    /// Result is ready
    ///
    /// Result is stored in this variant.
    Done(D),
}

impl<R, D> RunningResult<R, D> {
    /// Whether the running result is the variant [`Running`](RunningResult::Running)
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::RunningResult;
    /// assert!(RunningResult::<()>::Running(()).is_running());
    /// assert!(!RunningResult::<()>::Done(()).is_running());
    /// ```
    pub fn is_running(&self) -> bool {
        matches!(self, Self::Running(_))
    }

    /// Whether the running result is the variant [`Done`](RunningResult::Done)
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::RunningResult;
    /// assert!(RunningResult::<()>::Done(()).is_done());
    /// assert!(!RunningResult::<()>::Running(()).is_done());
    /// ```
    pub fn is_done(&self) -> bool {
        matches!(self, Self::Done(_))
    }

    /// Returns the content of the [`Running`](RunningResult::Running) variant
    ///
    /// This operation consumes `self` and puts the content of the [`Running`](RunningResult::Running) variant
    /// in an [`Option`]. If instead `self` is another variant, this method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::RunningResult;
    /// assert_eq!(RunningResult::<u8>::Running(10).running(), Some(10));
    /// assert_eq!(RunningResult::<u8>::Done(10).running(), None);
    /// ```
    #[must_use]
    pub fn running(self) -> Option<R> {
        match self {
            Self::Running(r) => Some(r),
            Self::Done(_) => None,
        }
    }

    /// Returns the content of the [`Done`](RunningResult::Done) variant
    ///
    /// This operation consumes `self` and puts the content of the [`Done`](RunningResult::Done) variant
    /// in an [`Option`]. If instead `self` is another variant, this method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::RunningResult;
    /// assert_eq!(RunningResult::<u8>::Done(10).done(), Some(10));
    /// assert_eq!(RunningResult::<u8>::Running(10).done(), None);
    /// ```
    #[must_use]
    pub fn done(self) -> Option<D> {
        match self {
            Self::Running(_) => None,
            Self::Done(d) => Some(d),
        }
    }

    /// Maps the contents of the [`Running`](RunningResult::Running) variant
    ///
    /// If `self` is another variant, the method returns `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::RunningResult;
    /// assert_eq!(
    ///     RunningResult::<u8>::Running(10).map_running(|x| x * 2),
    ///     RunningResult::<u8>::Running(20),
    /// );
    /// assert_eq!(
    ///     RunningResult::<u8>::Done(10).map_running(|x| x * 2),
    ///     RunningResult::<u8>::Done(10),
    /// );
    /// ```
    pub fn map_running<F, T>(self, f: F) -> RunningResult<T, D>
    where
        F: FnOnce(R) -> T,
    {
        match self {
            Self::Running(r) => RunningResult::Running((f)(r)),
            Self::Done(d) => RunningResult::Done(d),
        }
    }

    /// Maps the contents of the [`Done`](RunningResult::Done) variant
    ///
    /// If `self` is another variant, the method returns `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::RunningResult;
    /// assert_eq!(
    ///     RunningResult::<u8>::Done(10).map_done(|x| x * 2),
    ///     RunningResult::<u8>::Done(20),
    /// );
    /// assert_eq!(
    ///     RunningResult::<u8>::Running(10).map_done(|x| x * 2),
    ///     RunningResult::<u8>::Running(10),
    /// );
    /// ```
    pub fn map_done<F, T>(self, f: F) -> RunningResult<R, T>
    where
        F: FnOnce(D) -> T,
    {
        match self {
            Self::Running(r) => RunningResult::Running(r),
            Self::Done(d) => RunningResult::Done((f)(d)),
        }
    }
}

/// Represents the result of a [complement][1]
///
/// [1]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum ComplementResult<C> {
    /// Complement was successful and resulted in a single element
    Single(C),
    /// Complement was successful and resulted in two elements
    Split(C, C),
}

impl<C> ComplementResult<C> {
    /// Whether the [`ComplementResult`] is of the [`Single`](ComplementResult::Single) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::ComplementResult;
    /// assert!(ComplementResult::<u8>::Single(10).is_single());
    /// assert!(!ComplementResult::<u8>::Split(10, 20).is_single());
    /// ```
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Whether the [`ComplementResult`] is of the [`Split`](ComplementResult::Split) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::ComplementResult;
    /// assert!(ComplementResult::<u8>::Split(10, 20).is_split());
    /// assert!(!ComplementResult::<u8>::Single(10).is_split());
    /// ```
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Returns the content of the [`Single`](ComplementResult::Single) variant
    ///
    /// This operation consumes `self` and puts the content of the [`Single`](ComplementResult::Single) variant
    /// in an [`Option`]. If instead `self` is another variant, this method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::ComplementResult;
    /// assert_eq!(ComplementResult::<u8>::Single(10).single(), Some(10));
    /// assert_eq!(ComplementResult::<u8>::Split(10, 20).single(), None);
    /// ```
    #[must_use]
    pub fn single(self) -> Option<C> {
        match self {
            Self::Single(s) => Some(s),
            Self::Split(..) => None,
        }
    }

    /// Returns the content of the [`Split`](ComplementResult::Split) variant
    ///
    /// This operation consumes `self` and puts the content of the [`Split`](ComplementResult::Split) variant
    /// in an [`Option`]. If instead `self` is another variant, this method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::ComplementResult;
    /// assert_eq!(ComplementResult::<u8>::Split(10, 20).split(), Some((10, 20)));
    /// assert_eq!(ComplementResult::<u8>::Single(10).split(), None);
    /// ```
    #[must_use]
    pub fn split(self) -> Option<(C, C)> {
        match self {
            Self::Single(_) => None,
            Self::Split(s1, s2) => Some((s1, s2)),
        }
    }

    /// Maps the contents of the variants using the given transformation closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::ComplementResult;
    /// assert_eq!(
    ///     ComplementResult::<u8>::Single(10).map(|x| x * 2),
    ///     ComplementResult::<u8>::Single(20),
    /// );
    /// assert_eq!(
    ///     ComplementResult::<u8>::Split(10, 20).map(|x| x * 2),
    ///     ComplementResult::<u8>::Split(20, 40),
    /// );
    /// ```
    pub fn map<F, T>(self, mut f: F) -> ComplementResult<T>
    where
        F: FnMut(C) -> T,
    {
        match self {
            Self::Single(c) => ComplementResult::Single((f)(c)),
            Self::Split(c1, c2) => ComplementResult::Split((f)(c1), (f)(c2)),
        }
    }
}

/// Represents the result of a [union][1]
///
/// [1]: https://en.wikipedia.org/w/index.php?title=Union_(set_theory)&oldid=1309419266
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum UnionResult<U> {
    /// Union was successful, the united element is contained within this variant
    United(U),
    /// Union was unsuccessful
    Separate,
}

impl<U> UnionResult<U> {
    /// Whether the [`UnionResult`] is of the [`United`](UnionResult::United) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::UnionResult;
    /// assert!(UnionResult::<u8>::United(10).is_united());
    /// assert!(!UnionResult::<u8>::Separate.is_united());
    /// ```
    pub fn is_united(&self) -> bool {
        matches!(self, Self::United(_))
    }

    /// Whether the [`UnionResult`] is of the [`Separate`](UnionResult::Separate) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::UnionResult;
    /// assert!(UnionResult::<u8>::Separate.is_separate());
    /// assert!(!UnionResult::<u8>::United(10).is_separate());
    /// ```
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`United`](UnionResult::United) variant
    ///
    /// Consumes `self` and puts the content of the [`United`](UnionResult::United) variant
    /// in an [`Option`]. If instead `self` is another variant, this method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::UnionResult;
    /// assert_eq!(UnionResult::<u8>::United(10).united(), Some(10));
    /// assert_eq!(UnionResult::<u8>::Separate.united(), None);
    /// ```
    #[must_use]
    pub fn united(self) -> Option<U> {
        match self {
            Self::United(u) => Some(u),
            Self::Separate => None,
        }
    }

    /// Maps the contents of the [`United`](UnionResult::United) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::UnionResult;
    /// assert_eq!(
    ///     UnionResult::<u8>::United(10).map_united(|x| x * 2),
    ///     UnionResult::<u8>::United(20),
    /// );
    /// ```
    pub fn map_united<F, T>(self, f: F) -> UnionResult<T>
    where
        F: FnOnce(U) -> T,
    {
        match self {
            UnionResult::United(u) => UnionResult::United((f)(u)),
            UnionResult::Separate => UnionResult::Separate,
        }
    }
}

/// Represents the result of an [intersection][1]
///
/// [1]: https://en.wikipedia.org/w/index.php?title=Intersection_(set_theory)&oldid=1191979994
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum IntersectionResult<I> {
    /// Intersection was successful, the intersected element is contained within this variant
    Intersected(I),
    /// Intersection was unsuccessful
    Separate,
}

impl<I> IntersectionResult<I> {
    /// Whether the [`IntersectionResult`] is of the [`Intersected`](IntersectionResult::Intersected) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::IntersectionResult;
    /// assert!(IntersectionResult::<u8>::Intersected(10).is_intersected());
    /// assert!(!IntersectionResult::<u8>::Separate.is_intersected());
    /// ```
    pub fn is_intersected(&self) -> bool {
        matches!(self, Self::Intersected(_))
    }

    /// Whether the [`IntersectionResult`] is of the [`Separate`](IntersectionResult::Separate) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::IntersectionResult;
    /// assert!(IntersectionResult::<u8>::Separate.is_separate());
    /// assert!(!IntersectionResult::<u8>::Intersected(10).is_separate());
    /// ```
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`Intersected`](IntersectionResult::Intersected) variant
    ///
    /// Consumes `self` and puts the content of the [`Intersected`](IntersectionResult::Intersected) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::IntersectionResult;
    /// assert_eq!(
    ///     IntersectionResult::<u8>::Intersected(10).intersected(),
    ///     Some(10),
    /// );
    /// assert_eq!(
    ///     IntersectionResult::<u8>::Separate.intersected(),
    ///     None,
    /// );
    /// ```
    #[must_use]
    pub fn intersected(self) -> Option<I> {
        match self {
            Self::Intersected(i) => Some(i),
            Self::Separate => None,
        }
    }

    /// Maps the contents of the [`Intersected`](IntersectionResult::Intersected) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::IntersectionResult;
    /// assert_eq!(
    ///     IntersectionResult::<u8>::Intersected(10).map_intersected(|x| x * 2),
    ///     IntersectionResult::<u8>::Intersected(20),
    /// );
    /// ```
    pub fn map_intersected<F, T>(self, f: F) -> IntersectionResult<T>
    where
        F: FnOnce(I) -> T,
    {
        match self {
            Self::Intersected(i) => IntersectionResult::Intersected((f)(i)),
            Self::Separate => IntersectionResult::Separate,
        }
    }
}

/// Represents the result of a [difference][1]
///
/// [1]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum DifferenceResult<D> {
    /// Difference was successful and resulted in one single element
    Single(D),
    /// Difference was successful and resulted in two split elements
    Split(D, D),
    /// Difference was unsuccessful
    Separate,
}

impl<D> DifferenceResult<D> {
    /// Whether the [`DifferenceResult`] is of the [`Single`](DifferenceResult::Single) or
    /// [`Split`](DifferenceResult::Split) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::DifferenceResult;
    /// assert!(DifferenceResult::<u8>::Single(10).is_difference());
    /// assert!(DifferenceResult::<u8>::Split(10, 20).is_difference());
    /// assert!(!DifferenceResult::<u8>::Separate.is_difference());
    /// ```
    pub fn is_difference(&self) -> bool {
        matches!(self, Self::Single(_) | Self::Split(..))
    }

    /// Whether the [`DifferenceResult`] is of the [`Single`](DifferenceResult::Single) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::DifferenceResult;
    /// assert!(DifferenceResult::<u8>::Single(10).is_difference_single());
    /// assert!(!DifferenceResult::<u8>::Split(10, 20).is_difference_single());
    /// assert!(!DifferenceResult::<u8>::Separate.is_difference_single());
    /// ```
    pub fn is_difference_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Whether the [`DifferenceResult`] is of the [`Split`](DifferenceResult::Split) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::DifferenceResult;
    /// assert!(DifferenceResult::<u8>::Split(10, 20).is_difference_split());
    /// assert!(!DifferenceResult::<u8>::Single(10).is_difference_split());
    /// assert!(!DifferenceResult::<u8>::Separate.is_difference_split());
    /// ```
    pub fn is_difference_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Whether the [`DifferenceResult`] is of the [`Separate`](DifferenceResult::Separate) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::DifferenceResult;
    /// assert!(DifferenceResult::<u8>::Separate.is_separate());
    /// assert!(!DifferenceResult::<u8>::Single(10).is_separate());
    /// assert!(!DifferenceResult::<u8>::Split(10, 20).is_separate());
    /// ```
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`Single`](DifferenceResult::Single) variant
    ///
    /// Consumes `self` and puts the content of the [`Single`](DifferenceResult::Single) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::DifferenceResult;
    /// assert_eq!(DifferenceResult::<u8>::Single(10).single(), Some(10));
    /// assert_eq!(DifferenceResult::<u8>::Split(10, 20).single(), None);
    /// assert_eq!(DifferenceResult::<u8>::Separate.single(), None);
    /// ```
    #[must_use]
    pub fn single(self) -> Option<D> {
        match self {
            Self::Single(s) => Some(s),
            Self::Split(..) | Self::Separate => None,
        }
    }

    /// Returns the content of the [`Split`](DifferenceResult::Split) variant
    ///
    /// Consumes `self` and puts the content of the [`Split`](DifferenceResult::Split) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::DifferenceResult;
    /// assert_eq!(DifferenceResult::<u8>::Split(10, 20).split(), Some((10, 20)));
    /// assert_eq!(DifferenceResult::<u8>::Single(10).split(), None);
    /// assert_eq!(DifferenceResult::<u8>::Separate.split(), None);
    /// ```
    #[must_use]
    pub fn split(self) -> Option<(D, D)> {
        match self {
            Self::Split(s1, s2) => Some((s1, s2)),
            Self::Single(_) | Self::Separate => None,
        }
    }

    /// Maps the contents of the [`Single`](DifferenceResult::Single) and [`Split`](DifferenceResult::Split) variants
    ///
    /// Uses a closure that describes the transformation from the original difference elements to the transformed ones.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::DifferenceResult;
    /// assert_eq!(
    ///     DifferenceResult::<u8>::Single(10).map_difference(|x| x * 2),
    ///     DifferenceResult::<u8>::Single(20),
    /// );
    /// assert_eq!(
    ///     DifferenceResult::<u8>::Split(10, 20).map_difference(|x| x * 2),
    ///     DifferenceResult::<u8>::Split(20, 40),
    /// );
    /// ```
    pub fn map_difference<F, T>(self, mut f: F) -> DifferenceResult<T>
    where
        F: FnMut(D) -> T,
    {
        match self {
            Self::Single(d) => DifferenceResult::Single((f)(d)),
            Self::Split(d1, d2) => DifferenceResult::Split((f)(d1), (f)(d2)),
            Self::Separate => DifferenceResult::Separate,
        }
    }
}

/// Represents the result of a [symmetric difference][1]
///
/// [1]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1300584821
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum SymmetricDifferenceResult<D> {
    /// Symmetric difference was successful and resulted in one single element
    Single(D),
    /// Symmetric difference was successful and resulted in two split elements
    Split(D, D),
    /// Symmetric difference was unsuccessful
    Separate,
}

impl<D> SymmetricDifferenceResult<D> {
    /// Whether the [`SymmetricDifferenceResult`] is of the [`Single`](SymmetricDifferenceResult::Single)
    /// or [`Split`](SymmetricDifferenceResult::Split) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// assert!(SymmetricDifferenceResult::<u8>::Single(10).is_symmetric_difference());
    /// assert!(SymmetricDifferenceResult::<u8>::Split(10, 20).is_symmetric_difference());
    /// assert!(!SymmetricDifferenceResult::<u8>::Separate.is_symmetric_difference());
    /// ```
    pub fn is_symmetric_difference(&self) -> bool {
        matches!(self, Self::Single(_) | Self::Split(..))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Single`](SymmetricDifferenceResult::Single) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// assert!(SymmetricDifferenceResult::<u8>::Single(10).is_single());
    /// assert!(!SymmetricDifferenceResult::<u8>::Split(10, 20).is_single());
    /// assert!(!SymmetricDifferenceResult::<u8>::Separate.is_single());
    /// ```
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Split`](SymmetricDifferenceResult::Split) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// assert!(SymmetricDifferenceResult::<u8>::Split(10, 20).is_split());
    /// assert!(!SymmetricDifferenceResult::<u8>::Single(10).is_split());
    /// assert!(!SymmetricDifferenceResult::<u8>::Separate.is_split());
    /// ```
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Separate`](SymmetricDifferenceResult::Separate) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// assert!(SymmetricDifferenceResult::<u8>::Separate.is_separate());
    /// assert!(!SymmetricDifferenceResult::<u8>::Single(10).is_separate());
    /// assert!(!SymmetricDifferenceResult::<u8>::Split(10, 20).is_separate());
    /// ```
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`Single`](SymmetricDifferenceResult::Single) variant
    ///
    /// Consumes `self` and puts the content of the [`Single`](SymmetricDifferenceResult::Single) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Single(10).single(),
    ///     Some(10),
    /// );
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Split(10, 20).single(),
    ///     None,
    /// );
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Separate.single(),
    ///     None,
    /// );
    /// ```
    #[must_use]
    pub fn single(self) -> Option<D> {
        match self {
            Self::Single(s) => Some(s),
            Self::Split(..) | Self::Separate => None,
        }
    }

    /// Returns the content of the [`Split`](SymmetricDifferenceResult::Split) variant
    ///
    /// Consumes `self` and puts the content of the [`Split`](SymmetricDifferenceResult::Split) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Split(10, 20).split(),
    ///     Some((10, 20)),
    /// );
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Single(10).split(),
    ///     None,
    /// );
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Separate.split(),
    ///     None,
    /// );
    /// ```
    #[must_use]
    pub fn split(self) -> Option<(D, D)> {
        match self {
            Self::Split(s1, s2) => Some((s1, s2)),
            Self::Single(_) | Self::Separate => None,
        }
    }

    /// Maps the contents of the [`Single`](SymmetricDifferenceResult::Single)
    /// and [`Split`](SymmetricDifferenceResult::Split) variants
    ///
    /// Uses a closure that describes the transformation from the original difference elements to the transformed ones.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::ops::SymmetricDifferenceResult;
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Single(10).map_symmetric_difference(|x| x * 2),
    ///     SymmetricDifferenceResult::<u8>::Single(20),
    /// );
    /// assert_eq!(
    ///     SymmetricDifferenceResult::<u8>::Split(10, 20).map_symmetric_difference(|x| x * 2),
    ///     SymmetricDifferenceResult::<u8>::Split(20, 40),
    /// );
    /// ```
    pub fn map_symmetric_difference<F, T>(self, mut f: F) -> SymmetricDifferenceResult<T>
    where
        F: FnMut(D) -> T,
    {
        match self {
            Self::Single(d) => SymmetricDifferenceResult::Single((f)(d)),
            Self::Split(d1, d2) => SymmetricDifferenceResult::Split((f)(d1), (f)(d2)),
            Self::Separate => SymmetricDifferenceResult::Separate,
        }
    }
}

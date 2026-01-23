//! Generic operation-related structures
//!
//! This module contains [`Precision`], [`RunningResult`] and set operations result structures.
//!
//! Those structures are not part of [`intervals::ops`](crate::intervals::ops) as they are not related to intervals
//! and can be used in other contexts.

use std::error::Error;
use std::fmt::Display;

use chrono::{DateTime, Duration, DurationRound, RoundingError, Utc};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Precision to use for re-precising times and intervals
///
/// The precision describes ways to _round_ a time or interval bound in a given manner: Round up, down, or nearest.
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
/// # Examples
///
/// ## Rounding to the nearest 5 minutes
///
/// ```
/// # use chrono::{DateTime, Duration, Utc};
/// # use periodical::ops::Precision;
/// let round_to_nearest_five_mins = Precision::ToNearest(Duration::minutes(5));
///
/// let two_minutes_after_eight = "2025-01-01 08:02:11Z".parse::<DateTime<Utc>>()?;
/// let fourteen_minutes_after_ten = "2025-01-01 10:14:21Z".parse::<DateTime<Utc>>()?;
///
/// assert_eq!(
///     round_to_nearest_five_mins.precise_time(two_minutes_after_eight),
///     Ok("2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?),
/// );
///
/// assert_eq!(
///     round_to_nearest_five_mins.precise_time(fourteen_minutes_after_ten),
///     Ok("2025-01-01 10:15:00Z".parse::<DateTime<Utc>>()?),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
///
/// ## Rounding up every 35 minutes with a given base time
///
/// ```
/// # use chrono::{DateTime, Duration, Utc};
/// # use periodical::ops::Precision;
/// let round_up_every_35_mins = Precision::ToFuture(Duration::minutes(35));
///
/// let first_january_2025 = "2025-01-01 00:00:00Z".parse::<DateTime<Utc>>()?; // our base time
/// let two_minutes_after_eight = "2025-01-01 08:02:11Z".parse::<DateTime<Utc>>()?;
/// let fourteen_minutes_after_ten = "2025-01-01 10:14:21Z".parse::<DateTime<Utc>>()?;
///
/// // 13 * 35m = 07:35
/// // 14 * 35m = 08:10
/// assert_eq!(
///     round_up_every_35_mins.precise_time_with_base_time(
///         two_minutes_after_eight,
///         first_january_2025,
///     ),
///     Ok("2025-01-01 08:10:00Z".parse::<DateTime<Utc>>()?),
/// );
///
/// // 17 * 35m = 09:55
/// // 18 * 35m = 10:30
/// assert_eq!(
///     round_up_every_35_mins.precise_time_with_base_time(
///         fourteen_minutes_after_ten,
///         first_january_2025,
///     ),
///     Ok("2025-01-01 10:30:00Z".parse::<DateTime<Utc>>()?),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum Precision {
    /// Rounds the compared times to the given duration
    ToNearest(Duration),
    /// Ceils/Rounds up the compared times to the given duration
    ToFuture(Duration),
    /// Floors/Rounds down the compared times to the given duration
    ToPast(Duration),
}

/// Errors that can be produced when using [`Precision`]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrecisionError {
    /// A rounding error happened, see `chrono`'s [`RoundingError`]
    RoundingError(RoundingError),
    /// An operation produced an out-of-range date
    OutOfRangeDate,
}

impl Display for PrecisionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RoundingError(rounding_err) => rounding_err.fmt(f),
            Self::OutOfRangeDate => write!(f, "Operation produced an out-of-range date"),
        }
    }
}

impl Error for PrecisionError {}

impl Precision {
    /// Uses the given precision to precise the given time
    ///
    /// # Pitfalls
    ///
    /// If the precision is not a divisor of 24 hours, the rounded times will differ from one day to another, as
    /// the rounding is based on the [Unix time](https://en.wikipedia.org/w/index.php?title=Unix_time&useskin=vector),
    /// which begins on `1970-01-01`.
    ///
    /// If you instead want to use your own base time, which is often way more practical,
    /// use [`precise_time_with_base_time`](Precision::precise_time_with_base_time).
    ///
    /// # Errors
    ///
    /// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
    /// if the given duration used is too big, negative or zero, etc.
    ///
    /// For more details, check [`chrono`'s limitations on the `DurationRound` trait][1].
    ///
    /// [1]: https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations
    pub fn precise_time(&self, time: DateTime<Utc>) -> Result<DateTime<Utc>, PrecisionError> {
        match self {
            Self::ToNearest(duration) => time.duration_round(*duration).map_err(PrecisionError::RoundingError),
            Self::ToFuture(duration) => time.duration_round_up(*duration).map_err(PrecisionError::RoundingError),
            Self::ToPast(duration) => time.duration_trunc(*duration).map_err(PrecisionError::RoundingError),
        }
    }

    /// Uses the given precision to precise the given time using the given base
    ///
    /// Bases the given time on the given base time before precising the time, that way you can use [`Duration`]s
    /// within your [`Precision`] that are not divisor of 24 hours without unexpected results.
    ///
    /// # Errors
    ///
    /// Rebasing times can lead to out-of-range dates, so if this method produces an out-of-range date, it will return
    /// the error [`OutOfRangeDate`](PrecisionError::OutOfRangeDate).
    ///
    /// Otherwise, precising/rounding a time can also lead to errors, for example if the given duration is negative
    /// or simply too large, so it will produce [`RoundingError`](PrecisionError::RoundingError) containing chrono's
    /// [`RoundingError`] within for more details.
    ///
    /// For more details, check [`chrono`'s limitations on the `DurationRound` trait][1].
    ///
    /// [1]: https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations
    pub fn precise_time_with_base_time(
        &self,
        time: DateTime<Utc>,
        base: DateTime<Utc>,
    ) -> Result<DateTime<Utc>, PrecisionError> {
        let unix_epoch_base_diff = base.signed_duration_since(DateTime::UNIX_EPOCH);
        let rebased_time = time
            .checked_sub_signed(unix_epoch_base_diff)
            .ok_or(PrecisionError::OutOfRangeDate)?;

        let precised_rebased_time = match self {
            Self::ToNearest(duration) => rebased_time.duration_round(*duration),
            Self::ToFuture(duration) => rebased_time.duration_round_up(*duration),
            Self::ToPast(duration) => rebased_time.duration_trunc(*duration),
        };

        let precised_rebased_time = precised_rebased_time.map_err(PrecisionError::RoundingError)?;

        precised_rebased_time
            .checked_add_signed(unix_epoch_base_diff)
            .ok_or(PrecisionError::OutOfRangeDate)
    }
}

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

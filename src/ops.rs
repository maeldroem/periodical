//! Generic operations
//!
//! Here are operations as well as structures, enums etc. related to such operations that can be used
//! in a generic manner, i.e. they aren't specific to any feature or structure. That's why this file is separate
//! from [`intervals::ops`](crate::intervals::ops), which is for operations specialized in handling intervals and
//! can't be used (or can't be used as efficiently) for other structures.

use std::error::Error;
use std::fmt::Display;

use chrono::{DateTime, Duration, DurationRound, RoundingError, Utc};

/// Time precision used for comparisons
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Precision {
    /// Rounds the compared times to the given duration (e.g. if the duration is 1 second, the times will be rounded to the nearest second)
    ToNearest(Duration),
    /// Ceils the compared times to the given duration
    ToFuture(Duration),
    /// Floors the compared times to the given duration (e.g. if the duration is 5 minutes, the times will be floored to the 5-minutes part they are in)
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
            Self::RoundingError(rounding_err) => write!(f, "{rounding_err}"),
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
    /// which begins on 1970-01-01.
    ///
    /// If you instead want to use your own base time,
    /// use [`precise_time_with_base_time`](Precision::precise_time_with_base_time).
    ///
    /// # Errors
    ///
    /// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
    /// if the given duration used is too big, negative or zero, etc.
    ///
    /// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
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
    /// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
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
/// This enum is mostly used for iterators doing fold-like operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RunningResult<R, D = R> {
    Running(R),
    Done(D),
}

impl<R, D> RunningResult<R, D> {
    /// Whether the running result is the variant [`Running`](RunningResult::Running)
    pub fn is_running(&self) -> bool {
        matches!(self, Self::Running(_))
    }

    /// Whether the running result is the variant [`Done`](RunningResult::Done)
    pub fn is_done(&self) -> bool {
        matches!(self, Self::Done(_))
    }

    /// Converts the content of the [`Running`](RunningResult::Running) variant into an [`Option`]
    #[must_use]
    pub fn running(self) -> Option<R> {
        match self {
            Self::Running(r) => Some(r),
            Self::Done(_) => None,
        }
    }

    /// Converts the content of the [`Done`](RunningResult::Done) variant into an [`Option`]
    #[must_use]
    pub fn done(self) -> Option<D> {
        match self {
            Self::Running(_) => None,
            Self::Done(d) => Some(d),
        }
    }

    /// Maps the contents of the [`Running`](RunningResult::Running) variant
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

/// Represents the result of a complement
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ComplementResult<C> {
    /// Complement was successful and resulted in a single element
    Single(C),
    /// Complement was successful and resulted in two elements
    Split(C, C),
}

impl<C> ComplementResult<C> {
    /// Whether the [`ComplementResult`] is of the [`Single`](ComplementResult::Single) variant
    pub fn is_single(&self) -> bool {
        matches!(self, Self::Single(_))
    }

    /// Whether the [`ComplementResult`] is of the [`Split`](ComplementResult::Split) variant
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Converts the content of the [`Single`](ComplementResult::Single) variant into an [`Option`]
    #[must_use]
    pub fn single(self) -> Option<C> {
        match self {
            Self::Single(s) => Some(s),
            Self::Split(..) => None,
        }
    }

    /// Converts the content of the [`Split`](ComplementResult::Split) variant into an [`Option`]
    #[must_use]
    pub fn split(self) -> Option<(C, C)> {
        match self {
            Self::Single(_) => None,
            Self::Split(s1, s2) => Some((s1, s2)),
        }
    }

    /// Maps the contents of the variants using the given transformation closure
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

/// Represents the result of a union
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnionResult<U> {
    /// Union was successful, the united element is contained within this variant
    United(U),
    /// Union was unsuccessful
    Separate,
}

impl<U> UnionResult<U> {
    /// Whether the [`UnionResult`] is of the [`United`](UnionResult::United) variant
    pub fn is_united(&self) -> bool {
        matches!(self, Self::United(_))
    }

    /// Whether the [`UnionResult`] is of the [`Separate`](UnionResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`United`](UnionResult::United) variant
    #[must_use]
    pub fn united(self) -> Option<U> {
        match self {
            Self::United(u) => Some(u),
            Self::Separate => None,
        }
    }

    /// Maps the contents of the [`United`](UnionResult::United) variant
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

/// Represents the result of an intersection
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntersectionResult<I> {
    /// Intersection was successful, the intersected element is contained within this variant
    Intersected(I),
    /// Intersection was unsuccessful
    Separate,
}

impl<I> IntersectionResult<I> {
    /// Whether the [`IntersectionResult`] is of the [`Intersected`](IntersectionResult::Intersected) variant
    pub fn is_intersected(&self) -> bool {
        matches!(self, Self::Intersected(_))
    }

    /// Whether the [`IntersectionResult`] is of the [`Separate`](IntersectionResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`Intersected`](IntersectionResult::Intersected) variant
    #[must_use]
    pub fn intersected(self) -> Option<I> {
        match self {
            Self::Intersected(i) => Some(i),
            Self::Separate => None,
        }
    }

    /// Maps the contents of the [`Intersected`](IntersectionResult::Intersected) variant
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

/// Represents the result of a difference
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DifferenceResult<D> {
    /// Difference was successful and resulted in one shrunken element
    Shrunk(D),
    /// Difference was successful and resulted in two split elements
    Split(D, D),
    /// Difference was unsuccessful
    Separate,
}

impl<D> DifferenceResult<D> {
    /// Whether the [`DifferenceResult`] is of the [`Shrunk`](DifferenceResult::Shrunk) or
    /// [`Split`](DifferenceResult::Split) variant
    pub fn is_difference(&self) -> bool {
        matches!(self, Self::Shrunk(_) | Self::Split(..))
    }

    /// Whether the [`DifferenceResult`] is of the [`Shrunk`](DifferenceResult::Shrunk) variant
    pub fn is_difference_shrunk(&self) -> bool {
        matches!(self, Self::Shrunk(_))
    }

    /// Whether the [`DifferenceResult`] is of the [`Split`](DifferenceResult::Split) variant
    pub fn is_difference_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Whether the [`DifferenceResult`] is of the [`Separate`](DifferenceResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`Shrunk`](DifferenceResult::Shrunk) variant
    #[must_use]
    pub fn shrunk(self) -> Option<D> {
        match self {
            Self::Shrunk(s) => Some(s),
            Self::Split(..) | Self::Separate => None,
        }
    }

    /// Returns the content of the [`Split`](DifferenceResult::Split) variant
    #[must_use]
    pub fn split(self) -> Option<(D, D)> {
        match self {
            Self::Split(s1, s2) => Some((s1, s2)),
            Self::Shrunk(_) | Self::Separate => None,
        }
    }

    /// Maps the contents of the [`Shrunk`](DifferenceResult::Shrunk) and [`Split`](DifferenceResult::Split) variants
    ///
    /// Uses a closure that describes the transformation from the original difference elements to the transformed one.
    pub fn map_difference<F, T>(self, mut f: F) -> DifferenceResult<T>
    where
        F: FnMut(D) -> T,
    {
        match self {
            Self::Shrunk(d) => DifferenceResult::Shrunk((f)(d)),
            Self::Split(d1, d2) => DifferenceResult::Split((f)(d1), (f)(d2)),
            Self::Separate => DifferenceResult::Separate,
        }
    }
}

/// Represents the result of a symmetric difference
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymmetricDifferenceResult<D> {
    /// Symmetric difference was successful and resulted in one shrunken element
    Shrunk(D),
    /// Symmetric difference was successful and resulted in two split elements
    Split(D, D),
    /// Symmetric difference was unsuccessful
    Separate,
}

impl<D> SymmetricDifferenceResult<D> {
    /// Whether the [`SymmetricDifferenceResult`] is of the [`Shrunk`](SymmetricDifferenceResult::Shrunk)
    /// or [`Split`](SymmetricDifferenceResult::Split) variant
    pub fn has_symmetric_difference(&self) -> bool {
        matches!(self, Self::Shrunk(_) | Self::Split(..))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Shrunk`](SymmetricDifferenceResult::Shrunk) variant
    pub fn is_shrunk(&self) -> bool {
        matches!(self, Self::Shrunk(_))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Split`](SymmetricDifferenceResult::Split) variant
    pub fn is_split(&self) -> bool {
        matches!(self, Self::Split(..))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Separate`](SymmetricDifferenceResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Returns the content of the [`Shrunk`](SymmetricDifferenceResult::Shrunk) variant
    #[must_use]
    pub fn shrunk(self) -> Option<D> {
        match self {
            Self::Shrunk(s) => Some(s),
            Self::Split(..) | Self::Separate => None,
        }
    }

    /// Returns the content of the [`Split`](SymmetricDifferenceResult::Split) variant
    #[must_use]
    pub fn split(self) -> Option<(D, D)> {
        match self {
            Self::Split(s1, s2) => Some((s1, s2)),
            Self::Shrunk(_) | Self::Separate => None,
        }
    }

    /// Maps the contents of the [`Shrunk`](SymmetricDifferenceResult::Shrunk)
    /// and [`Split`](SymmetricDifferenceResult::Split) variants
    ///
    /// Uses a closure that describes the transformation from the original difference elements to the transformed one.
    pub fn map_symmetric_difference<F, T>(self, mut f: F) -> SymmetricDifferenceResult<T>
    where
        F: FnMut(D) -> T,
    {
        match self {
            Self::Shrunk(d) => SymmetricDifferenceResult::Shrunk((f)(d)),
            Self::Split(d1, d2) => SymmetricDifferenceResult::Split((f)(d1), (f)(d2)),
            Self::Separate => SymmetricDifferenceResult::Separate,
        }
    }
}

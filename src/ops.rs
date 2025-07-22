//! Generic operations
//!
//! Here are operations as well as structures, enums etc. related to such operations that can be used
//! in a generic manner, i.e. they aren't specific to any feature or structure. That's why this file is separate
//! from [`intervals::ops`](crate::intervals::ops), which is for operations specialized in handling intervals and
//! can't be used (or can't be used as efficiently) for other structures.

use chrono::{DateTime, Duration, DurationRound, RoundingError, Utc};

/// Time precision used for comparisons
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Precision {
    /// Rounds the compared times to the given duration (e.g. if the duration is 1 second, the times will be rounded to the nearest second)
    ToNearest(Duration),
    /// Floors the compared times to the given duration (e.g. if the duration is 5 minutes, the times will be floored to the 5-minutes part they are in)
    ToPast(Duration),
    /// Ceils the compared times to the given duration
    ToFuture(Duration),
}

impl Precision {
    /// Uses the given precision to precise the given time
    ///
    /// # Errors
    ///
    /// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
    /// if the given duration used is too big, negative or zero, etc.
    ///
    /// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
    pub fn precise_time(&self, time: DateTime<Utc>) -> Result<DateTime<Utc>, RoundingError> {
        match self {
            Self::ToNearest(duration) => time.duration_round(*duration),
            Self::ToPast(duration) => time.duration_trunc(*duration),
            Self::ToFuture(duration) => time.duration_round_up(*duration),
        }
    }
}

/// Represents a running result
///
/// This enum is mostly used for iterators doing fold-like operations.
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

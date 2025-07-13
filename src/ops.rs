//! Generic operations
//!
//! Here are operations as well as structures, enums etc. related to such operations that can be used
//! in a generic manner, i.e. they aren't specific to any feature or structure. That's why this file is separate
//! from [`intervals::ops`](crate::intervals::ops), which is for operations specialized in handling intervals and
//! can't be used (or can't be used as efficiently) for other structures.

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
    /// Difference was successful, the resulting element is contained within this variant
    Difference(D),
    /// Difference was unsuccessful
    Separate,
}

impl<D> DifferenceResult<D> {
    /// Whether the [`DifferenceResult`] is of the [`Difference`](DifferenceResult::Difference) variant
    pub fn is_difference(&self) -> bool {
        matches!(self, Self::Difference(_))
    }

    /// Whether the [`DifferenceResult`] is of the [`Separate`](DifferenceResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Maps the contents of the [`Difference`](DifferenceResult::Difference) variant
    pub fn map_difference<F, T>(self, f: F) -> DifferenceResult<T>
    where
        F: FnOnce(D) -> T,
    {
        match self {
            Self::Difference(d) => DifferenceResult::Difference((f)(d)),
            Self::Separate => DifferenceResult::Separate,
        }
    }
}

/// Represents the result of a symmetric difference
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymmetricDifferenceResult<D1, D2 = D1> {
    /// Symmetric difference was successful, the resulting elements are contained within this variant
    SymmetricDifference(D1, D2),
    /// Symmetric difference was unsuccessful, both elements involved are contained within this variant
    Separate,
}

impl<D1, D2> SymmetricDifferenceResult<D1, D2> {
    /// Whether the [`SymmetricDifferenceResult`] is of the
    /// [`SymmetricDifference`](SymmetricDifferenceResult::SymmetricDifference) variant
    pub fn is_symmetric_difference(&self) -> bool {
        matches!(self, Self::SymmetricDifference(..))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Separate`](SymmetricDifferenceResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate)
    }

    /// Maps the contents of the [`SymmetricDifference`](SymmetricDifferenceResult::SymmetricDifference) variant
    pub fn map_symmetric_difference<F, T, U>(self, f: F) -> SymmetricDifferenceResult<T, U>
    where
        F: FnOnce(D1, D2) -> (T, U),
    {
        match self {
            Self::SymmetricDifference(d1, d2) => {
                let new_symmetric_difference = (f)(d1, d2);
                SymmetricDifferenceResult::SymmetricDifference(new_symmetric_difference.0, new_symmetric_difference.1)
            },
            Self::Separate => SymmetricDifferenceResult::Separate,
        }
    }
}

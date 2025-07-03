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
pub enum UnionResult<U, S> {
    /// Union was successful, the united element is contained within this variant
    United(U),
    /// Union was unsuccessful, both elements involved are contained within this variant
    Separate(S, S),
}

impl<U, S> UnionResult<U, S> {
    /// Whether the [`UnionResult`] is of the [`United`](UnionResult::United) variant
    pub fn is_united(&self) -> bool {
        matches!(self, Self::United(_))
    }

    /// Whether the [`UnionResult`] is of the [`Separate`](UnionResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate(..))
    }

    /// Maps the contents of the [`United`](UnionResult::United) variant
    pub fn map_united<F, T>(self, f: F) -> UnionResult<T, S>
    where
        F: FnOnce(U) -> T,
    {
        match self {
            UnionResult::United(u) => UnionResult::United((f)(u)),
            UnionResult::Separate(a, b) => UnionResult::Separate(a, b),
        }
    }

    /// Maps the contents of the [`Separate`](UnionResult::Separate) variant
    pub fn map_separate<F, T>(self, f: F) -> UnionResult<U, T>
    where
        F: FnOnce((S, S)) -> (T, T),
    {
        match self {
            UnionResult::United(u) => UnionResult::United(u),
            UnionResult::Separate(a, b) => {
                let new_separate = (f)((a, b));
                UnionResult::Separate(new_separate.0, new_separate.1)
            },
        }
    }
}

/// Represents the result of an intersection
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntersectionResult<I, S> {
    /// Intersection was successful, the intersected element is contained within this variant
    Intersected(I),
    /// Intersection was unsuccessful, both elements involved are contained within this variant
    Separate(S, S),
}

impl<I, S> IntersectionResult<I, S> {
    /// Whether the [`IntersectionResult`] is of the [`Intersected`](IntersectionResult::Intersected) variant
    pub fn is_intersected(&self) -> bool {
        matches!(self, Self::Intersected(_))
    }

    /// Whether the [`IntersectionResult`] is of the [`Separate`](IntersectionResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate(..))
    }

    /// Maps the contents of the [`Intersected`](IntersectionResult::Intersected) variant
    pub fn map_intersected<F, T>(self, f: F) -> IntersectionResult<T, S>
    where
        F: FnOnce(I) -> T,
    {
        match self {
            Self::Intersected(i) => IntersectionResult::Intersected((f)(i)),
            Self::Separate(a, b) => IntersectionResult::Separate(a, b),
        }
    }

    /// Maps the contents of the [`Separate`](IntersectionResult::Separate) variant
    pub fn map_separate<F, T>(self, f: F) -> IntersectionResult<I, T>
    where
        F: FnOnce((S, S)) -> (T, T),
    {
        match self {
            IntersectionResult::Intersected(i) => IntersectionResult::Intersected(i),
            IntersectionResult::Separate(a, b) => {
                let new_separate = (f)((a, b));
                IntersectionResult::Separate(new_separate.0, new_separate.1)
            },
        }
    }
}

/// Represents the result of a difference
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DifferenceResult<D, S> {
    /// Difference was successful, the resulting element is contained within this variant
    Difference(D),
    /// Difference was unsuccessful, both elements involved are contained within this variant
    Separate(S, S),
}

impl<D, S> DifferenceResult<D, S> {
    /// Whether the [`DifferenceResult`] is of the [`Difference`](DifferenceResult::Difference) variant
    pub fn is_difference(&self) -> bool {
        matches!(self, Self::Difference(_))
    }

    /// Whether the [`DifferenceResult`] is of the [`Separate`](DifferenceResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate(..))
    }

    /// Maps the contents of the [`Difference`](DifferenceResult::Difference) variant
    pub fn map_difference<F, T>(self, f: F) -> DifferenceResult<T, S>
    where
        F: FnOnce(D) -> T,
    {
        match self {
            Self::Difference(d) => DifferenceResult::Difference((f)(d)),
            Self::Separate(a, b) => DifferenceResult::Separate(a, b),
        }
    }

    /// Maps the contents of the [`Separate`](DifferenceResult::Separate) variant
    pub fn map_separate<F, T>(self, f: F) -> DifferenceResult<D, T>
    where
        F: FnOnce((S, S)) -> (T, T),
    {
        match self {
            DifferenceResult::Difference(d) => DifferenceResult::Difference(d),
            DifferenceResult::Separate(a, b) => {
                let new_separate = (f)((a, b));
                DifferenceResult::Separate(new_separate.0, new_separate.1)
            },
        }
    }
}

/// Represents the result of a symmetric difference
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymmetricDifferenceResult<D, S> {
    /// Symmetric difference was successful, the resulting elements are contained within this variant
    SymmetricDifference(D, D),
    /// Symmetric difference was unsuccessful, both elements involved are contained within this variant
    Separate(S, S),
}

impl<D, S> SymmetricDifferenceResult<D, S> {
    /// Whether the [`SymmetricDifferenceResult`] is of the
    /// [`SymmetricDifference`](SymmetricDifferenceResult::SymmetricDifference) variant
    pub fn is_symmetric_difference(&self) -> bool {
        matches!(self, Self::SymmetricDifference(..))
    }

    /// Whether the [`SymmetricDifferenceResult`] is of the [`Separate`](SymmetricDifferenceResult::Separate) variant
    pub fn is_separate(&self) -> bool {
        matches!(self, Self::Separate(..))
    }

    /// Maps the contents of the [`SymmetricDifference`](SymmetricDifferenceResult::SymmetricDifference) variant
    pub fn map_symmetric_difference<F, T>(self, f: F) -> SymmetricDifferenceResult<T, S>
    where
        F: FnOnce((D, D)) -> (T, T),
    {
        match self {
            Self::SymmetricDifference(a, b) => {
                let new_symmetric_difference = (f)((a, b));
                SymmetricDifferenceResult::SymmetricDifference(new_symmetric_difference.0, new_symmetric_difference.1)
            },
            Self::Separate(a, b) => SymmetricDifferenceResult::Separate(a, b),
        }
    }

    /// Maps the contents of the [`Separate`](SymmetricDifferenceResult::Separate) variant
    pub fn map_separate<F, T>(self, f: F) -> SymmetricDifferenceResult<D, T>
    where
        F: FnOnce((S, S)) -> (T, T),
    {
        match self {
            SymmetricDifferenceResult::SymmetricDifference(a, b) => {
                SymmetricDifferenceResult::SymmetricDifference(a, b)
            },
            SymmetricDifferenceResult::Separate(a, b) => {
                let new_separate = (f)((a, b));
                SymmetricDifferenceResult::Separate(new_separate.0, new_separate.1)
            },
        }
    }
}

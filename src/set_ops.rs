//! Set operation traits
//!
//! Defines traits for the different [set operations](https://en.wikipedia.org/w/index.php?title=Set_%28mathematics%29&oldid=1291275696&useskin=vector#Basic_operations)

use crate::collections::Union;

/// Intersection operations
///
/// Similar to an OR operation
pub trait Intersect<Rhs = Self> {
    type Output;

    #[must_use]
    fn intersect(self, rhs: Rhs) -> Self::Output;
}

/// Union operation
///
/// Similar to an addition
pub trait Unite<Rhs = Self> {
    type Output;

    #[must_use]
    fn unite(self, rhs: Rhs) -> Union<Self::Output>;
}

/// Difference operation
///
/// Similar to a subtraction
pub trait Difference<Rhs = Self> {
    type Output;

    #[must_use]
    fn difference(self, rhs: Rhs) -> Self::Output;
}

/// Symmetric difference
///
/// Similar to an exclusive OR operation (XOR)
pub trait SymmetricDifference<Rhs = Self> {
    type Output;

    #[must_use]
    fn symmetric_difference(self, rhs: Rhs) -> Self::Output;
}

/// Inclusivity operations
///
/// Includes/Excludes boolean operations
pub trait Inclusivity<Rhs = Self> {
    #[must_use]
    fn includes(&self, rhs: Rhs) -> bool;

    #[must_use]
    fn excludes(&self, rhs: Rhs) -> bool {
        !self.includes(rhs)
    }
}

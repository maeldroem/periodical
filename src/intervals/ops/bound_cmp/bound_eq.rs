use crate::intervals::ops::BoundOverlapDisambiguationRuleSet;

/// Total bound equality
///
/// This trait is dedicated to equality between intervals bounds, which must be total.
pub trait BoundEq<Rhs = Self>
where
    Rhs: ?Sized,
{
    /// Returns whether two bounds are equal
    #[must_use]
    fn bound_eq(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool;

    /// Returns whether two bounds are not equal
    #[must_use]
    fn bound_ne(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        !self.bound_eq(other, rule_set)
    }
}

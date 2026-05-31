use crate::intervals::ops::BoundOverlapDisambiguationRuleSet;

// note to implementors: only implement on bounds + guarantee all transitivity etc.
pub trait BoundEq<Rhs = Self>
where
    Rhs: ?Sized,
{
    fn bound_eq(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool;

    fn bound_ne(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        !self.bound_eq(other, rule_set)
    }
}

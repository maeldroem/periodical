// note to implementors: only implement on bounds + guarantee all transitivity etc.
pub trait BoundEq<Rhs = Self>
where
    Rhs: ?Sized,
{
    fn bound_eq(&self, other: &Rhs) -> bool;

    fn bound_ne(&self, other: &Rhs) -> bool {
        !self.bound_eq(other)
    }
}

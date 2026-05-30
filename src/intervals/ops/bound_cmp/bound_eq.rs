pub trait BoundPartialEq<Rhs = Self>
where
    Rhs: ?Sized,
{
    fn bound_eq(&self, other: &Rhs) -> bool;

    fn bound_ne(&self, other: &Rhs) -> bool {
        !self.bound_eq(other)
    }
}

pub trait BoundEq: BoundPartialEq {}

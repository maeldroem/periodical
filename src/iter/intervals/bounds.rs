//! Iterator over bounds of a unite interval set

use std::iter::{FusedIterator, Peekable};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteBounds};
use crate::intervals::bound_position::BoundPosition;
use crate::intervals::relative::{RelativeBound, RelativeBounds};
use crate::iter::intervals::united_bounds::{AbsoluteUnitedBoundsIter, RelativeUnitedBoundsIter};

/// Iterator for bounds of [`AbsoluteBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBoundsIter {
    bounds: Vec<AbsoluteBounds>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl AbsoluteBoundsIter {
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = AbsoluteBounds>,
    {
        AbsoluteBoundsIter {
            bounds: iter.collect::<Vec<_>>(),
            position: BoundPosition::default(),
            initd: true,
            exhausted: false,
        }
    }

    /// Collects the bounds, sorts them and creates an [`AbsoluteUnitedBoundsIter`] from them
    #[must_use]
    pub fn united(self) -> AbsoluteUnitedBoundsIter<Peekable<impl Iterator<Item = AbsoluteBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort();

        AbsoluteUnitedBoundsIter::new(bounds.into_iter())
    }
}

impl Iterator for AbsoluteBoundsIter {
    type Item = AbsoluteBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        if !self.initd && self.position.next_bound() {
            self.exhausted = true;
            return None;
        }

        if self.initd {
            self.initd = false;
        }

        self.position.get_abs_bound(&self.bounds)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let bounds_amount = self.bounds.len().checked_mul(2);

        (bounds_amount.unwrap_or(usize::MAX), bounds_amount)
    }
}

impl FusedIterator for AbsoluteBoundsIter {}

impl ExactSizeIterator for AbsoluteBoundsIter {}

impl FromIterator<AbsoluteBounds> for AbsoluteBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = AbsoluteBounds>,
    {
        AbsoluteBoundsIter::new(iter.into_iter())
    }
}

impl Extend<AbsoluteBounds> for AbsoluteBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = AbsoluteBounds>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`AbsoluteBoundsIter`]
pub trait AbsoluteBoundsIterDispatcher: IntoIterator<Item = AbsoluteBounds> + Sized {
    fn abs_bounds_iter(self) -> AbsoluteBoundsIter {
        AbsoluteBoundsIter::new(self.into_iter())
    }
}

impl<I> AbsoluteBoundsIterDispatcher for I where I: IntoIterator<Item = AbsoluteBounds> + Sized {}

/// Iterator for bounds of [`RelativeBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativeBoundsIter {
    bounds: Vec<RelativeBounds>,
    position: BoundPosition,
    initd: bool, // whether the iterator was just initialized
    exhausted: bool,
}

impl RelativeBoundsIter {
    #[must_use]
    pub fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = RelativeBounds>,
    {
        RelativeBoundsIter {
            bounds: iter.collect::<Vec<_>>(),
            position: BoundPosition::default(),
            initd: true,
            exhausted: false,
        }
    }

    /// Collects the bounds, sorts them and creates an [`RelativeUnitedBoundsIter`] from them
    #[must_use]
    pub fn united(self) -> RelativeUnitedBoundsIter<Peekable<impl Iterator<Item = RelativeBound>>> {
        let mut bounds = self.collect::<Vec<_>>();
        bounds.sort();

        RelativeUnitedBoundsIter::new(bounds.into_iter())
    }
}

impl Iterator for RelativeBoundsIter {
    type Item = RelativeBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        if !self.initd && self.position.next_bound() {
            self.exhausted = true;
            return None;
        }

        if self.initd {
            self.initd = false;
        }

        self.position.get_rel_bound(&self.bounds)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let bounds_amount = self.bounds.len().checked_mul(2);

        (bounds_amount.unwrap_or(usize::MAX), bounds_amount)
    }
}

impl FusedIterator for RelativeBoundsIter {}

impl ExactSizeIterator for RelativeBoundsIter {}

impl FromIterator<RelativeBounds> for RelativeBoundsIter {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = RelativeBounds>,
    {
        RelativeBoundsIter::new(iter.into_iter())
    }
}

impl Extend<RelativeBounds> for RelativeBoundsIter {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = RelativeBounds>,
    {
        self.bounds.extend(iter);
    }
}

/// Iterator dispatcher trait for [`RelativeBoundsIter`]
pub trait RelativeBoundsIterDispatcher: IntoIterator<Item = RelativeBounds> + Sized {
    fn rel_bounds_iter(self) -> RelativeBoundsIter {
        RelativeBoundsIter::new(self.into_iter())
    }
}

impl<I> RelativeBoundsIterDispatcher for I where I: IntoIterator<Item = RelativeBounds> + Sized {}

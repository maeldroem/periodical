//! Iterator over bounds of a unite interval set

use std::iter::FusedIterator;

use crate::collections::intervals::united_bounds::{AbsoluteUnitedBoundsIter, RelativeUnitedBoundsIter};
use crate::intervals::absolute::{AbsoluteBound, AbsoluteBounds};
use crate::intervals::bound_position::BoundPosition;
use crate::intervals::relative::{RelativeBound, RelativeBounds};

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

    /// Unites the bounds of the iterator
    #[must_use]
    pub fn united(self) -> AbsoluteUnitedBoundsIter {
        AbsoluteUnitedBoundsIter::new(self)
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
}

impl FusedIterator for AbsoluteBoundsIter {}

/// Iterator dispatcher trait for [`AbsoluteBoundsIter`]
pub trait AbsoluteBoundsIterDispatcher: IntoIterator<Item = AbsoluteBounds> + Sized {
    fn abs_bounds_iter(self) -> AbsoluteBoundsIter {
        AbsoluteBoundsIter::new(self.into_iter())
    }
}

impl<I> AbsoluteBoundsIterDispatcher for I where I: IntoIterator<Item = AbsoluteBounds> {}

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

    /// Unites the bounds of the iterator
    #[must_use]
    pub fn united(self) -> RelativeUnitedBoundsIter {
        RelativeUnitedBoundsIter::new(self)
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
}

impl FusedIterator for RelativeBoundsIter {}

/// Iterator dispatcher trait for [`RelativeBoundsIter`]
pub trait RelativeBoundsIterDispatcher: IntoIterator<Item = RelativeBounds> + Sized {
    fn rel_bounds_iter(self) -> RelativeBoundsIter {
        RelativeBoundsIter::new(self.into_iter())
    }
}

impl<I> RelativeBoundsIterDispatcher for I where I: IntoIterator<Item = RelativeBounds> {}

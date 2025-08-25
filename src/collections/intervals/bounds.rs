//! Iterator over bounds of a unite interval set

use crate::intervals::absolute::{AbsoluteBound, AbsoluteBounds};
use crate::intervals::bound_position::BoundPosition;
use crate::intervals::relative::{RelativeBound, RelativeBounds};

/// Iterator for bounds of [`AbsoluteBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBoundsIter<'a> {
    bounds: Vec<&'a AbsoluteBounds>,
    position: BoundPosition,
}

impl Iterator for AbsoluteBoundsIter<'_> {
    type Item = AbsoluteBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position.next_bound() {
            return None;
        }

        self.position.get_abs_bound(&self.bounds)
    }
}

impl DoubleEndedIterator for AbsoluteBoundsIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.position.next_back_bound() {
            return None;
        }

        self.position.get_abs_bound(&self.bounds)
    }
}

/// Iterator for bounds of [`RelativeBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativeBoundsIter<'a> {
    bounds: Vec<&'a RelativeBounds>,
    position: BoundPosition,
}

impl Iterator for RelativeBoundsIter<'_> {
    type Item = RelativeBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position.next_bound() {
            return None;
        }

        self.position.get_rel_bound(&self.bounds)
    }
}

impl DoubleEndedIterator for RelativeBoundsIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.position.next_back_bound() {
            return None;
        }

        self.position.get_rel_bound(&self.bounds)
    }
}

//! Interval complement iterator

use crate::intervals::prelude::*;
use crate::ops::ComplementResult;

/// Dispatcher trait for the [`ComplementIter`] iterator
pub trait ComplementIteratorDispatcher: Iterator + Sized {
    fn complement(self) -> ComplementIter<Self> {
        ComplementIter::new(self)
    }
}

impl<I> ComplementIteratorDispatcher for I
where
    I: Iterator,
    I::Item: Complementable,
{
}

/// Returns the interval complement of each element
pub struct ComplementIter<I> {
    iter: I,
}

impl<I> ComplementIter<I> {
    pub fn new(iter: I) -> Self {
        ComplementIter { iter }
    }
}

impl<I> Iterator for ComplementIter<I>
where
    I: Iterator,
    I::Item: Complementable,
{
    type Item = ComplementResult<<I::Item as Complementable>::Output>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.complement())
    }
}

impl<I> DoubleEndedIterator for ComplementIter<I>
where
    I: DoubleEndedIterator,
    I::Item: Complementable,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.complement())
    }
}

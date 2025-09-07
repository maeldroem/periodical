//! Iterator to remove empty intervals

use crate::intervals::Emptiable;

/// Dispatcher trait for empty interval removal
pub trait RemoveEmptyIntervalsIteratorDispatcher
where
    Self: IntoIterator + Sized,
    Self::Item: Emptiable,
{
    /// Remove empty intervals
    fn remove_empty_intervals(self) -> RemoveEmptyIntervals<Self::IntoIter> {
        RemoveEmptyIntervals::new(self.into_iter())
    }
}

impl<I> RemoveEmptyIntervalsIteratorDispatcher for I
where
    I: IntoIterator + Sized,
    I::Item: Emptiable,
{
}

/// Empty interval removal iterator
#[derive(Debug, Clone, Hash)]
pub struct RemoveEmptyIntervals<I> {
    iter: I,
}

impl<I> RemoveEmptyIntervals<I>
where
    I: Iterator,
    I::Item: Emptiable,
{
    pub fn new(iter: I) -> Self {
        RemoveEmptyIntervals { iter }
    }
}

impl<I> Iterator for RemoveEmptyIntervals<I>
where
    I: Iterator,
    I::Item: Emptiable,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.iter.next()?;
            if !current.is_empty() {
                return Some(current);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // All items could be empty, so reset lower bound at 0
        (0, self.iter.size_hint().1)
    }
}

impl<I> DoubleEndedIterator for RemoveEmptyIntervals<I>
where
    I: DoubleEndedIterator,
    I::Item: Emptiable,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.iter.next_back()?;
            if !current.is_empty() {
                return Some(current);
            }
        }
    }
}

//! Iterator to remove empty intervals

use crate::intervals::Emptiable;

/// Dispatcher trait for empty interval removal
pub trait RemoveEmptyIntervalsIteratorDispatcher: Iterator + Sized {
    /// Remove empty intervals
    fn remove_empty_intervals(self) -> RemoveEmptyIntervals<Self> {
        RemoveEmptyIntervals::new(self)
    }
}

impl<I> RemoveEmptyIntervalsIteratorDispatcher for I
where
    I: Iterator,
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

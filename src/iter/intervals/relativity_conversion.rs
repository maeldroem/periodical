//! Relativity conversion iterators

use chrono::{DateTime, Utc};

use crate::intervals::prelude::*;

/// Dispatcher trait for the [`ToAbsoluteIter`] conversion iterator
pub trait ToAbsoluteIteratorDispatcher: IntoIterator + Sized {
    /// Converts [`RelativeInterval`]s to [`AbsoluteInterval`]s
    fn to_absolute(self, reference_time: DateTime<Utc>) -> ToAbsoluteIter<Self::IntoIter> {
        ToAbsoluteIter::new(self.into_iter(), reference_time)
    }
}

impl<I> ToAbsoluteIteratorDispatcher for I
where
    I: IntoIterator,
    I::Item: ToAbsolute,
{
}

/// Converts relative intervals to absolute intervals
pub struct ToAbsoluteIter<I> {
    iter: I,
    reference_time: DateTime<Utc>,
}

impl<I> ToAbsoluteIter<I> {
    pub fn new(iter: I, reference_time: DateTime<Utc>) -> Self {
        ToAbsoluteIter { iter, reference_time }
    }
}

impl<I> Iterator for ToAbsoluteIter<I>
where
    I: Iterator,
    I::Item: ToAbsolute,
{
    type Item = <I::Item as ToAbsolute>::AbsoluteType;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_absolute(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for ToAbsoluteIter<I>
where
    I: DoubleEndedIterator,
    I::Item: ToAbsolute,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.to_absolute(self.reference_time))
    }
}

/// Dispatcher trait for the [`ToRelativeIter`] conversion iterator
pub trait ToRelativeIteratorDispatcher: IntoIterator + Sized {
    /// Converts [`AbsoluteInterval`]s to [`RelativeInterval`]s
    fn to_relative(self, reference_time: DateTime<Utc>) -> ToRelativeIter<Self::IntoIter> {
        ToRelativeIter::new(self.into_iter(), reference_time)
    }
}

impl<I> ToRelativeIteratorDispatcher for I
where
    I: IntoIterator,
    I::Item: ToRelative,
{
}

/// Converts absolute intervals to relative intervals
pub struct ToRelativeIter<I> {
    iter: I,
    reference_time: DateTime<Utc>,
}

impl<I> ToRelativeIter<I> {
    pub fn new(iter: I, reference_time: DateTime<Utc>) -> Self {
        ToRelativeIter { iter, reference_time }
    }
}

impl<I> Iterator for ToRelativeIter<I>
where
    I: Iterator,
    I::Item: ToRelative,
{
    type Item = <I::Item as ToRelative>::RelativeType;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.to_relative(self.reference_time))
    }
}

impl<I> DoubleEndedIterator for ToRelativeIter<I>
where
    I: DoubleEndedIterator,
    I::Item: ToRelative,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.iter.next_back()?.to_relative(self.reference_time))
    }
}

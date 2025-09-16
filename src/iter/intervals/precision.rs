//! Precision change iterators

use crate::intervals::ops::precision::PreciseAbsoluteInterval;
use crate::ops::Precision;

/// Dispatcher trait for the [`PrecisionChange`] iterator
pub trait PrecisionChangeIteratorDispatcher
where
    Self: IntoIterator + Sized,
    Self::Item: PreciseAbsoluteInterval,
{
    /// Changes the precision of the interval with the given [`Precision`]
    fn change_precision(self, precision: Precision) -> PrecisionChange<Self::IntoIter> {
        PrecisionChange::new(self.into_iter(), precision, precision)
    }

    /// Changes the precision of start and end bounds with the given [`Precision`]s
    fn change_start_end_precision(
        self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> PrecisionChange<Self::IntoIter> {
        PrecisionChange::new(self.into_iter(), start_precision, end_precision)
    }
}

impl<I> PrecisionChangeIteratorDispatcher for I
where
    I: IntoIterator + Sized,
    I::Item: PreciseAbsoluteInterval,
{
}

/// Changes the precision of start end end times
pub struct PrecisionChange<I> {
    iter: I,
    start_precision: Precision,
    end_precision: Precision,
}

impl<I> PrecisionChange<I>
where
    I: Iterator,
    I::Item: PreciseAbsoluteInterval,
{
    pub fn new(iter: I, start_precision: Precision, end_precision: Precision) -> Self {
        PrecisionChange {
            iter,
            start_precision,
            end_precision,
        }
    }
}

impl<I> Iterator for PrecisionChange<I>
where
    I: Iterator,
    I::Item: PreciseAbsoluteInterval,
{
    type Item = <I::Item as PreciseAbsoluteInterval>::PrecisedIntervalOutput;

    fn next(&mut self) -> Option<Self::Item> {
        Some(
            self.iter
                .next()?
                .precise_interval_with_different_precisions(self.start_precision, self.end_precision),
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I> DoubleEndedIterator for PrecisionChange<I>
where
    I: DoubleEndedIterator,
    I::Item: PreciseAbsoluteInterval,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(
            self.iter
                .next_back()?
                .precise_interval_with_different_precisions(self.start_precision, self.end_precision),
        )
    }
}

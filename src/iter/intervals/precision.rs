//! Precision change iterators

use crate::intervals::PreciseAbsoluteBounds;
use crate::ops::Precision;

/// Dispatcher trait for the [`PrecisionChange`] iterator
pub trait PrecisionChangeIteratorDispatcher
where
    Self: IntoIterator + Sized,
    Self::Item: PreciseAbsoluteBounds,
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
    I::Item: PreciseAbsoluteBounds,
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
    I::Item: PreciseAbsoluteBounds,
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
    I::Item: PreciseAbsoluteBounds,
{
    type Item = <I::Item as PreciseAbsoluteBounds>::PrecisedBoundsOutput;

    fn next(&mut self) -> Option<Self::Item> {
        Some(
            self.iter
                .next()?
                .precise_bounds_with_different_precisions(self.start_precision, self.end_precision),
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I> DoubleEndedIterator for PrecisionChange<I>
where
    I: DoubleEndedIterator,
    I::Item: PreciseAbsoluteBounds,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(
            self.iter
                .next_back()?
                .precise_bounds_with_different_precisions(self.start_precision, self.end_precision),
        )
    }
}

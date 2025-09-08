//! Symmetric difference of a [layered bounds iterator](crate::iter::intervals::layered_bounds)

use std::iter::FusedIterator;

use crate::intervals::absolute::AbsoluteBounds;
use crate::intervals::relative::RelativeBounds;
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};

/// Symmetric difference iterator
/// for [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredAbsoluteBoundsSymmetricDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsoluteBoundsSymmetricDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>,
{
    /// Creates an instance of [`LayeredAbsoluteBoundsSymmetricDifference`]
    ///
    /// # Input requirements
    ///
    /// The given iterator **must return continuous [state changes](LayeredBoundsStateChangeAtAbsoluteBound)**,
    /// that is to say the first state change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [old state](LayeredBoundsStateChangeAtAbsoluteBound::old_state),
    /// the last change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [new state](LayeredBoundsStateChangeAtAbsoluteBound::new_state), and all state changes must follow each
    /// other, i.e. if one change transitions from state A to state B, the next change's old state must be the previous
    /// change's new state: state B.
    ///
    /// All of that is automatically guaranteed if the state changes are obtained from
    /// [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds).
    pub fn new(iter: I) -> LayeredAbsoluteBoundsSymmetricDifference<I> {
        LayeredAbsoluteBoundsSymmetricDifference { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredAbsoluteBoundsSymmetricDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>,
{
    type Item = AbsoluteBounds;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        loop {
            let Some(current) = self.iter.next() else {
                self.exhausted = true;
                return None;
            };

            if matches!(
                current.new_state(),
                LayeredBoundsState::NoLayers | LayeredBoundsState::BothLayers
            ) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            loop {
                let Some(next) = self.iter.next() else {
                    unreachable!(
                        "The input requirements guarantee that the given iterator \
                        cannot end on an active state such as `FirstLayer` or `SecondLayer`"
                    );
                };

                // State can transition from FirstLayer to SecondLayer, but in a symmetric difference,
                // those should be united
                if matches!(
                    next.new_state(),
                    LayeredBoundsState::FirstLayer | LayeredBoundsState::SecondLayer
                ) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "We can infer the guarantee that the state change following one that transitions \
                        to `FirstLayer` or `SecondLayer` must contain an end to the old state, \
                        given that the input requirements guarantee that the given iterator cannot end \
                        on an active state such as `FirstLayer` or `SecondLayer`"
                    );
                };

                return Some(AbsoluteBounds::new(start, end));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredAbsoluteBoundsSymmetricDifference<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>
{
}

/// Iterator dispatcher trait for [`LayeredAbsoluteBoundsSymmetricDifference`]
pub trait LayeredAbsoluteBoundsSymmetricDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtAbsoluteBound> + Sized,
{
    /// Creates a [`LayeredAbsoluteBoundsSymmetricDifference`]
    fn abs_symmetric_difference_layered(self) -> LayeredAbsoluteBoundsSymmetricDifference<Self::IntoIter> {
        LayeredAbsoluteBoundsSymmetricDifference::new(self.into_iter())
    }
}

impl<I> LayeredAbsoluteBoundsSymmetricDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtAbsoluteBound> + Sized
{
}

/// Symmetric difference iterator
/// for [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::LayeredRelativeBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelativeBoundsSymmetricDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelativeBoundsSymmetricDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>,
{
    /// Creates an instance of [`LayeredRelativeBoundsSymmetricDifference`]
    ///
    /// # Input requirements
    ///
    /// The given iterator **must return continuous [state changes](LayeredBoundsStateChangeAtRelativeBound)**,
    /// that is to say the first state change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [old state](LayeredBoundsStateChangeAtRelativeBound::old_state),
    /// the last change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [new state](LayeredBoundsStateChangeAtRelativeBound::new_state), and all state changes must follow each
    /// other, i.e. if one change transitions from state A to state B, the next change's old state must be the previous
    /// change's new state: state B.
    ///
    /// All of that is automatically guaranteed if the state changes are obtained from
    /// [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::LayeredRelativeBounds).
    pub fn new(iter: I) -> LayeredRelativeBoundsSymmetricDifference<I> {
        LayeredRelativeBoundsSymmetricDifference { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredRelativeBoundsSymmetricDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>,
{
    type Item = RelativeBounds;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        loop {
            let Some(current) = self.iter.next() else {
                self.exhausted = true;
                return None;
            };

            if matches!(
                current.new_state(),
                LayeredBoundsState::NoLayers | LayeredBoundsState::BothLayers
            ) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            loop {
                let Some(next) = self.iter.next() else {
                    unreachable!(
                        "The input requirements guarantee that the given iterator \
                        cannot end on an active state such as `FirstLayer` or `SecondLayer`"
                    );
                };

                // State can transition from FirstLayer to SecondLayer, but in a symmetric difference,
                // those should be united
                if matches!(
                    next.new_state(),
                    LayeredBoundsState::FirstLayer | LayeredBoundsState::SecondLayer
                ) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "We can infer the guarantee that the state change following one that transitions \
                        to `FirstLayer` or `SecondLayer` must contain an end to the old state, \
                        given that the input requirements guarantee that the given iterator cannot end \
                        on an active state such as `FirstLayer` or `SecondLayer`"
                    );
                };

                return Some(RelativeBounds::new(start, end));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredRelativeBoundsSymmetricDifference<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>
{
}

/// Iterator dispatcher trait for [`LayeredRelativeBoundsSymmetricDifference`]
pub trait LayeredRelativeBoundsSymmetricDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtRelativeBound> + Sized,
{
    /// Creates a [`LayeredRelativeBoundsSymmetricDifference`]
    fn rel_symmetric_difference_layered(self) -> LayeredRelativeBoundsSymmetricDifference<Self::IntoIter> {
        LayeredRelativeBoundsSymmetricDifference::new(self.into_iter())
    }
}

impl<I> LayeredRelativeBoundsSymmetricDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtRelativeBound> + Sized
{
}

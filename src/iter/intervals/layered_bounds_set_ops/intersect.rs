//! Intersection of a [layered bounds iterator](crate::iter::intervals::layered_bounds)

use std::iter::FusedIterator;

use crate::intervals::absolute::AbsoluteBounds;
use crate::intervals::relative::RelativeBounds;
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};

/// Intersection iterator
/// for [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LayeredAbsoluteBoundsIntersection<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsoluteBoundsIntersection<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>,
{
    /// Creates an instance of [`LayeredAbsoluteBoundsIntersection`]
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
    pub fn new(iter: I) -> LayeredAbsoluteBoundsIntersection<I> {
        LayeredAbsoluteBoundsIntersection { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredAbsoluteBoundsIntersection<I>
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

            if !matches!(current.new_state(), LayeredBoundsState::BothLayers) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            let Some(next) = self.iter.next() else {
                unreachable!(
                    "The input requirements guarantee that the given iterator \
                    cannot end on an active state such as `BothLayers`"
                );
            };

            let Some(end) = next.old_state_end() else {
                unreachable!(
                    "We can infer the guarantee that the state change following one that transitions to `BothLayers` \
                    must contain an end to the old state, given that the input requirements guarantee \
                    that the given iterator cannot end on an active state such as `BothLayers`"
                );
            };

            return Some(AbsoluteBounds::new(start, end));
        }
    }
}

impl<I> FusedIterator for LayeredAbsoluteBoundsIntersection<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>
{
}

/// Intersection iterator
/// for [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::LayeredRelativeBounds)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LayeredRelativeBoundsIntersection<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelativeBoundsIntersection<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>,
{
    /// Creates an instance of [`LayeredRelativeBoundsIntersection`]
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
    pub fn new(iter: I) -> LayeredRelativeBoundsIntersection<I> {
        LayeredRelativeBoundsIntersection { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredRelativeBoundsIntersection<I>
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

            if !matches!(current.new_state(), LayeredBoundsState::BothLayers) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            let Some(next) = self.iter.next() else {
                unreachable!(
                    "The input requirements guarantee that the given iterator \
                    cannot end on an active state such as `BothLayers`"
                );
            };

            let Some(end) = next.old_state_end() else {
                unreachable!(
                    "We can infer the guarantee that the state change following one that transitions to `BothLayers` \
                    must contain an end to the old state, given that the input requirements guarantee \
                    that the given iterator cannot end on an active state such as `BothLayers`"
                );
            };

            return Some(RelativeBounds::new(start, end));
        }
    }
}

impl<I> FusedIterator for LayeredRelativeBoundsIntersection<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>
{
}

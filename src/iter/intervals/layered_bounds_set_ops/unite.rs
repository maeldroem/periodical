//! Union of a [layered bounds iterator](crate::iter::intervals::layered_bounds)

use std::iter::FusedIterator;

use crate::intervals::absolute::AbsoluteBounds;
use crate::intervals::relative::RelativeBounds;
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};

/// Union iterator
/// for [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds)
pub struct LayeredAbsoluteBoundsUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsoluteBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>,
{
    /// Creates an instance of [`LayeredAbsoluteBoundsUnion`]
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
    pub fn new(iter: I) -> LayeredAbsoluteBoundsUnion<I> {
        LayeredAbsoluteBoundsUnion { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredAbsoluteBoundsUnion<I>
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

            if matches!(current.new_state(), LayeredBoundsState::NoLayers) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            loop {
                let Some(next) = self.iter.next() else {
                    unreachable!(
                        "Since the input requirements state that the state changes need to be continuous, \
                        and since we already stopped at a state that is not `NoLayers`, we can expect \
                        the next elements to exist until a state change that transitions to `NoLayers` is returned"
                    );
                };

                if !matches!(next.new_state(), LayeredBoundsState::NoLayers) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "Since the input requirements state that the state changes need to be continuous, \
                        we can expect the next state change which transitions to `NoLayers` to contain \
                        the change's old state's end"
                    );
                };

                return Some(AbsoluteBounds::new(start, end));
            }
        }
    }
}

impl<I> FusedIterator for LayeredAbsoluteBoundsUnion<I> where I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>
{}

/// Union iterator
/// for [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::LayeredRelativeBounds)
pub struct LayeredRelativeBoundsUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelativeBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>,
{
    /// Creates an instance of [`LayeredRelativeBoundsUnion`]
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
    pub fn new(iter: I) -> LayeredRelativeBoundsUnion<I> {
        LayeredRelativeBoundsUnion { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredRelativeBoundsUnion<I>
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

            if matches!(current.new_state(), LayeredBoundsState::NoLayers) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            loop {
                let Some(next) = self.iter.next() else {
                    unreachable!(
                        "Since the input requirements state that the state changes need to be continuous, \
                        and since we already stopped at a state that is not `NoLayers`, we can expect \
                        the next elements to exist until a state change that transitions to `NoLayers` is returned"
                    );
                };

                if !matches!(next.new_state(), LayeredBoundsState::NoLayers) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "Since the input requirements state that the state changes need to be continuous, \
                        we can expect the next state change which transitions to `NoLayers` to contain \
                        the change's old state's end"
                    );
                };

                return Some(RelativeBounds::new(start, end));
            }
        }
    }
}

impl<I> FusedIterator for LayeredRelativeBoundsUnion<I> where I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>
{}

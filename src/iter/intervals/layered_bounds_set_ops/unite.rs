//! Union of a [layered bounds iterator](crate::iter::intervals::layered_bounds)
//!
//! Operates a [union] on a [layered bounds iterator](crate::iter::intervals::layered_bounds).
//!
//! [union]: https://en.wikipedia.org/w/index.php?title=Union_(set_theory)&oldid=1310613637
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
//! # use periodical::iter::intervals::layered_bounds_set_ops::LayeredAbsBoundsUnionIteratorDispatcher;
//! # use periodical::iter::intervals::layered_bounds::{
//! #     LayeredAbsBounds, LayeredBoundsState, LayeredBoundsStateChangeAtAbsBound,
//! # };
//! let first_layer_intervals = [
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_end_bound(),
//!     ),
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 13:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_end_bound(),
//!     ),
//! ];
//!
//! let second_layer_intervals = [
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 07:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 11:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_end_bound(),
//!     ),
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         ).to_end_bound(),
//!     ),
//! ];
//!
//! assert_eq!(
//!     first_layer_intervals
//!         .abs_bounds_iter()
//!         .unite_bounds()
//!         .layer(second_layer_intervals.abs_bounds_iter().unite_bounds())
//!         .abs_unite_layered()
//!         .collect::<Vec<_>>(),
//!     vec![
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 07:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_start_bound(),
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_end_bound(),
//!         ),
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 13:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_start_bound(),
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 18:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_end_bound(),
//!         ),
//!     ],
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use std::iter::FusedIterator;

use crate::intervals::absolute::AbsBoundPair;
use crate::intervals::relative::RelBoundPair;
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState,
    LayeredBoundsStateChangeAtAbsBound,
    LayeredBoundsStateChangeAtRelBound,
};

/// Union iterator
/// for [`LayeredAbsBounds`](crate::iter::intervals::layered_bounds::LayeredAbsBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredAbsBoundsUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsBound>,
{
    /// Creates a new [`LayeredAbsBoundsUnion`]
    ///
    /// # Input requirements
    ///
    /// 1. The iterator **must return continuous [state changes](LayeredBoundsStateChangeAtAbsBound)**
    /// 2. The state changes **must be in chronological order**
    ///
    /// For more precision about requirement 1, _continuous state changes_ means
    /// that the first state change
    /// must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [old state](LayeredBoundsStateChangeAtAbsBound::old_state),
    /// the last change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [new state](LayeredBoundsStateChangeAtAbsBound::new_state),
    /// and all state changes must follow each other, i.e. if one change
    /// transitions from state A to state B, the next change's old state must be
    /// the previous change's new state: state B.
    ///
    /// All requirements are automatically guaranteed if the state changes are
    /// obtained from
    /// [`LayeredAbsBounds`](crate::iter::intervals::layered_bounds::LayeredAbsBounds).
    pub fn new(iter: I) -> LayeredAbsBoundsUnion<I> {
        LayeredAbsBoundsUnion {
            iter,
            exhausted: false,
        }
    }
}

impl<I> Iterator for LayeredAbsBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsBound>,
{
    type Item = AbsBoundPair;

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
                        "Since the input requirements state that the state changes need to be continuous, and since \
                         we already stopped at a state that is not `NoLayers`, we can expect the next elements to \
                         exist until a state change that transitions to `NoLayers` is returned"
                    );
                };

                if !matches!(next.new_state(), LayeredBoundsState::NoLayers) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "Since the input requirements state that the state changes need to be continuous, we can \
                         expect the next state change which transitions to `NoLayers` to contain the change's old \
                         state's end"
                    );
                };

                return Some(AbsBoundPair::new(start, end));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();

        (
            inner_size_hint.0.min(1),
            inner_size_hint.1.map(|upper_bound| upper_bound.div_ceil(2)),
        )
    }
}

impl<I> FusedIterator for LayeredAbsBoundsUnion<I> where I: Iterator<Item = LayeredBoundsStateChangeAtAbsBound> {}

/// Iterator dispatcher trait for [`LayeredAbsBoundsUnion`]
pub trait LayeredAbsBoundsUnionIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtAbsBound> + Sized,
{
    /// Operates a [union]
    ///
    /// See [module documentation](self) for more information.
    ///
    /// [union]: https://en.wikipedia.org/w/index.php?title=Union_(set_theory)&oldid=1310613637
    fn abs_unite_layered(self) -> LayeredAbsBoundsUnion<Self::IntoIter> {
        LayeredAbsBoundsUnion::new(self.into_iter())
    }
}

impl<I> LayeredAbsBoundsUnionIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtAbsBound> + Sized
{
}

/// Union iterator
/// for [`LayeredRelBounds`](crate::iter::intervals::layered_bounds::LayeredRelBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelBoundsUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelBound>,
{
    /// Creates a new [`LayeredRelBoundsUnion`]
    ///
    /// # Input requirements
    ///
    /// 1. The iterator **must return continuous [state changes](LayeredBoundsStateChangeAtRelBound)**
    /// 2. The state changes **must be in chronological order**
    ///
    /// For more precision about requirement 1, _continuous state changes_ means
    /// that the first state change
    /// must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [old state](LayeredBoundsStateChangeAtRelBound::old_state),
    /// the last change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [new state](LayeredBoundsStateChangeAtRelBound::new_state),
    /// and all state changes must follow each other, i.e. if one change
    /// transitions from state A to state B, the next change's old state must be
    /// the previous change's new state: state B.
    ///
    /// All requirements are automatically guaranteed if the state changes are
    /// obtained from
    /// [`LayeredRelBounds`](crate::iter::intervals::layered_bounds::LayeredRelBounds).
    pub fn new(iter: I) -> LayeredRelBoundsUnion<I> {
        LayeredRelBoundsUnion {
            iter,
            exhausted: false,
        }
    }
}

impl<I> Iterator for LayeredRelBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelBound>,
{
    type Item = RelBoundPair;

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
                        "Since the input requirements state that the state changes need to be continuous, and since \
                         we already stopped at a state that is not `NoLayers`, we can expect the next elements to \
                         exist until a state change that transitions to `NoLayers` is returned"
                    );
                };

                if !matches!(next.new_state(), LayeredBoundsState::NoLayers) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "Since the input requirements state that the state changes need to be continuous, we can \
                         expect the next state change which transitions to `NoLayers` to contain the change's old \
                         state's end"
                    );
                };

                return Some(RelBoundPair::new(start, end));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();

        (
            inner_size_hint.0.min(1),
            inner_size_hint.1.map(|upper_bound| upper_bound.div_ceil(2)),
        )
    }
}

impl<I> FusedIterator for LayeredRelBoundsUnion<I> where I: Iterator<Item = LayeredBoundsStateChangeAtRelBound> {}

/// Iterator dispatcher trait for [`LayeredRelBoundsUnion`]
pub trait LayeredRelBoundsUnionIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtRelBound> + Sized,
{
    /// Operates a [union]
    ///
    /// See [module documentation](self) for more information.
    ///
    /// [union]: https://en.wikipedia.org/w/index.php?title=Union_(set_theory)&oldid=1310613637
    fn rel_unite_layered(self) -> LayeredRelBoundsUnion<Self::IntoIter> {
        LayeredRelBoundsUnion::new(self.into_iter())
    }
}

impl<I> LayeredRelBoundsUnionIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtRelBound> + Sized
{
}

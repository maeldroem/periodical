//! Union of a [layered bounds iterator](crate::iter::intervals::layered_bounds)
//!
//! Operates a [union] on a [layered bounds iterator](crate::iter::intervals::layered_bounds).
//!
//! [union]: https://en.wikipedia.org/w/index.php?title=Union_(set_theory)&oldid=1310613637
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
//! # use periodical::iter::intervals::layered_bounds_set_ops::LayeredAbsoluteBoundsUnionIteratorDispatcher;
//! # use periodical::iter::intervals::layered_bounds::{
//! #     LayeredAbsoluteBounds, LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
//! # };
//! let first_layer_intervals = [
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     ),
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     ),
//! ];
//!
//! let second_layer_intervals = [
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     ),
//!     AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
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
//!         AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         ),
//!         AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         ),
//!     ],
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::iter::FusedIterator;

use crate::intervals::absolute::AbsoluteBounds;
use crate::intervals::relative::RelativeBounds;
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};

/// Union iterator
/// for [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredAbsoluteBoundsUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsoluteBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>,
{
    /// Creates a new [`LayeredAbsoluteBoundsUnion`]
    ///
    /// # Input requirements
    ///
    /// 1. The iterator **must return continuous [state changes](LayeredBoundsStateChangeAtAbsoluteBound)**
    /// 2. The state changes **must be in chronological order**
    ///
    /// For more precision about requirement 1, _continuous state changes_ means that the first state change
    /// must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [old state](LayeredBoundsStateChangeAtAbsoluteBound::old_state),
    /// the last change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [new state](LayeredBoundsStateChangeAtAbsoluteBound::new_state), and all state changes must follow each
    /// other, i.e. if one change transitions from state A to state B, the next change's old state must be the previous
    /// change's new state: state B.
    ///
    /// All requirements are automatically guaranteed if the state changes are obtained from
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();

        (
            inner_size_hint.0.min(1),
            inner_size_hint.1.map(|upper_bound| upper_bound.div_ceil(2)),
        )
    }
}

impl<I> FusedIterator for LayeredAbsoluteBoundsUnion<I> where I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>
{}

/// Iterator dispatcher trait for [`LayeredAbsoluteBoundsUnion`]
pub trait LayeredAbsoluteBoundsUnionIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtAbsoluteBound> + Sized,
{
    /// Operates a [union]
    ///
    /// See [module documentation](crate::iter::intervals::layered_bounds_set_ops::unite) for more information.
    ///
    /// [union]: https://en.wikipedia.org/w/index.php?title=Union_(set_theory)&oldid=1310613637
    fn abs_unite_layered(self) -> LayeredAbsoluteBoundsUnion<Self::IntoIter> {
        LayeredAbsoluteBoundsUnion::new(self.into_iter())
    }
}

impl<I> LayeredAbsoluteBoundsUnionIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtAbsoluteBound> + Sized
{
}

/// Union iterator
/// for [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::LayeredRelativeBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelativeBoundsUnion<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelativeBoundsUnion<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>,
{
    /// Creates a new [`LayeredRelativeBoundsUnion`]
    ///
    /// # Input requirements
    ///
    /// 1. The iterator **must return continuous [state changes](LayeredBoundsStateChangeAtRelativeBound)**
    /// 2. The state changes **must be in chronological order**
    ///
    /// For more precision about requirement 1, _continuous state changes_ means that the first state change
    /// must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [old state](LayeredBoundsStateChangeAtRelativeBound::old_state),
    /// the last change must have [`NoLayers`](LayeredBoundsState::NoLayers)
    /// as its [new state](LayeredBoundsStateChangeAtRelativeBound::new_state), and all state changes must follow each
    /// other, i.e. if one change transitions from state A to state B, the next change's old state must be the previous
    /// change's new state: state B.
    ///
    /// All requirements are automatically guaranteed if the state changes are obtained from
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_size_hint = self.iter.size_hint();

        (
            inner_size_hint.0.min(1),
            inner_size_hint.1.map(|upper_bound| upper_bound.div_ceil(2)),
        )
    }
}

impl<I> FusedIterator for LayeredRelativeBoundsUnion<I> where I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>
{}

/// Iterator dispatcher trait for [`LayeredRelativeBoundsUnion`]
pub trait LayeredRelativeBoundsUnionIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtRelativeBound> + Sized,
{
    /// Operates a [union]
    ///
    /// See [module documentation](crate::iter::intervals::layered_bounds_set_ops::unite) for more information.
    ///
    /// [union]: https://en.wikipedia.org/w/index.php?title=Union_(set_theory)&oldid=1310613637
    fn rel_unite_layered(self) -> LayeredRelativeBoundsUnion<Self::IntoIter> {
        LayeredRelativeBoundsUnion::new(self.into_iter())
    }
}

impl<I> LayeredRelativeBoundsUnionIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtRelativeBound> + Sized
{
}

//! Difference of a [layered bounds iterator](crate::iter::intervals::layered_bounds)
//!
//! Operates a [set difference] on a [layered bounds iterator](crate::iter::intervals::layered_bounds).
//! The first layer acts like the first operand in a classical set difference, while the second layer acts
//! like the second operand. In other words, the first layer are the _removed_
//! while the second layer are the _removers_.
//!
//! [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Rel_complement
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{
//! #     AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
//! # use periodical::iter::intervals::layered_bounds_set_ops::LayeredAbsBoundsDifferenceIteratorDispatcher;
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
//!         .abs_difference_layered()
//!         .collect::<Vec<_>>(),
//!     vec![
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new_with_inclusivity(
//!                 "2025-01-01 11:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             ).to_start_bound(),
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_end_bound(),
//!         ),
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 13:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_start_bound(),
//!             AbsFiniteBoundPos::new_with_inclusivity(
//!                 "2025-01-01 14:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!                 BoundInclusivity::Exclusive,
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

/// Difference iterator
/// for [`LayeredAbsBounds`](crate::iter::intervals::layered_bounds::LayeredAbsBounds)
///
/// The first layer acts like the first operand in a classical set difference,
/// while the second layer acts like the second operand. In other words, the
/// first layer are the _removed_ while the second layer are the _removers_.
#[derive(Debug, Clone, Hash)]
pub struct LayeredAbsBoundsDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsBoundsDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsBound>,
{
    /// Creates a new [`LayeredAbsBoundsDifference`]
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
    pub fn new(iter: I) -> LayeredAbsBoundsDifference<I> {
        LayeredAbsBoundsDifference {
            iter,
            exhausted: false,
        }
    }
}

impl<I> Iterator for LayeredAbsBoundsDifference<I>
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

            if !matches!(current.new_state(), LayeredBoundsState::FirstLayer) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            let Some(next) = self.iter.next() else {
                unreachable!(
                    "The input requirements guarantee that the given iterator cannot end on an active state such as \
                     `FirstLayer`"
                );
            };

            let Some(end) = next.old_state_end() else {
                unreachable!(
                    "We can infer the guarantee that the state change following one that transitions to `FirstLayer` \
                     must contain an end to the old state, given that the input requirements guarantee that the given \
                     iterator cannot end on an active state such as `FirstLayer`"
                );
            };

            return Some(AbsBoundPair::new(start, end));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredAbsBoundsDifference<I> where I: Iterator<Item = LayeredBoundsStateChangeAtAbsBound> {}

/// Iterator dispatcher trait for [`LayeredAbsBoundsDifference`]
pub trait LayeredAbsBoundsDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtAbsBound> + Sized,
{
    /// Operates a [set difference]
    ///
    /// See [module documentation](self) for more information.
    ///
    /// [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Rel_complement
    fn abs_difference_layered(self) -> LayeredAbsBoundsDifference<Self::IntoIter> {
        LayeredAbsBoundsDifference::new(self.into_iter())
    }
}

impl<I> LayeredAbsBoundsDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtAbsBound> + Sized
{
}

/// Difference iterator
/// for [`LayeredRelBounds`](crate::iter::intervals::layered_bounds::LayeredRelBounds)
///
/// The first layer acts like the first operand in a classical set difference,
/// while the second layer acts like the second operand. In other words, the
/// first layer are the _removed_ while the second layer are the _removers_.
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelBoundsDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelBoundsDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelBound>,
{
    /// Creates a new [`LayeredRelBoundsDifference`]
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
    pub fn new(iter: I) -> LayeredRelBoundsDifference<I> {
        LayeredRelBoundsDifference {
            iter,
            exhausted: false,
        }
    }
}

impl<I> Iterator for LayeredRelBoundsDifference<I>
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

            if !matches!(current.new_state(), LayeredBoundsState::FirstLayer) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            let Some(next) = self.iter.next() else {
                unreachable!(
                    "The input requirements guarantee that the given iterator cannot end on an active state such as \
                     `FirstLayer`"
                );
            };

            let Some(end) = next.old_state_end() else {
                unreachable!(
                    "We can infer the guarantee that the state change following one that transitions to `FirstLayer` \
                     must contain an end to the old state, given that the input requirements guarantee that the given \
                     iterator cannot end on an active state such as `FirstLayer`"
                );
            };

            return Some(RelBoundPair::new(start, end));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredRelBoundsDifference<I> where I: Iterator<Item = LayeredBoundsStateChangeAtRelBound> {}

/// Iterator dispatcher trait for [`LayeredRelBoundsDifference`]
pub trait LayeredRelBoundsDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtRelBound> + Sized,
{
    /// Operates a [set difference]
    ///
    /// See [module documentation](self) for more information.
    ///
    /// [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Rel_complement
    fn rel_difference_layered(self) -> LayeredRelBoundsDifference<Self::IntoIter> {
        LayeredRelBoundsDifference::new(self.into_iter())
    }
}

impl<I> LayeredRelBoundsDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtRelBound> + Sized
{
}

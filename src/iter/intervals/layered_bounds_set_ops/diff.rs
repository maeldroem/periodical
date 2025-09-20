//! Difference of a [layered bounds iterator](crate::iter::intervals::layered_bounds)
//!
//! Operates a [set difference] on a [layered bounds iterator](crate::iter::intervals::layered_bounds).
//! The first layer acts like the first operand in a classical set difference, while the second layer acts
//! like the second operand. In other words, the first layer are the _removed_ while the second layer
//! are the _removers_.
//!
//! [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
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
//! # use periodical::iter::intervals::layered_bounds_set_ops::LayeredAbsoluteBoundsDifferenceIteratorDispatcher;
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
//!         .abs_difference_layered()
//!         .collect::<Vec<_>>(),
//!     vec![
//!         AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         ),
//!         AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
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

/// Difference iterator
/// for [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds)
///
/// The first layer acts like the first operand in a classical set difference, while the second layer acts
/// like the second operand. In other words, the first layer are the _removed_ while the second layer
/// are the _removers_.
#[derive(Debug, Clone, Hash)]
pub struct LayeredAbsoluteBoundsDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsoluteBoundsDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>,
{
    /// Creates a new [`LayeredAbsoluteBoundsDifference`]
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
    pub fn new(iter: I) -> LayeredAbsoluteBoundsDifference<I> {
        LayeredAbsoluteBoundsDifference { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredAbsoluteBoundsDifference<I>
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

            if !matches!(current.new_state(), LayeredBoundsState::FirstLayer) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            let Some(next) = self.iter.next() else {
                unreachable!(
                    "The input requirements guarantee that the given iterator \
                    cannot end on an active state such as `FirstLayer`"
                );
            };

            let Some(end) = next.old_state_end() else {
                unreachable!(
                    "We can infer the guarantee that the state change following one that transitions to `FirstLayer` \
                    must contain an end to the old state, given that the input requirements guarantee \
                    that the given iterator cannot end on an active state such as `FirstLayer`"
                );
            };

            return Some(AbsoluteBounds::new(start, end));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredAbsoluteBoundsDifference<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsoluteBound>
{
}

/// Iterator dispatcher trait for [`LayeredAbsoluteBoundsDifference`]
pub trait LayeredAbsoluteBoundsDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtAbsoluteBound> + Sized,
{
    /// Operates a [set difference]
    ///
    /// See [module documentation](crate::iter::intervals::layered_bounds_set_ops::diff) for more information.
    ///
    /// [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
    fn abs_difference_layered(self) -> LayeredAbsoluteBoundsDifference<Self::IntoIter> {
        LayeredAbsoluteBoundsDifference::new(self.into_iter())
    }
}

impl<I> LayeredAbsoluteBoundsDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtAbsoluteBound> + Sized
{
}

/// Difference iterator
/// for [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::LayeredRelativeBounds)
///
/// The first layer acts like the first operand in a classical set difference, while the second layer acts
/// like the second operand. In other words, the first layer are the _removed_ while the second layer
/// are the _removers_.
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelativeBoundsDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelativeBoundsDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>,
{
    /// Creates a new [`LayeredRelativeBoundsDifference`]
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
    pub fn new(iter: I) -> LayeredRelativeBoundsDifference<I> {
        LayeredRelativeBoundsDifference { iter, exhausted: false }
    }
}

impl<I> Iterator for LayeredRelativeBoundsDifference<I>
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

            if !matches!(current.new_state(), LayeredBoundsState::FirstLayer) {
                continue;
            }

            let Some(start) = current.new_state_start() else {
                unreachable!("When the state is not `NoLayers`, the new state's start is guaranteed to exist");
            };

            let Some(next) = self.iter.next() else {
                unreachable!(
                    "The input requirements guarantee that the given iterator \
                    cannot end on an active state such as `FirstLayer`"
                );
            };

            let Some(end) = next.old_state_end() else {
                unreachable!(
                    "We can infer the guarantee that the state change following one that transitions to `FirstLayer` \
                    must contain an end to the old state, given that the input requirements guarantee \
                    that the given iterator cannot end on an active state such as `FirstLayer`"
                );
            };

            return Some(RelativeBounds::new(start, end));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredRelativeBoundsDifference<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelativeBound>
{
}

/// Iterator dispatcher trait for [`LayeredRelativeBoundsDifference`]
pub trait LayeredRelativeBoundsDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtRelativeBound> + Sized,
{
    /// Operates a [set difference]
    ///
    /// See [module documentation](crate::iter::intervals::layered_bounds_set_ops::diff) for more information.
    ///
    /// [set difference]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427#Relative_complement
    fn rel_difference_layered(self) -> LayeredRelativeBoundsDifference<Self::IntoIter> {
        LayeredRelativeBoundsDifference::new(self.into_iter())
    }
}

impl<I> LayeredRelativeBoundsDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtRelativeBound> + Sized
{
}

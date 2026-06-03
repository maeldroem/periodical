//! Symmetric difference of a [layered bounds iterator](crate::iter::intervals::layered_bounds)
//!
//! Operates a [symmetric difference] on a [layered bounds iterator](crate::iter::intervals::layered_bounds).
//!
//! [symmetric difference]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
//! # use periodical::iter::intervals::layered_bounds_set_ops::{
//! #     LayeredAbsBoundsSymmetricDifferenceIteratorDispatcher,
//! # };
//! # use periodical::iter::intervals::layered_bounds::{
//! #     LayeredAbsBounds, LayeredBoundsState, LayeredBoundsStateChangeAtAbsBound,
//! # };
//! let first_layer_intervals = [
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 13:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//! ];
//!
//! let second_layer_intervals = [
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 07:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 11:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//!     AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 14:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 18:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//! ];
//!
//! assert_eq!(
//!     first_layer_intervals
//!         .abs_bounds_iter()
//!         .unite_bounds()
//!         .layer(second_layer_intervals.abs_bounds_iter().unite_bounds())
//!         .abs_symmetric_difference_layered()
//!         .collect::<Vec<_>>(),
//!     vec![
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 07:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!             )
//!             .to_start_bound(),
//!             AbsFiniteBoundPos::new_with_inclusivity(
//!                 "2025-01-01 08:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             )
//!             .to_end_bound(),
//!         ),
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new_with_inclusivity(
//!                 "2025-01-01 11:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!                 BoundInclusivity::Exclusive
//!             )
//!             .to_start_bound(),
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 12:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!             )
//!             .to_end_bound(),
//!         ),
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 13:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!             )
//!             .to_start_bound(),
//!             AbsFiniteBoundPos::new_with_inclusivity(
//!                 "2025-01-01 14:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             )
//!             .to_end_bound(),
//!         ),
//!         AbsBoundPair::new(
//!             AbsFiniteBoundPos::new_with_inclusivity(
//!                 "2025-01-01 16:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!                 BoundInclusivity::Exclusive
//!             )
//!             .to_start_bound(),
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 18:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!             )
//!             .to_end_bound(),
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

/// Symmetric difference iterator
/// for [`LayeredAbsBounds`](crate::iter::intervals::layered_bounds::LayeredAbsBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredAbsBoundsSymmetricDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredAbsBoundsSymmetricDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsBound>,
{
    /// Creates a new [`LayeredAbsBoundsSymmetricDifference`]
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
    pub fn new(iter: I) -> LayeredAbsBoundsSymmetricDifference<I> {
        LayeredAbsBoundsSymmetricDifference {
            iter,
            exhausted: false,
        }
    }
}

impl<I> Iterator for LayeredAbsBoundsSymmetricDifference<I>
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
                        "The input requirements guarantee that the given iterator cannot end on an active state such \
                         as `FirstLayer` or `SecondLayer`"
                    );
                };

                // State can transition from FirstLayer to SecondLayer, but in a symmetric
                // difference, those should be united
                if matches!(
                    next.new_state(),
                    LayeredBoundsState::FirstLayer | LayeredBoundsState::SecondLayer
                ) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "We can infer the guarantee that the state change following one that transitions to \
                         `FirstLayer` or `SecondLayer` must contain an end to the old state, given that the input \
                         requirements guarantee that the given iterator cannot end on an active state such as \
                         `FirstLayer` or `SecondLayer`"
                    );
                };

                return Some(AbsBoundPair::new(start, end));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredAbsBoundsSymmetricDifference<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtAbsBound>
{
}

/// Iterator dispatcher trait for [`LayeredAbsBoundsSymmetricDifference`]
pub trait LayeredAbsBoundsSymmetricDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtAbsBound> + Sized,
{
    /// Operates a [symmetric difference]
    ///
    /// See [module documentation](self) for more information.
    ///
    /// [intersection]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
    fn abs_symmetric_difference_layered(self) -> LayeredAbsBoundsSymmetricDifference<Self::IntoIter> {
        LayeredAbsBoundsSymmetricDifference::new(self.into_iter())
    }
}

impl<I> LayeredAbsBoundsSymmetricDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtAbsBound> + Sized
{
}

/// Symmetric difference iterator
/// for [`LayeredRelBounds`](crate::iter::intervals::layered_bounds::LayeredRelBounds)
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelBoundsSymmetricDifference<I> {
    iter: I,
    exhausted: bool,
}

impl<I> LayeredRelBoundsSymmetricDifference<I>
where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelBound>,
{
    /// Creates a new [`LayeredRelBoundsSymmetricDifference`]
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
    pub fn new(iter: I) -> LayeredRelBoundsSymmetricDifference<I> {
        LayeredRelBoundsSymmetricDifference {
            iter,
            exhausted: false,
        }
    }
}

impl<I> Iterator for LayeredRelBoundsSymmetricDifference<I>
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
                        "The input requirements guarantee that the given iterator cannot end on an active state such \
                         as `FirstLayer` or `SecondLayer`"
                    );
                };

                // State can transition from FirstLayer to SecondLayer, but in a symmetric
                // difference, those should be united
                if matches!(
                    next.new_state(),
                    LayeredBoundsState::FirstLayer | LayeredBoundsState::SecondLayer
                ) {
                    continue;
                }

                let Some(end) = next.old_state_end() else {
                    unreachable!(
                        "We can infer the guarantee that the state change following one that transitions to \
                         `FirstLayer` or `SecondLayer` must contain an end to the old state, given that the input \
                         requirements guarantee that the given iterator cannot end on an active state such as \
                         `FirstLayer` or `SecondLayer`"
                    );
                };

                return Some(RelBoundPair::new(start, end));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1.map(|upper_bound| upper_bound.div_ceil(2)))
    }
}

impl<I> FusedIterator for LayeredRelBoundsSymmetricDifference<I> where
    I: Iterator<Item = LayeredBoundsStateChangeAtRelBound>
{
}

/// Iterator dispatcher trait for [`LayeredRelBoundsSymmetricDifference`]
pub trait LayeredRelBoundsSymmetricDifferenceIteratorDispatcher
where
    Self: IntoIterator<Item = LayeredBoundsStateChangeAtRelBound> + Sized,
{
    /// Operates a [symmetric difference]
    ///
    /// See [module documentation](self) for more information.
    ///
    /// [intersection]: https://en.wikipedia.org/w/index.php?title=Symmetric_difference&oldid=1311741596
    fn rel_symmetric_difference_layered(self) -> LayeredRelBoundsSymmetricDifference<Self::IntoIter> {
        LayeredRelBoundsSymmetricDifference::new(self.into_iter())
    }
}

impl<I> LayeredRelBoundsSymmetricDifferenceIteratorDispatcher for I where
    I: IntoIterator<Item = LayeredBoundsStateChangeAtRelBound> + Sized
{
}

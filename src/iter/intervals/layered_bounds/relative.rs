//! Layered relative bounds iterator

use std::cmp::Ordering;
use std::iter::{FusedIterator, Peekable};
use std::ops::{Add, Sub};

use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::RelBound;
use crate::iter::intervals::layered_bounds::rel_state_change::LayeredBoundsStateChangeAtRelBound;
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

/// Iterator tracking which layers of relative bounds are active
///
/// Tracks the layers by using a [`LayeredBoundsState`] and outputs a
/// [`LayeredBoundsStateChangeAtRelBound`] when this state changes.
///
/// # Examples
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
/// # use periodical::iter::intervals::bounds::RelBoundsIteratorDispatcher;
/// # use periodical::iter::intervals::layered_bounds::{
/// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelBound, LayeredRelBounds,
/// # };
/// let first_layer_intervals = [
///     RelBoundPair::new(
///         RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
///         RelFiniteBoundPos::new(SignedDuration::from_hours(12)).to_end_bound(),
///     ),
///     RelBoundPair::new(
///         RelFiniteBoundPos::new(SignedDuration::from_hours(13)).to_start_bound(),
///         RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
///     ),
/// ];
///
/// let second_layer_intervals = [
///     RelBoundPair::new(
///         RelFiniteBoundPos::new(SignedDuration::from_hours(7)).to_start_bound(),
///         RelFiniteBoundPos::new(SignedDuration::from_hours(11)).to_end_bound(),
///     ),
///     RelBoundPair::new(
///         RelFiniteBoundPos::new(SignedDuration::from_hours(14)).to_start_bound(),
///         RelFiniteBoundPos::new(SignedDuration::from_hours(18)).to_end_bound(),
///     ),
/// ];
///
/// assert_eq!(
///     first_layer_intervals
///         .rel_bounds_iter()
///         .unite_bounds()
///         .layer(second_layer_intervals.rel_bounds_iter().unite_bounds())
///         .collect::<Vec<_>>(),
///     vec![
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::NoLayers,
///             LayeredBoundsState::SecondLayer,
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(7),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_end_bound()
///             ),
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(7),).to_start_bound()),
///         ),
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::SecondLayer,
///             LayeredBoundsState::BothLayers,
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(8),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_end_bound()
///             ),
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(8),).to_start_bound()),
///         ),
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::BothLayers,
///             LayeredBoundsState::FirstLayer,
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(11),).to_end_bound()),
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(11),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_start_bound()
///             ),
///         ),
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::FirstLayer,
///             LayeredBoundsState::NoLayers,
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(12),).to_end_bound()),
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(12),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_start_bound()
///             ),
///         ),
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::NoLayers,
///             LayeredBoundsState::FirstLayer,
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(13),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_end_bound()
///             ),
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(13),).to_start_bound()),
///         ),
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::FirstLayer,
///             LayeredBoundsState::BothLayers,
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(14),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_end_bound()
///             ),
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(14),).to_start_bound()),
///         ),
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::BothLayers,
///             LayeredBoundsState::SecondLayer,
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(16),).to_end_bound()),
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(16),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_start_bound()
///             ),
///         ),
///         LayeredBoundsStateChangeAtRelBound::new(
///             LayeredBoundsState::SecondLayer,
///             LayeredBoundsState::NoLayers,
///             Some(RelFiniteBoundPos::new(SignedDuration::from_hours(18),).to_end_bound()),
///             Some(
///                 RelFiniteBoundPos::new_with_incl(
///                     SignedDuration::from_hours(18),
///                     BoundInclusivity::Exclusive,
///                 )
///                 .to_start_bound()
///             ),
///         ),
///     ],
/// );
/// ```
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelBounds<I1, I2> {
    first_layer: I1,
    second_layer: I2,
    state: LayeredBoundsState,
    // In some cases, the iterator needs to return two results at once
    queued_result: Option<LayeredBoundsStateChangeAtRelBound>,
    exhausted: bool,
}

impl<I1, I2> LayeredRelBounds<I1, I2> {
    /// Returns the current [state](LayeredBoundsState)
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// # use periodical::iter::intervals::bounds::RelBoundsIteratorDispatcher;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelBound, LayeredRelBounds,
    /// # };
    /// let first_layer_intervals = [
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(12)).to_end_bound(),
    ///     ),
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(13)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(7)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(11)).to_end_bound(),
    ///     ),
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(14)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(18)).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let mut layered_bounds = first_layer_intervals
    ///     .rel_bounds_iter()
    ///     .unite_bounds()
    ///     .layer(second_layer_intervals.rel_bounds_iter().unite_bounds());
    ///
    /// layered_bounds.nth(2);
    ///
    /// assert_eq!(layered_bounds.state(), LayeredBoundsState::FirstLayer);
    /// ```
    #[must_use]
    pub fn state(&self) -> LayeredBoundsState {
        self.state
    }
}

impl<I1, I2> LayeredRelBounds<I1, I2>
where
    I1: Iterator<Item = RelBound>,
    I2: Iterator<Item = RelBound>,
{
    /// Creates a new [`LayeredRelBounds`]
    ///
    /// # Input requirements
    ///
    /// 1. The bounds in each layer iterator **must be sorted chronologically**
    /// 2. The bounds in each layer iterator **must not be overlapping**
    /// 3. The bounds in each layer iterator **must be paired**, that means there should be an equal amount of
    ///    [`Start`](RelBound::Start)s and [`End`](RelBound::End)s.
    ///
    /// The responsibility of verifying those requirements are left to the
    /// caller in order to prevent double-processing.
    ///
    /// Requirements 1 and 2 are automatically guaranteed if the bounds are
    /// obtained from
    /// [`RelUnitedBoundsIter`](crate::iter::intervals::united_bounds::RelUnitedBoundsIter).
    ///
    /// Requirement 3 is automatically guaranteed if the bounds are obtained
    /// from
    /// a set of [intervals](crate::intervals::relative::RelInterval)
    /// or from [bound pairs](crate::intervals::relative::RelBoundPair) and
    /// then processed through
    /// [`RelBoundsIter`](crate::iter::intervals::bounds::RelBoundsIter).
    #[must_use]
    pub fn new(first_layer_iter: I1, second_layer_iter: I2) -> LayeredRelBounds<Peekable<I1>, Peekable<I2>> {
        LayeredRelBounds {
            first_layer: first_layer_iter.peekable(),
            second_layer: second_layer_iter.peekable(),
            state: LayeredBoundsState::default(),
            queued_result: None,
            exhausted: false,
        }
    }
}

impl<I1, I2> Iterator for LayeredRelBounds<Peekable<I1>, Peekable<I2>>
where
    I1: Iterator<Item = RelBound>,
    I2: Iterator<Item = RelBound>,
{
    type Item = LayeredBoundsStateChangeAtRelBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        // Empties the queued result before continuing
        if let Some(queued_result) = self.queued_result.take() {
            return Some(queued_result);
        }

        let old_state = self.state();

        let first_layer_peek = self.first_layer.peek();
        let second_layer_peek = self.second_layer.peek();

        match (first_layer_peek, second_layer_peek) {
            (None, None) => {
                self.exhausted = true;
                self.state = LayeredBoundsState::NoLayers;
                self.first_layer.next();
                self.second_layer.next();
                None
            },
            (Some(RelBound::Start(_)), None) => Some(layered_rel_bounds_change_start_first_layer(
                old_state,
                &mut self.first_layer,
                &mut self.state,
            )),
            (Some(RelBound::End(_)), None) => Some(layered_rel_bounds_change_end_first_layer(
                old_state,
                &mut self.first_layer,
                &mut self.state,
            )),
            (None, Some(RelBound::Start(_))) => Some(layered_rel_bounds_change_start_second_layer(
                old_state,
                &mut self.second_layer,
                &mut self.state,
            )),
            (None, Some(RelBound::End(_))) => Some(layered_rel_bounds_change_end_second_layer(
                old_state,
                &mut self.second_layer,
                &mut self.state,
            )),
            (Some(RelBound::Start(first_layer_peeked_start)), Some(RelBound::Start(second_layer_peeked_start))) => {
                Some(layered_rel_bounds_change_start_start(
                    old_state,
                    first_layer_peeked_start.cmp(second_layer_peeked_start),
                    &mut self.first_layer,
                    &mut self.second_layer,
                    &mut self.state,
                ))
            },
            (Some(RelBound::Start(first_layer_peeked_start)), Some(RelBound::End(second_layer_peeked_end))) => {
                Some(layered_rel_bounds_change_start_end(
                    old_state,
                    first_layer_peeked_start.bound_cmp(second_layer_peeked_end),
                    &mut self.first_layer,
                    &mut self.second_layer,
                    &mut self.state,
                    &mut self.queued_result,
                ))
            },
            (Some(RelBound::End(first_layer_peeked_end)), Some(RelBound::Start(second_layer_peeked_start))) => {
                Some(layered_rel_bounds_change_end_start(
                    old_state,
                    first_layer_peeked_end.bound_cmp(second_layer_peeked_start),
                    &mut self.first_layer,
                    &mut self.second_layer,
                    &mut self.state,
                    &mut self.queued_result,
                ))
            },
            (Some(RelBound::End(first_layer_peeked_end)), Some(RelBound::End(second_layer_peeked_end))) => {
                Some(layered_rel_bounds_change_end_end(
                    old_state,
                    first_layer_peeked_end.cmp(second_layer_peeked_end),
                    &mut self.first_layer,
                    &mut self.second_layer,
                    &mut self.state,
                ))
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let first_layer_size_hint = self.first_layer.size_hint();
        let second_layer_size_hint = self.second_layer.size_hint();

        (
            first_layer_size_hint.0.max(second_layer_size_hint.0),
            first_layer_size_hint.1.and_then(|first_layer_upper_bound| {
                second_layer_size_hint
                    .1
                    .and_then(|second_layer_upper_bound| first_layer_upper_bound.checked_add(second_layer_upper_bound))
            }),
        )
    }
}

impl<I1, I2> FusedIterator for LayeredRelBounds<Peekable<I1>, Peekable<I2>>
where
    I1: Iterator<Item = RelBound>,
    I2: Iterator<Item = RelBound>,
{
}

/// Computes the state change - first layer peeked, start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when only the first
/// layer has a peeked value and is a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked start bound of the first layer didn't equal the value returned by `next()` on the first layer
/// 2. The value returned by `next()` on the first layer wasn't of the [`Start`](RelBound::Start) variant
#[must_use]
pub fn layered_rel_bounds_change_start_first_layer(
    old_state: LayeredBoundsState,
    first_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    let first_layer_start = first_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .start()
        .expect("Matched for `RelBound::Start(_)`, destructured to something else");

    *state_mut = (*state_mut).add(LayeredBoundsState::FirstLayer);

    Change::new(
        old_state,
        *state_mut,
        first_layer_start.opposite(),
        Some(first_layer_start),
    )
}

/// Computes the state change - first layer peeked, end bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when only the first
/// layer has a peeked value and is an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked end bound of the first layer didn't equal the value returned by `next()` on the first layer
/// 2. The value returned by `next()` on the first layer wasn't of the [`End`](RelBound::End) variant
#[must_use]
pub fn layered_rel_bounds_change_end_first_layer(
    old_state: LayeredBoundsState,
    first_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    let first_layer_end = first_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .end()
        .expect("Matched for `RelBound::End(_)`, destructured to something else");

    *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

    Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
}

/// Computes the state change - second layer peeked, start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when only the
/// second layer has a peeked value and is a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked start bound of the second layer didn't equal the value returned by `next()` on the second layer
/// 2. The value returned by `next()` on the second layer wasn't of the [`Start`](RelBound::Start) variant
#[must_use]
pub fn layered_rel_bounds_change_start_second_layer(
    old_state: LayeredBoundsState,
    second_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    let second_layer_start = second_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .start()
        .expect("Matched for `RelBound::Start(_)`, destructured to something else");

    *state_mut = (*state_mut).add(LayeredBoundsState::SecondLayer);

    Change::new(
        old_state,
        *state_mut,
        second_layer_start.opposite(),
        Some(second_layer_start),
    )
}

/// Computes the state change - second layer peeked, end bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when only the
/// second layer has a peeked value and is an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked end bound of the second layer didn't equal the value returned by `next()` on the second layer
/// 2. The value returned by `next()` on the second layer wasn't of the [`End`](RelBound::End) variant
#[must_use]
pub fn layered_rel_bounds_change_end_second_layer(
    old_state: LayeredBoundsState,
    second_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    let second_layer_end = second_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .end()
        .expect("Matched for `RelBound::End(_)`, destructured to something else");

    *state_mut = (*state_mut).sub(LayeredBoundsState::SecondLayer);

    Change::new(
        old_state,
        *state_mut,
        Some(second_layer_end),
        second_layer_end.opposite(),
    )
}

/// Computes the state change - both layers peeked, both start bounds
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when both layers
/// have a peeked value and both are start bounds.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_rel_bounds_change_start_start(
    old_state: LayeredBoundsState,
    start_start_cmp: Ordering,
    first_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    match start_start_cmp {
        Ordering::Less => {
            let first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut).add(LayeredBoundsState::FirstLayer);

            Change::new(
                old_state,
                *state_mut,
                first_layer_start.opposite(),
                Some(first_layer_start),
            )
        },
        Ordering::Equal => {
            let first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelBound::Start(_)`, destructured to something else");

            // Advance the second layer's iterator since both layers' bounds are equal
            second_layer.next();

            *state_mut = (*state_mut).add(LayeredBoundsState::BothLayers);

            // We use the first layer's bound but that doesn't matter as bounds from both
            // layers are equal
            Change::new(
                old_state,
                *state_mut,
                first_layer_start.opposite(),
                Some(first_layer_start),
            )
        },
        Ordering::Greater => {
            let second_layer_start = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut).add(LayeredBoundsState::SecondLayer);

            Change::new(
                old_state,
                *state_mut,
                second_layer_start.opposite(),
                Some(second_layer_start),
            )
        },
    }
}

/// Computes the state change - both layers peeked, first layer start bound,
/// second layer end bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when both layers
/// have a peeked value and the first layer is a start bound and the second
/// layer is an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
/// 3. The comparison between [`RelStartBound`](crate::intervals::relative::RelStartBound) and
///    [`RelEndBound`](crate::intervals::relative::RelEndBound) returned [`None`]
#[must_use]
pub fn layered_rel_bounds_change_start_end(
    old_state: LayeredBoundsState,
    start_end_cmp: BoundOrdering,
    first_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
    queued_result_mut: &mut Option<LayeredBoundsStateChangeAtRelBound>,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    match start_end_cmp.disambiguate(BoundOverlapDisambiguationRuleSet::Lenient) {
        Ordering::Less => {
            let first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut).add(LayeredBoundsState::FirstLayer);

            Change::new(
                old_state,
                *state_mut,
                first_layer_start.opposite(),
                Some(first_layer_start),
            )
        },
        Ordering::Equal => {
            let finite_first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelBound::Start(_)`, destructured to something else")
                .finite()
                .expect("An RelStartBound and an RelEndBound can only be equal if they are finite");

            let finite_second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelBound::End(_)`, destructured to something else")
                .finite()
                .expect("An RelStartBound and an RelEndBound can only be equal if they are finite");

            if finite_first_layer_start.bound_eq(&finite_second_layer_end, BoundOverlapDisambiguationRuleSet::Strict) {
                let mut end_of_second_layer = finite_second_layer_end; // Copy
                end_of_second_layer
                    .pos_mut()
                    .set_inclusivity(BoundInclusivity::Exclusive);

                let change_to_return = Change::new(
                    old_state,
                    LayeredBoundsState::BothLayers,
                    Some(end_of_second_layer.to_end_bound()),
                    // We use `finite_first_layer_start` here because it overlaps with the second layer's end
                    // for a single instant
                    Some(finite_first_layer_start.to_start_bound()),
                );

                let mut start_of_first_layer = finite_first_layer_start; // Copy
                start_of_first_layer
                    .pos_mut()
                    .set_inclusivity(BoundInclusivity::Inclusive);

                // Since the queued result will always be emptied before any of this logic is
                // run again, we can safely modify `state_mut` here.
                *state_mut = LayeredBoundsState::FirstLayer;

                *queued_result_mut = Some(Change::new(
                    LayeredBoundsState::BothLayers,
                    *state_mut,
                    Some(finite_first_layer_start.pos().to_end_bound()),
                    Some(start_of_first_layer.to_start_bound()),
                ));

                change_to_return
            } else {
                *state_mut = (*state_mut)
                    .add(LayeredBoundsState::FirstLayer)
                    .sub(LayeredBoundsState::SecondLayer);

                Change::new(
                    old_state,
                    *state_mut,
                    Some(finite_second_layer_end.to_end_bound()),
                    Some(finite_first_layer_start.to_start_bound()),
                )
            }
        },
        Ordering::Greater => {
            let second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::SecondLayer);

            Change::new(
                old_state,
                *state_mut,
                Some(second_layer_end),
                second_layer_end.opposite(),
            )
        },
    }
}

/// Computes the state change - both layers peeked, first layer end bound,
/// second layer start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when both layers
/// have a peeked value and the first layer is an end bound and the second layer
/// is a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
/// 3. The comparison between [`RelEndBound`](crate::intervals::relative::RelEndBound) and
///    [`RelStartBound`](crate::intervals::relative::RelStartBound) returned [`None`]
#[must_use]
pub fn layered_rel_bounds_change_end_start(
    old_state: LayeredBoundsState,
    end_start_cmp: BoundOrdering,
    first_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
    queued_result_mut: &mut Option<LayeredBoundsStateChangeAtRelBound>,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    match end_start_cmp.disambiguate(BoundOverlapDisambiguationRuleSet::Lenient) {
        Ordering::Less => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Equal => {
            let finite_first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelBound::End(_)`, destructured to something else")
                .finite()
                .expect("An RelStartBound and an RelEndBound can only be equal if they are finite");

            let finite_second_layer_start = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelBound::Start(_)`, destructured to something else")
                .finite()
                .expect("An RelStartBound and an RelEndBound can only be equal if they are finite");

            if finite_first_layer_end.bound_eq(&finite_second_layer_start, BoundOverlapDisambiguationRuleSet::Strict) {
                let mut end_of_first_layer = finite_first_layer_end; // Copy
                end_of_first_layer
                    .pos_mut()
                    .set_inclusivity(BoundInclusivity::Exclusive);

                let change_to_return = Change::new(
                    old_state,
                    LayeredBoundsState::BothLayers,
                    Some(end_of_first_layer.to_end_bound()),
                    // We use `finite_second_layer_start` here because it overlaps with the first layer's end
                    // for a single instant
                    Some(finite_second_layer_start.to_start_bound()),
                );

                let mut start_of_second_layer = finite_second_layer_start; // Copy
                start_of_second_layer
                    .pos_mut()
                    .set_inclusivity(BoundInclusivity::Exclusive);

                // Since the queued result will always be emptied before any of this logic is
                // run again, we can safely modify `state_mut` here.
                *state_mut = LayeredBoundsState::SecondLayer;

                *queued_result_mut = Some(Change::new(
                    LayeredBoundsState::BothLayers,
                    *state_mut,
                    Some(finite_second_layer_start.pos().to_end_bound()),
                    Some(start_of_second_layer.to_start_bound()),
                ));

                change_to_return
            } else {
                *state_mut = (*state_mut)
                    .sub(LayeredBoundsState::FirstLayer)
                    .add(LayeredBoundsState::SecondLayer);

                Change::new(
                    old_state,
                    *state_mut,
                    Some(finite_first_layer_end.to_end_bound()),
                    Some(finite_second_layer_start.to_start_bound()),
                )
            }
        },
        Ordering::Greater => {
            let second_layer_start = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut).add(LayeredBoundsState::SecondLayer);

            Change::new(
                old_state,
                *state_mut,
                second_layer_start.opposite(),
                Some(second_layer_start),
            )
        },
    }
}

/// Computes the state change - both layers peeked, first layer end bound,
/// second layer start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelBound`] when both layers
/// have a peeked value and both are end bounds.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_rel_bounds_change_end_end(
    old_state: LayeredBoundsState,
    end_end_cmp: Ordering,
    first_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelBound>>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelBound {
    type Change = LayeredBoundsStateChangeAtRelBound;

    match end_end_cmp {
        Ordering::Less => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Equal => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelBound::End(_)`, destructured to something else");

            // Advance the second layer's iterator since both layers' bounds are equal
            second_layer.next();

            *state_mut = (*state_mut).sub(LayeredBoundsState::BothLayers);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Greater => {
            let second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::SecondLayer);

            Change::new(
                old_state,
                *state_mut,
                Some(second_layer_end),
                second_layer_end.opposite(),
            )
        },
    }
}

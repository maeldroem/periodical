//! Iterator for dealing with two sets and to compare what begins when and overlaps with what

use std::cmp::Ordering;
use std::iter::{FusedIterator, Peekable};
use std::ops::{Add, Sub};

use crate::collections::intervals::bounds::{AbsoluteBoundsIter, RelativeBoundsIter};
use crate::collections::intervals::united_bounds::{AbsoluteUnitedBoundsIter, RelativeUnitedBoundsIter};
use crate::intervals::absolute::{AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::relative::{RelativeBound, RelativeBounds, RelativeEndBound, RelativeStartBound};

/// State of a layered bounds iterator, indicating which layer(s) are active
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub enum LayeredBoundsState {
    #[default]
    NoLayers,
    FirstLayer,
    SecondLayer,
    BothLayers,
}

impl Add for LayeredBoundsState {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::NoLayers, other) => other,
            (Self::FirstLayer, Self::NoLayers | Self::FirstLayer) => Self::FirstLayer,
            (Self::SecondLayer, Self::NoLayers | Self::SecondLayer) => Self::SecondLayer,
            (Self::FirstLayer, Self::SecondLayer | Self::BothLayers)
            | (Self::SecondLayer, Self::FirstLayer | Self::BothLayers)
            | (Self::BothLayers, _) => Self::BothLayers,
        }
    }
}

impl Sub for LayeredBoundsState {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (_, Self::BothLayers)
            | (Self::NoLayers | Self::FirstLayer, Self::FirstLayer)
            | (Self::NoLayers | Self::SecondLayer, Self::SecondLayer) => Self::NoLayers,
            (Self::FirstLayer | Self::BothLayers, Self::SecondLayer) => Self::FirstLayer,
            (Self::SecondLayer | Self::BothLayers, Self::FirstLayer) => Self::SecondLayer,
            (og, Self::NoLayers) => og,
        }
    }
}

/// State change of a [`LayeredAbsoluteBounds`]
#[derive(Debug, Clone, Hash)]
pub struct LayeredBoundsStateChangeAtAbsoluteBound {
    old_state: LayeredBoundsState,
    new_state: LayeredBoundsState,
    old_state_end: Option<AbsoluteEndBound>,
    new_state_start: Option<AbsoluteStartBound>,
    // Could add a `cause` field containing the original AbsoluteBound, but idk if it's useful to do that now
}

impl LayeredBoundsStateChangeAtAbsoluteBound {
    /// Creates a new instance of [`LayeredBoundsStateChangeAtAbsoluteBound`]
    #[must_use]
    pub fn new(
        old_state: LayeredBoundsState,
        new_state: LayeredBoundsState,
        old_state_end: Option<AbsoluteEndBound>,
        new_state_start: Option<AbsoluteStartBound>,
    ) -> Self {
        LayeredBoundsStateChangeAtAbsoluteBound {
            old_state,
            new_state,
            old_state_end,
            new_state_start,
        }
    }

    /// Returns the state of the [`LayeredAbsoluteBounds`] before the change
    #[must_use]
    pub fn old_state(&self) -> LayeredBoundsState {
        self.old_state
    }

    /// Returns the state of the [`LayeredAbsoluteBounds`] after the change
    #[must_use]
    pub fn new_state(&self) -> LayeredBoundsState {
        self.new_state
    }

    /// Returns the optional [`AbsoluteEndBound`] that corresponds to the end of the old state
    #[must_use]
    pub fn old_state_end(&self) -> Option<AbsoluteEndBound> {
        self.old_state_end
    }

    /// Returns the optional [`AbsoluteStartBound`] that corresponds to the start of the new state
    #[must_use]
    pub fn new_state_start(&self) -> Option<AbsoluteStartBound> {
        self.new_state_start
    }
}

/// State change of a [`LayeredRelativeBounds`]
#[derive(Debug, Clone, Hash)]
pub struct LayeredBoundsStateChangeAtRelativeBound {
    old_state: LayeredBoundsState,
    new_state: LayeredBoundsState,
    old_state_end: Option<RelativeEndBound>,
    new_state_start: Option<RelativeStartBound>,
    // Could add a `cause` field containing the original RelativeBound, but idk if it's useful to do that now
}

impl LayeredBoundsStateChangeAtRelativeBound {
    /// Creates a new instance of [`LayeredBoundsStateChangeAtRelativeBound`]
    #[must_use]
    pub fn new(
        old_state: LayeredBoundsState,
        new_state: LayeredBoundsState,
        old_state_end: Option<RelativeEndBound>,
        new_state_start: Option<RelativeStartBound>,
    ) -> Self {
        LayeredBoundsStateChangeAtRelativeBound {
            old_state,
            new_state,
            old_state_end,
            new_state_start,
        }
    }

    /// Returns the state of the [`LayeredRelativeBounds`] before the change
    #[must_use]
    pub fn old_state(&self) -> LayeredBoundsState {
        self.old_state
    }

    /// Returns the state of the [`LayeredRelativeBounds`] after the change
    #[must_use]
    pub fn new_state(&self) -> LayeredBoundsState {
        self.new_state
    }

    /// Returns the optional [`RelativeEndBound`] that corresponds to the end of the old state
    #[must_use]
    pub fn old_state_end(&self) -> Option<RelativeEndBound> {
        self.old_state_end
    }

    /// Returns the optional [`RelativeStartBound`] that corresponds to the start of the new state
    #[must_use]
    pub fn new_state_start(&self) -> Option<RelativeStartBound> {
        self.new_state_start
    }
}

/// Iterator running over the bounds of two [`AbsoluteUnitedBoundsIter`], tracking which layers are active,
/// bound by bound
pub struct LayeredAbsoluteBounds {
    first_layer: Peekable<AbsoluteUnitedBoundsIter>,
    second_layer: Peekable<AbsoluteUnitedBoundsIter>,
    state: LayeredBoundsState,
    exhausted: bool,
}

impl LayeredAbsoluteBounds {
    pub fn new<I1, I2>(first_layer_iter: I1, second_layer_iter: I2) -> Self
    where
        I1: Iterator<Item = AbsoluteBounds>,
        I2: Iterator<Item = AbsoluteBounds>,
    {
        LayeredAbsoluteBounds {
            first_layer: AbsoluteBoundsIter::new(first_layer_iter).united().peekable(),
            second_layer: AbsoluteBoundsIter::new(second_layer_iter).united().peekable(),
            state: LayeredBoundsState::default(),
            exhausted: false,
        }
    }

    /// Returns the current [state](LayeredBoundsState) of the [`LayeredAbsoluteBounds`]
    #[must_use]
    pub fn state(&self) -> LayeredBoundsState {
        self.state
    }
}

impl Iterator for LayeredAbsoluteBounds {
    type Item = LayeredBoundsStateChangeAtAbsoluteBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
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
            (Some(AbsoluteBound::Start(_)), None) => Some(layered_abs_bounds_change_start_first_layer(
                old_state,
                &mut self.first_layer,
                &mut self.state,
            )),
            (Some(AbsoluteBound::End(_)), None) => Some(layered_abs_bounds_change_end_first_layer(
                old_state,
                &mut self.first_layer,
                &mut self.state,
            )),
            (None, Some(AbsoluteBound::Start(_))) => Some(layered_abs_bounds_change_start_second_layer(
                old_state,
                &mut self.second_layer,
                &mut self.state,
            )),
            (None, Some(AbsoluteBound::End(_))) => Some(layered_abs_bounds_change_end_second_layer(
                old_state,
                &mut self.second_layer,
                &mut self.state,
            )),
            (
                Some(AbsoluteBound::Start(first_layer_peeked_start)),
                Some(AbsoluteBound::Start(second_layer_peeked_start)),
            ) => Some(layered_abs_bounds_change_start_start(
                old_state,
                first_layer_peeked_start.cmp(second_layer_peeked_start),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
            )),
            (
                Some(AbsoluteBound::Start(first_layer_peeked_start)),
                Some(AbsoluteBound::End(second_layer_peeked_end)),
            ) => Some(layered_abs_bounds_change_start_end(
                old_state,
                first_layer_peeked_start.partial_cmp(second_layer_peeked_end).unwrap(),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
            )),
            (
                Some(AbsoluteBound::End(first_layer_peeked_end)),
                Some(AbsoluteBound::Start(second_layer_peeked_start)),
            ) => Some(layered_abs_bounds_change_end_start(
                old_state,
                first_layer_peeked_end.partial_cmp(second_layer_peeked_start).unwrap(),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
            )),
            (Some(AbsoluteBound::End(first_layer_peeked_end)), Some(AbsoluteBound::End(second_layer_peeked_end))) => {
                Some(layered_abs_bounds_change_end_end(
                    old_state,
                    first_layer_peeked_end.cmp(second_layer_peeked_end),
                    &mut self.first_layer,
                    &mut self.second_layer,
                    &mut self.state,
                ))
            },
        }
    }
}

impl FusedIterator for LayeredAbsoluteBounds {}

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when only the first layer had a peeked value and was
/// a start bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked start bound of the first layer didn't equal the value returned by `next()` on the first layer
/// 2. The value returned by `next()` on the first layer wasn't of the [`Start`](AbsoluteBound::Start) variant
#[must_use]
pub fn layered_abs_bounds_change_start_first_layer(
    old_state: LayeredBoundsState,
    first_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    let first_layer_start = first_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .start()
        .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

    *state_mut = (*state_mut).add(LayeredBoundsState::FirstLayer);

    Change::new(
        old_state,
        *state_mut,
        first_layer_start.opposite(),
        Some(first_layer_start),
    )
}

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when only the first layer had a peeked value and was
/// an end bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked end bound of the first layer didn't equal the value returned by `next()` on the first layer
/// 2. The value returned by `next()` on the first layer wasn't of the [`End`](AbsoluteBound::End) variant
#[must_use]
pub fn layered_abs_bounds_change_end_first_layer(
    old_state: LayeredBoundsState,
    first_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    let first_layer_end = first_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .end()
        .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

    *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

    Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
}

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when only the second layer had a peeked value and was
/// a start bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked start bound of the second layer didn't equal the value returned by `next()` on the second layer
/// 2. The value returned by `next()` on the second layer wasn't of the [`Start`](AbsoluteBound::Start) variant
#[must_use]
pub fn layered_abs_bounds_change_start_second_layer(
    old_state: LayeredBoundsState,
    second_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    let second_layer_start = second_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .start()
        .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

    *state_mut = (*state_mut).add(LayeredBoundsState::SecondLayer);

    Change::new(
        old_state,
        *state_mut,
        second_layer_start.opposite(),
        Some(second_layer_start),
    )
}

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when only the second layer had a peeked value and was
/// an end bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked end bound of the second layer didn't equal the value returned by `next()` on the second layer
/// 2. The value returned by `next()` on the second layer wasn't of the [`End`](AbsoluteBound::End) variant
#[must_use]
pub fn layered_abs_bounds_change_end_second_layer(
    old_state: LayeredBoundsState,
    second_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    let second_layer_end = second_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .end()
        .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

    *state_mut = (*state_mut).sub(LayeredBoundsState::SecondLayer);

    Change::new(
        old_state,
        *state_mut,
        Some(second_layer_end),
        second_layer_end.opposite(),
    )
}

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when both layers have a peeked value
///
/// The first layer has a start bound and the second layer has a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_abs_bounds_change_start_start(
    old_state: LayeredBoundsState,
    start_start_cmp: Ordering,
    first_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    second_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    match start_start_cmp {
        Ordering::Less => {
            let first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

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
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut).add(LayeredBoundsState::BothLayers);

            // We use the first layer's bound but that doesn't matter as bounds from both layers are equal
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
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

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

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when both layers have a peeked value
///
/// The first layer has a start bound and the second layer has an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_abs_bounds_change_start_end(
    old_state: LayeredBoundsState,
    start_end_cmp: Ordering,
    first_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    second_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    match start_end_cmp {
        Ordering::Less => {
            let first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

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
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut)
                .add(LayeredBoundsState::FirstLayer)
                .sub(LayeredBoundsState::SecondLayer);

            // We use the first layer's bound but that doesn't matter as bounds from both layers are equal
            Change::new(
                old_state,
                *state_mut,
                first_layer_start.opposite(),
                Some(first_layer_start),
            )
        },
        Ordering::Greater => {
            let second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

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

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when both layers have a peeked value
///
/// The first layer has an end bound and the second layer has a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_abs_bounds_change_end_start(
    old_state: LayeredBoundsState,
    end_start_cmp: Ordering,
    first_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    second_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    match end_start_cmp {
        Ordering::Less => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Equal => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut)
                .sub(LayeredBoundsState::FirstLayer)
                .add(LayeredBoundsState::SecondLayer);

            // We use the first layer's bound but that doesn't matter as bounds from both layers are equal
            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Greater => {
            let second_layer_start = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else");

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

/// Creates the [`LayeredBoundsStateChangeAtAbsoluteBound`] for when both layers have a peeked value
///
/// The first layer has an end bound and the second layer has an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_abs_bounds_change_end_end(
    old_state: LayeredBoundsState,
    end_end_cmp: Ordering,
    first_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    second_layer: &mut Peekable<AbsoluteUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    match end_end_cmp {
        Ordering::Less => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Equal => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::BothLayers);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Greater => {
            let second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else");

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

/// Iterator running over the bounds of two [`RelativeUnitedBoundsIter`], tracking which layers are active,
/// bound by bound
pub struct LayeredRelativeBounds {
    first_layer: Peekable<RelativeUnitedBoundsIter>,
    second_layer: Peekable<RelativeUnitedBoundsIter>,
    state: LayeredBoundsState,
    exhausted: bool,
}

impl LayeredRelativeBounds {
    pub fn new<I1, I2>(first_layer_iter: I1, second_layer_iter: I2) -> Self
    where
        I1: Iterator<Item = RelativeBounds>,
        I2: Iterator<Item = RelativeBounds>,
    {
        LayeredRelativeBounds {
            first_layer: RelativeBoundsIter::new(first_layer_iter).united().peekable(),
            second_layer: RelativeBoundsIter::new(second_layer_iter).united().peekable(),
            state: LayeredBoundsState::default(),
            exhausted: false,
        }
    }

    /// Returns the current [state](LayeredBoundsState) of the [`LayeredRelativeBounds`]
    #[must_use]
    pub fn state(&self) -> LayeredBoundsState {
        self.state
    }
}

impl Iterator for LayeredRelativeBounds {
    type Item = LayeredBoundsStateChangeAtRelativeBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
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
            (Some(RelativeBound::Start(_)), None) => Some(layered_rel_bounds_change_start_first_layer(
                old_state,
                &mut self.first_layer,
                &mut self.state,
            )),
            (Some(RelativeBound::End(_)), None) => Some(layered_rel_bounds_change_end_first_layer(
                old_state,
                &mut self.first_layer,
                &mut self.state,
            )),
            (None, Some(RelativeBound::Start(_))) => Some(layered_rel_bounds_change_start_second_layer(
                old_state,
                &mut self.second_layer,
                &mut self.state,
            )),
            (None, Some(RelativeBound::End(_))) => Some(layered_rel_bounds_change_end_second_layer(
                old_state,
                &mut self.second_layer,
                &mut self.state,
            )),
            (
                Some(RelativeBound::Start(first_layer_peeked_start)),
                Some(RelativeBound::Start(second_layer_peeked_start)),
            ) => Some(layered_rel_bounds_change_start_start(
                old_state,
                first_layer_peeked_start.cmp(second_layer_peeked_start),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
            )),
            (
                Some(RelativeBound::Start(first_layer_peeked_start)),
                Some(RelativeBound::End(second_layer_peeked_end)),
            ) => Some(layered_rel_bounds_change_start_end(
                old_state,
                first_layer_peeked_start.partial_cmp(second_layer_peeked_end).unwrap(),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
            )),
            (
                Some(RelativeBound::End(first_layer_peeked_end)),
                Some(RelativeBound::Start(second_layer_peeked_start)),
            ) => Some(layered_rel_bounds_change_end_start(
                old_state,
                first_layer_peeked_end.partial_cmp(second_layer_peeked_start).unwrap(),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
            )),
            (Some(RelativeBound::End(first_layer_peeked_end)), Some(RelativeBound::End(second_layer_peeked_end))) => {
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
}

impl FusedIterator for LayeredRelativeBounds {}

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when only the first layer had a peeked value and was
/// a start bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked start bound of the first layer didn't equal the value returned by `next()` on the first layer
/// 2. The value returned by `next()` on the first layer wasn't of the [`Start`](RelativeBound::Start) variant
#[must_use]
pub fn layered_rel_bounds_change_start_first_layer(
    old_state: LayeredBoundsState,
    first_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    let first_layer_start = first_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .start()
        .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

    *state_mut = (*state_mut).add(LayeredBoundsState::FirstLayer);

    Change::new(
        old_state,
        *state_mut,
        first_layer_start.opposite(),
        Some(first_layer_start),
    )
}

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when only the first layer had a peeked value and was
/// an end bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked end bound of the first layer didn't equal the value returned by `next()` on the first layer
/// 2. The value returned by `next()` on the first layer wasn't of the [`End`](RelativeBound::End) variant
#[must_use]
pub fn layered_rel_bounds_change_end_first_layer(
    old_state: LayeredBoundsState,
    first_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    let first_layer_end = first_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .end()
        .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

    *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

    Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
}

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when only the second layer had a peeked value and was
/// a start bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked start bound of the second layer didn't equal the value returned by `next()` on the second layer
/// 2. The value returned by `next()` on the second layer wasn't of the [`Start`](RelativeBound::Start) variant
#[must_use]
pub fn layered_rel_bounds_change_start_second_layer(
    old_state: LayeredBoundsState,
    second_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    let second_layer_start = second_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .start()
        .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

    *state_mut = (*state_mut).add(LayeredBoundsState::SecondLayer);

    Change::new(
        old_state,
        *state_mut,
        second_layer_start.opposite(),
        Some(second_layer_start),
    )
}

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when only the second layer had a peeked value and was
/// an end bound
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked end bound of the second layer didn't equal the value returned by `next()` on the second layer
/// 2. The value returned by `next()` on the second layer wasn't of the [`End`](RelativeBound::End) variant
#[must_use]
pub fn layered_rel_bounds_change_end_second_layer(
    old_state: LayeredBoundsState,
    second_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    let second_layer_end = second_layer
        .next()
        .expect("Peeked `Some`, got `None` after calling `next()`")
        .end()
        .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

    *state_mut = (*state_mut).sub(LayeredBoundsState::SecondLayer);

    Change::new(
        old_state,
        *state_mut,
        Some(second_layer_end),
        second_layer_end.opposite(),
    )
}

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when both layers have a peeked value
///
/// The first layer has a start bound and the second layer has a start bound.
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
    first_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    second_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    match start_start_cmp {
        Ordering::Less => {
            let first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

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
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut).add(LayeredBoundsState::BothLayers);

            // We use the first layer's bound but that doesn't matter as bounds from both layers are equal
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
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

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

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when both layers have a peeked value
///
/// The first layer has a start bound and the second layer has an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_rel_bounds_change_start_end(
    old_state: LayeredBoundsState,
    start_end_cmp: Ordering,
    first_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    second_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    match start_end_cmp {
        Ordering::Less => {
            let first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

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
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

            *state_mut = (*state_mut)
                .add(LayeredBoundsState::FirstLayer)
                .sub(LayeredBoundsState::SecondLayer);

            // We use the first layer's bound but that doesn't matter as bounds from both layers are equal
            Change::new(
                old_state,
                *state_mut,
                first_layer_start.opposite(),
                Some(first_layer_start),
            )
        },
        Ordering::Greater => {
            let second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

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

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when both layers have a peeked value
///
/// The first layer has an end bound and the second layer has a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
#[must_use]
pub fn layered_rel_bounds_change_end_start(
    old_state: LayeredBoundsState,
    end_start_cmp: Ordering,
    first_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    second_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    match end_start_cmp {
        Ordering::Less => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Equal => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut)
                .sub(LayeredBoundsState::FirstLayer)
                .add(LayeredBoundsState::SecondLayer);

            // We use the first layer's bound but that doesn't matter as bounds from both layers are equal
            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Greater => {
            let second_layer_start = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else");

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

/// Creates the [`LayeredBoundsStateChangeAtRelativeBound`] for when both layers have a peeked value
///
/// The first layer has an end bound and the second layer has an end bound.
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
    first_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    second_layer: &mut Peekable<RelativeUnitedBoundsIter>,
    state_mut: &mut LayeredBoundsState,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    match end_end_cmp {
        Ordering::Less => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::FirstLayer);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Equal => {
            let first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

            *state_mut = (*state_mut).sub(LayeredBoundsState::BothLayers);

            Change::new(old_state, *state_mut, Some(first_layer_end), first_layer_end.opposite())
        },
        Ordering::Greater => {
            let second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else");

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

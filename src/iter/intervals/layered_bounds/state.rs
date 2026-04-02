//! State for layered bounds iterators

use std::ops::{Add, Sub};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// State of a layered bounds iterator
///
/// This state indicates which layers are active.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum LayeredBoundsState {
    /// No layers are active
    #[default]
    NoLayers,
    /// Only first layer is active
    FirstLayer,
    /// Only second layer is active
    SecondLayer,
    /// Both layers are active
    BothLayers,
}

impl LayeredBoundsState {
    /// Returns whether the first layer is active
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::iter::intervals::layered_bounds::LayeredBoundsState;
    /// assert!(LayeredBoundsState::FirstLayer.is_first_layer_active());
    /// assert!(LayeredBoundsState::BothLayers.is_first_layer_active());
    /// assert!(!LayeredBoundsState::NoLayers.is_first_layer_active());
    /// assert!(!LayeredBoundsState::SecondLayer.is_first_layer_active());
    /// ```
    #[must_use]
    pub fn is_first_layer_active(&self) -> bool {
        matches!(self, Self::FirstLayer | Self::BothLayers)
    }

    /// Returns whether the second layer is active in this state
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::iter::intervals::layered_bounds::LayeredBoundsState;
    /// assert!(LayeredBoundsState::SecondLayer.is_second_layer_active());
    /// assert!(LayeredBoundsState::BothLayers.is_second_layer_active());
    /// assert!(!LayeredBoundsState::NoLayers.is_second_layer_active());
    /// assert!(!LayeredBoundsState::FirstLayer.is_second_layer_active());
    /// ```
    #[must_use]
    pub fn is_second_layer_active(&self) -> bool {
        matches!(self, Self::SecondLayer | Self::BothLayers)
    }
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

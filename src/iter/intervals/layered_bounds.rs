//! Layered bounds iterator
//!
//! Iterator used for tracking layer changes between two sets of bounds, interpreted as two separate _layers_.
//!
//! This iterator is very useful for [set operations](crate::iter::intervals::layered_bounds_set_ops) but also
//! for making the process of dealing with bounds flexible, as layered bounds iterator return changes
//! in the [`LayeredBoundsState`] using either [`LayeredBoundsStateChangeAtAbsoluteBound`] for absolute bounds,
//! or [`LayeredBoundsStateChangeAtRelativeBound`] for relative bounds.
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
//!         .collect::<Vec<_>>(),
//!     vec![
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::NoLayers,
//!             LayeredBoundsState::SecondLayer,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::SecondLayer,
//!             LayeredBoundsState::BothLayers,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::BothLayers,
//!             LayeredBoundsState::FirstLayer,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::FirstLayer,
//!             LayeredBoundsState::NoLayers,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::NoLayers,
//!             LayeredBoundsState::FirstLayer,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::FirstLayer,
//!             LayeredBoundsState::BothLayers,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::BothLayers,
//!             LayeredBoundsState::SecondLayer,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::SecondLayer,
//!             LayeredBoundsState::NoLayers,
//!             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
//!             ))),
//!             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             ))),
//!         ),
//!     ],
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::cmp::Ordering;
use std::iter::{FusedIterator, Peekable};
use std::ops::{Add, Sub};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
use crate::intervals::relative::{RelativeBound, RelativeEndBound, RelativeStartBound};

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

/// State change of a [`LayeredAbsoluteBounds`]
///
/// This state change is situated using absolute bounds: [`AbsoluteStartBound`] and [`AbsoluteEndBound`].
///
/// A state change represents a point in the iterator where the [`LayeredBoundsState`] changes.
/// It also stores with it _when_ the change happened, more precisely, when the old state ends, given by
/// [`old_state_end`](LayeredBoundsStateChangeAtAbsoluteBound::old_state_end), and when the new state begins,
/// given by [`new_state_start`](LayeredBoundsStateChangeAtAbsoluteBound::new_state_start).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct LayeredBoundsStateChangeAtAbsoluteBound {
    old_state: LayeredBoundsState,
    new_state: LayeredBoundsState,
    old_state_end: Option<AbsoluteEndBound>,
    new_state_start: Option<AbsoluteStartBound>,
    // Could add a `cause` field containing the original AbsoluteBound, but idk if it's useful to do that now
}

impl LayeredBoundsStateChangeAtAbsoluteBound {
    /// Creates a new [`LayeredBoundsStateChangeAtAbsoluteBound`]
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

    /// Returns the state before the change
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsoluteBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))),
    ///     Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(change.old_state(), LayeredBoundsState::NoLayers);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn old_state(&self) -> LayeredBoundsState {
        self.old_state
    }

    /// Returns the state after the change
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsoluteBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))),
    ///     Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(change.new_state(), LayeredBoundsState::FirstLayer);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new_state(&self) -> LayeredBoundsState {
        self.new_state
    }

    /// Returns the end of the old state
    ///
    /// Returns an [`AbsoluteEndBound`] wrapped in an [`Option`] that corresponds to the end of the old state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at [`AbsoluteStartBound::InfinitePast`],
    /// therefore there is nothing that can be positioned _before_ infinite past.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsoluteBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))),
    ///     Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(
    ///     change.old_state_end(),
    ///     Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn old_state_end(&self) -> Option<AbsoluteEndBound> {
        self.old_state_end
    }

    /// Returns the start of the new state
    ///
    /// Returns an [`AbsoluteStartBound`] wrapped in an [`Option`] that corresponds to the start of the new state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at [`AbsoluteEndBound::InfiniteFuture`],
    /// therefore there is nothing that can be positioned _after_ infinite future.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsoluteBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ))),
    ///     Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(
    ///     change.new_state_start(),
    ///     Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new_state_start(&self) -> Option<AbsoluteStartBound> {
        self.new_state_start
    }
}

/// State change of a [`LayeredRelativeBounds`]
///
/// This state change is situated using relative bounds: [`RelativeStartBound`] and [`RelativeEndBound`].
///
/// A state change represents a point in the iterator where the [`LayeredBoundsState`] changes.
/// It also stores with it _when_ the change happened, more precisely, when the old state ends, given by
/// [`old_state_end`](LayeredBoundsStateChangeAtRelativeBound::old_state_end), and when the new state begins,
/// given by [`new_state_start`](LayeredBoundsStateChangeAtRelativeBound::new_state_start).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct LayeredBoundsStateChangeAtRelativeBound {
    old_state: LayeredBoundsState,
    new_state: LayeredBoundsState,
    old_state_end: Option<RelativeEndBound>,
    new_state_start: Option<RelativeStartBound>,
    // Could add a `cause` field containing the original RelativeBound, but idk if it's useful to do that now
}

impl LayeredBoundsStateChangeAtRelativeBound {
    /// Creates a new [`LayeredBoundsStateChangeAtRelativeBound`]
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

    /// Returns the state before the change
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///         Duration::hours(8),
    ///     ))),
    ///     Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
    ///         Duration::hours(8),
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(change.old_state(), LayeredBoundsState::NoLayers);
    /// ```
    #[must_use]
    pub fn old_state(&self) -> LayeredBoundsState {
        self.old_state
    }

    /// Returns the state after the change
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///         Duration::hours(8),
    ///     ))),
    ///     Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
    ///         Duration::hours(8),
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(change.new_state(), LayeredBoundsState::FirstLayer);
    /// ```
    #[must_use]
    pub fn new_state(&self) -> LayeredBoundsState {
        self.new_state
    }

    /// Returns the end of the old state
    ///
    /// Returns an [`RelativeEndBound`] wrapped in an [`Option`] that corresponds to the end of the old state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at [`RelativeStartBound::InfinitePast`],
    /// therefore there is nothing that can be positioned _before_ infinite past.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///         Duration::hours(8),
    ///     ))),
    ///     Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
    ///         Duration::hours(8),
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(
    ///     change.old_state_end(),
    ///     Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///         Duration::hours(8),
    ///     ))),
    /// );
    /// ```
    #[must_use]
    pub fn old_state_end(&self) -> Option<RelativeEndBound> {
        self.old_state_end
    }

    /// Returns the start of the new state
    ///
    /// Returns an [`RelativeStartBound`] wrapped in an [`Option`] that corresponds to the start of the new state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at [`RelativeEndBound::InfiniteFuture`],
    /// therefore there is nothing that can be positioned _after_ infinite future.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///         Duration::hours(8),
    ///     ))),
    ///     Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
    ///         Duration::hours(8),
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    ///
    /// assert_eq!(
    ///     change.new_state_start(),
    ///     Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
    ///         Duration::hours(8),
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// ```
    #[must_use]
    pub fn new_state_start(&self) -> Option<RelativeStartBound> {
        self.new_state_start
    }
}

/// Iterator tracking which layers of absolute bounds are active
///
/// Tracks the layers by using a [`LayeredBoundsState`] and outputs a [`LayeredBoundsStateChangeAtAbsoluteBound`]
/// when this state changes.
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
/// # use periodical::iter::intervals::layered_bounds::{
/// #     LayeredAbsoluteBounds, LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
/// # };
/// let first_layer_intervals = [
///     AbsoluteBounds::new(
///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///     ),
///     AbsoluteBounds::new(
///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///     ),
/// ];
///
/// let second_layer_intervals = [
///     AbsoluteBounds::new(
///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///     ),
///     AbsoluteBounds::new(
///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///     ),
/// ];
///
/// assert_eq!(
///     first_layer_intervals
///         .abs_bounds_iter()
///         .unite_bounds()
///         .layer(second_layer_intervals.abs_bounds_iter().unite_bounds())
///         .collect::<Vec<_>>(),
///     vec![
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::NoLayers,
///             LayeredBoundsState::SecondLayer,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::SecondLayer,
///             LayeredBoundsState::BothLayers,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::BothLayers,
///             LayeredBoundsState::FirstLayer,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::FirstLayer,
///             LayeredBoundsState::NoLayers,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::NoLayers,
///             LayeredBoundsState::FirstLayer,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::FirstLayer,
///             LayeredBoundsState::BothLayers,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::BothLayers,
///             LayeredBoundsState::SecondLayer,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtAbsoluteBound::new(
///             LayeredBoundsState::SecondLayer,
///             LayeredBoundsState::NoLayers,
///             Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
///             ))),
///             Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///     ],
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
#[derive(Debug, Clone, Hash)]
pub struct LayeredAbsoluteBounds<I1, I2> {
    first_layer: I1,
    second_layer: I2,
    state: LayeredBoundsState,
    // In some cases, the iterator needs to return two results at once
    queued_result: Option<LayeredBoundsStateChangeAtAbsoluteBound>,
    exhausted: bool,
}

impl<I1, I2> LayeredAbsoluteBounds<I1, I2> {
    /// Returns the current [state](LayeredBoundsState)
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredAbsoluteBounds, LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
    /// # };
    /// let first_layer_intervals = [
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 13:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 07:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 11:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 14:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 18:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    /// ];
    ///
    /// let mut layered_bounds = first_layer_intervals
    ///     .abs_bounds_iter()
    ///     .unite_bounds()
    ///     .layer(second_layer_intervals.abs_bounds_iter().unite_bounds());
    ///
    /// layered_bounds.nth(2);
    ///
    /// assert_eq!(layered_bounds.state(), LayeredBoundsState::FirstLayer);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn state(&self) -> LayeredBoundsState {
        self.state
    }
}

impl<I1, I2> LayeredAbsoluteBounds<I1, I2>
where
    I1: Iterator<Item = AbsoluteBound>,
    I2: Iterator<Item = AbsoluteBound>,
{
    /// Creates a new [`LayeredAbsoluteBounds`]
    ///
    /// # Input requirements
    ///
    /// 1. The bounds in each layer iterator **must be sorted chronologically**
    /// 2. The bounds in each layer iterator **must not be overlapping**
    /// 3. The bounds in each layer iterator **must be paired**, that means there should be an equal amount of
    ///    [`Start`](AbsoluteBound::Start)s and [`End`](AbsoluteBound::End)s.
    ///
    /// The responsibility of verifying those requirements are left to the caller
    /// in order to prevent double-processing.
    ///
    /// Requirements 1 and 2 are automatically guaranteed if the bounds are obtained from
    /// [`AbsoluteUnitedBoundsIter`](crate::iter::intervals::united_bounds::AbsoluteUnitedBoundsIter).
    ///
    /// Requirement 3 is automatically guaranteed if the bounds are obtained from
    /// a set of [intervals](crate::intervals::absolute::AbsoluteInterval)
    /// or from [bound pairs](crate::intervals::absolute::AbsoluteBounds) and then processed through
    /// [`AbsoluteBoundsIter`](crate::iter::intervals::bounds::AbsoluteBoundsIter).
    #[must_use]
    pub fn new(first_layer_iter: I1, second_layer_iter: I2) -> LayeredAbsoluteBounds<Peekable<I1>, Peekable<I2>> {
        LayeredAbsoluteBounds {
            first_layer: first_layer_iter.peekable(),
            second_layer: second_layer_iter.peekable(),
            state: LayeredBoundsState::default(),
            queued_result: None,
            exhausted: false,
        }
    }
}

impl<I1, I2> Iterator for LayeredAbsoluteBounds<Peekable<I1>, Peekable<I2>>
where
    I1: Iterator<Item = AbsoluteBound>,
    I2: Iterator<Item = AbsoluteBound>,
{
    type Item = LayeredBoundsStateChangeAtAbsoluteBound;

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
                first_layer_peeked_start.bound_cmp(second_layer_peeked_end),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
                &mut self.queued_result,
            )),
            (
                Some(AbsoluteBound::End(first_layer_peeked_end)),
                Some(AbsoluteBound::Start(second_layer_peeked_start)),
            ) => Some(layered_abs_bounds_change_end_start(
                old_state,
                first_layer_peeked_end.bound_cmp(second_layer_peeked_start),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
                &mut self.queued_result,
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

impl<I1, I2> FusedIterator for LayeredAbsoluteBounds<Peekable<I1>, Peekable<I2>>
where
    I1: Iterator<Item = AbsoluteBound>,
    I2: Iterator<Item = AbsoluteBound>,
{
}

/// Computes the state change - first layer peeked, start bound
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when only the first layer has a peeked value
/// and is a start bound.
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
    first_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
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

/// Computes the state change - first layer peeked, end bound
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when only the first layer has a peeked value
/// and is an end bound.
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
    first_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
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

/// Computes the state change - second layer peeked, start bound
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when only the second layer has a peeked value
/// and is a start bound.
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
    second_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
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

/// Computes the state change - second layer peeked, end bound
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when only the second layer has a peeked value
/// and is an end bound.
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
    second_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
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

/// Computes the state change - both layers peeked, both start bounds
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when both layers have a peeked value
/// and both are start bounds.
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
    first_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
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

            // Advance the second layer's iterator since both layers' bounds are equal
            second_layer.next();

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

/// Computes the state change - both layers peeked, first layer start bound, second layer end bound
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when both layers have a peeked value
/// and the first layer is a start bound and the second layer is an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
/// 3. The comparison between [`AbsoluteStartBound`] and [`AbsoluteEndBound`] returned [`None`]
#[must_use]
pub fn layered_abs_bounds_change_start_end(
    old_state: LayeredBoundsState,
    start_end_cmp: BoundOrdering,
    first_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
    state_mut: &mut LayeredBoundsState,
    queued_result_mut: &mut Option<LayeredBoundsStateChangeAtAbsoluteBound>,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    match start_end_cmp.disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient) {
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
            let finite_first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else")
                .finite()
                .expect("An AbsoluteStartBound and an AbsoluteEndBound can only be equal if they are finite");

            let finite_second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else")
                .finite()
                .expect("An AbsoluteStartBound and an AbsoluteEndBound can only be equal if they are finite");

            if finite_first_layer_start == finite_second_layer_end {
                let mut end_of_second_layer = finite_second_layer_end; // Copy
                end_of_second_layer.set_inclusivity(BoundInclusivity::Exclusive);

                let change_to_return = Change::new(
                    old_state,
                    LayeredBoundsState::BothLayers,
                    Some(AbsoluteEndBound::Finite(end_of_second_layer)),
                    // We use `finite_first_layer_start` here because it overlaps with the second layer's end
                    // for a single instant
                    Some(AbsoluteStartBound::Finite(finite_first_layer_start)),
                );

                let mut start_of_first_layer = finite_first_layer_start; // Copy
                start_of_first_layer.set_inclusivity(BoundInclusivity::Exclusive);

                // Since the queued result will always be emptied before any of this logic is run again,
                // we can safely modify `state_mut` here.
                *state_mut = LayeredBoundsState::FirstLayer;

                *queued_result_mut = Some(Change::new(
                    LayeredBoundsState::BothLayers,
                    *state_mut,
                    Some(AbsoluteEndBound::Finite(finite_first_layer_start)),
                    Some(AbsoluteStartBound::Finite(start_of_first_layer)),
                ));

                change_to_return
            } else {
                *state_mut = (*state_mut)
                    .add(LayeredBoundsState::FirstLayer)
                    .sub(LayeredBoundsState::SecondLayer);

                Change::new(
                    old_state,
                    *state_mut,
                    Some(AbsoluteEndBound::Finite(finite_second_layer_end)),
                    Some(AbsoluteStartBound::Finite(finite_first_layer_start)),
                )
            }
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

/// Computes the state change - both layers peeked, first layer end bound, second layer start bound
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when both layers have a peeked value
/// and the first layer is an end bound and the second layer is a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
/// 3. The comparison between [`AbsoluteEndBound`] and [`AbsoluteStartBound`] returned [`None`]
#[must_use]
pub fn layered_abs_bounds_change_end_start(
    old_state: LayeredBoundsState,
    end_start_cmp: BoundOrdering,
    first_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
    state_mut: &mut LayeredBoundsState,
    queued_result_mut: &mut Option<LayeredBoundsStateChangeAtAbsoluteBound>,
) -> LayeredBoundsStateChangeAtAbsoluteBound {
    type Change = LayeredBoundsStateChangeAtAbsoluteBound;

    match end_start_cmp.disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient) {
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
            let finite_first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `AbsoluteBound::End(_)`, destructured to something else")
                .finite()
                .expect("An AbsoluteStartBound and an AbsoluteEndBound can only be equal if they are finite");

            let finite_second_layer_start = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `AbsoluteBound::Start(_)`, destructured to something else")
                .finite()
                .expect("An AbsoluteStartBound and an AbsoluteEndBound can only be equal if they are finite");

            if finite_first_layer_end == finite_second_layer_start {
                let mut end_of_first_layer = finite_first_layer_end; // Copy
                end_of_first_layer.set_inclusivity(BoundInclusivity::Exclusive);

                let change_to_return = Change::new(
                    old_state,
                    LayeredBoundsState::BothLayers,
                    Some(AbsoluteEndBound::Finite(end_of_first_layer)),
                    // We use `finite_second_layer_start` here because it overlaps with the first layer's end
                    // for a single instant
                    Some(AbsoluteStartBound::Finite(finite_second_layer_start)),
                );

                let mut start_of_second_layer = finite_second_layer_start; // Copy
                start_of_second_layer.set_inclusivity(BoundInclusivity::Exclusive);

                // Since the queued result will always be emptied before any of this logic is run again,
                // we can safely modify `state_mut` here.
                *state_mut = LayeredBoundsState::SecondLayer;

                *queued_result_mut = Some(Change::new(
                    LayeredBoundsState::BothLayers,
                    *state_mut,
                    Some(AbsoluteEndBound::Finite(finite_second_layer_start)),
                    Some(AbsoluteStartBound::Finite(start_of_second_layer)),
                ));

                change_to_return
            } else {
                *state_mut = (*state_mut)
                    .sub(LayeredBoundsState::FirstLayer)
                    .add(LayeredBoundsState::SecondLayer);

                Change::new(
                    old_state,
                    *state_mut,
                    Some(AbsoluteEndBound::Finite(finite_first_layer_end)),
                    Some(AbsoluteStartBound::Finite(finite_second_layer_start)),
                )
            }
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

/// Computes the state change - both layers peeked, first layer end bound, second layer start bound
///
/// Computes the [`LayeredBoundsStateChangeAtAbsoluteBound`] when both layers have a peeked value
/// and both are end bounds.
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
    first_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = AbsoluteBound>>,
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

/// Iterator tracking which layers of relative bounds are active
///
/// Tracks the layers by using a [`LayeredBoundsState`] and outputs a [`LayeredBoundsStateChangeAtRelativeBound`]
/// when this state changes.
///
/// # Examples
///
/// ```
/// # use chrono::Duration;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::relative::{
/// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
/// # };
/// # use periodical::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
/// # use periodical::iter::intervals::layered_bounds::{
/// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound, LayeredRelativeBounds,
/// # };
/// let first_layer_intervals = [
///     RelativeBounds::new(
///         RelativeStartBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(8),
///         )),
///         RelativeEndBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(12),
///         )),
///     ),
///     RelativeBounds::new(
///         RelativeStartBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(13),
///         )),
///         RelativeEndBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(16),
///         )),
///     ),
/// ];
///
/// let second_layer_intervals = [
///     RelativeBounds::new(
///         RelativeStartBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(7),
///         )),
///         RelativeEndBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(11),
///         )),
///     ),
///     RelativeBounds::new(
///         RelativeStartBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(14),
///         )),
///         RelativeEndBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(18),
///         )),
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
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::NoLayers,
///             LayeredBoundsState::SecondLayer,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(7),
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(7),
///             ))),
///         ),
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::SecondLayer,
///             LayeredBoundsState::BothLayers,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(8),
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(8),
///             ))),
///         ),
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::BothLayers,
///             LayeredBoundsState::FirstLayer,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(11),
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(11),
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::FirstLayer,
///             LayeredBoundsState::NoLayers,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(12),
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(12),
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::NoLayers,
///             LayeredBoundsState::FirstLayer,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(13),
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(13),
///             ))),
///         ),
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::FirstLayer,
///             LayeredBoundsState::BothLayers,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(14),
///                 BoundInclusivity::Exclusive,
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(14),
///             ))),
///         ),
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::BothLayers,
///             LayeredBoundsState::SecondLayer,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(16),
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(16),
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///         LayeredBoundsStateChangeAtRelativeBound::new(
///             LayeredBoundsState::SecondLayer,
///             LayeredBoundsState::NoLayers,
///             Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
///                 Duration::hours(18),
///             ))),
///             Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
///                 Duration::hours(18),
///                 BoundInclusivity::Exclusive,
///             ))),
///         ),
///     ],
/// );
/// ```
#[derive(Debug, Clone, Hash)]
pub struct LayeredRelativeBounds<I1, I2> {
    first_layer: I1,
    second_layer: I2,
    state: LayeredBoundsState,
    // In some cases, the iterator needs to return two results at once
    queued_result: Option<LayeredBoundsStateChangeAtRelativeBound>,
    exhausted: bool,
}

impl<I1, I2> LayeredRelativeBounds<I1, I2> {
    /// Returns the current [state](LayeredBoundsState)
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// # use periodical::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound, LayeredRelativeBounds,
    /// # };
    /// let first_layer_intervals = [
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(8),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(12),
    ///         )),
    ///     ),
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(13),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(16),
    ///         )),
    ///     ),
    /// ];
    ///
    /// let second_layer_intervals = [
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(7),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(11),
    ///         )),
    ///     ),
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(14),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(18),
    ///         )),
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

impl<I1, I2> LayeredRelativeBounds<I1, I2>
where
    I1: Iterator<Item = RelativeBound>,
    I2: Iterator<Item = RelativeBound>,
{
    /// Creates a new [`LayeredRelativeBounds`]
    ///
    /// # Input requirements
    ///
    /// 1. The bounds in each layer iterator **must be sorted chronologically**
    /// 2. The bounds in each layer iterator **must not be overlapping**
    /// 3. The bounds in each layer iterator **must be paired**, that means there should be an equal amount of
    ///    [`Start`](RelativeBound::Start)s and [`End`](RelativeBound::End)s.
    ///
    /// The responsibility of verifying those requirements are left to the caller
    /// in order to prevent double-processing.
    ///
    /// Requirements 1 and 2 are automatically guaranteed if the bounds are obtained from
    /// [`RelativeUnitedBoundsIter`](crate::iter::intervals::united_bounds::RelativeUnitedBoundsIter).
    ///
    /// Requirement 3 is automatically guaranteed if the bounds are obtained from
    /// a set of [intervals](crate::intervals::relative::RelativeInterval)
    /// or from [bound pairs](crate::intervals::relative::RelativeBounds) and then processed through
    /// [`RelativeBoundsIter`](crate::iter::intervals::bounds::RelativeBoundsIter).
    #[must_use]
    pub fn new(first_layer_iter: I1, second_layer_iter: I2) -> LayeredRelativeBounds<Peekable<I1>, Peekable<I2>> {
        LayeredRelativeBounds {
            first_layer: first_layer_iter.peekable(),
            second_layer: second_layer_iter.peekable(),
            state: LayeredBoundsState::default(),
            queued_result: None,
            exhausted: false,
        }
    }
}

impl<I1, I2> Iterator for LayeredRelativeBounds<Peekable<I1>, Peekable<I2>>
where
    I1: Iterator<Item = RelativeBound>,
    I2: Iterator<Item = RelativeBound>,
{
    type Item = LayeredBoundsStateChangeAtRelativeBound;

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
                first_layer_peeked_start.bound_cmp(second_layer_peeked_end),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
                &mut self.queued_result,
            )),
            (
                Some(RelativeBound::End(first_layer_peeked_end)),
                Some(RelativeBound::Start(second_layer_peeked_start)),
            ) => Some(layered_rel_bounds_change_end_start(
                old_state,
                first_layer_peeked_end.bound_cmp(second_layer_peeked_start),
                &mut self.first_layer,
                &mut self.second_layer,
                &mut self.state,
                &mut self.queued_result,
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

impl<I1, I2> FusedIterator for LayeredRelativeBounds<Peekable<I1>, Peekable<I2>>
where
    I1: Iterator<Item = RelativeBound>,
    I2: Iterator<Item = RelativeBound>,
{
}

/// Computes the state change - first layer peeked, start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when only the first layer has a peeked value
/// and is a start bound.
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
    first_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
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

/// Computes the state change - first layer peeked, end bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when only the first layer has a peeked value
/// and is an end bound.
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
    first_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
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

/// Computes the state change - second layer peeked, start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when only the second layer has a peeked value
/// and is a start bound.
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
    second_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
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

/// Computes the state change - second layer peeked, end bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when only the second layer has a peeked value
/// and is an end bound.
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
    second_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
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

/// Computes the state change - both layers peeked, both start bounds
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when both layers have a peeked value
/// and both are start bounds.
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
    first_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
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

            // Advance the second layer's iterator since both layers' bounds are equal
            second_layer.next();

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

/// Computes the state change - both layers peeked, first layer start bound, second layer end bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when both layers have a peeked value
/// and the first layer is a start bound and the second layer is an end bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
/// 3. The comparison between [`RelativeStartBound`] and [`RelativeEndBound`] returned [`None`]
#[must_use]
pub fn layered_rel_bounds_change_start_end(
    old_state: LayeredBoundsState,
    start_end_cmp: BoundOrdering,
    first_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
    state_mut: &mut LayeredBoundsState,
    queued_result_mut: &mut Option<LayeredBoundsStateChangeAtRelativeBound>,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    match start_end_cmp.disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient) {
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
            let finite_first_layer_start = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else")
                .finite()
                .expect("An RelativeStartBound and an RelativeEndBound can only be equal if they are finite");

            let finite_second_layer_end = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else")
                .finite()
                .expect("An RelativeStartBound and an RelativeEndBound can only be equal if they are finite");

            if finite_first_layer_start == finite_second_layer_end {
                let mut end_of_second_layer = finite_second_layer_end; // Copy
                end_of_second_layer.set_inclusivity(BoundInclusivity::Exclusive);

                let change_to_return = Change::new(
                    old_state,
                    LayeredBoundsState::BothLayers,
                    Some(RelativeEndBound::Finite(end_of_second_layer)),
                    // We use `finite_first_layer_start` here because it overlaps with the second layer's end
                    // for a single instant
                    Some(RelativeStartBound::Finite(finite_first_layer_start)),
                );

                let mut start_of_first_layer = finite_first_layer_start; // Copy
                start_of_first_layer.set_inclusivity(BoundInclusivity::Exclusive);

                // Since the queued result will always be emptied before any of this logic is run again,
                // we can safely modify `state_mut` here.
                *state_mut = LayeredBoundsState::FirstLayer;

                *queued_result_mut = Some(Change::new(
                    LayeredBoundsState::BothLayers,
                    *state_mut,
                    Some(RelativeEndBound::Finite(finite_first_layer_start)),
                    Some(RelativeStartBound::Finite(start_of_first_layer)),
                ));

                change_to_return
            } else {
                *state_mut = (*state_mut)
                    .add(LayeredBoundsState::FirstLayer)
                    .sub(LayeredBoundsState::SecondLayer);

                Change::new(
                    old_state,
                    *state_mut,
                    Some(RelativeEndBound::Finite(finite_second_layer_end)),
                    Some(RelativeStartBound::Finite(finite_first_layer_start)),
                )
            }
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

/// Computes the state change - both layers peeked, first layer end bound, second layer start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when both layers have a peeked value
/// and the first layer is an end bound and the second layer is a start bound.
///
/// # Panics
///
/// Shouldn't panic but could if one of the following is true:
///
/// 1. The peeked value of a layer wasn't equal to the value returned by calling `next()` on that layer
/// 2. The value returned by `next()` on the layer wasn't of the expected variant
/// 3. The comparison between [`RelativeEndBound`] and [`RelativeStartBound`] returned [`None`]
#[must_use]
pub fn layered_rel_bounds_change_end_start(
    old_state: LayeredBoundsState,
    end_start_cmp: BoundOrdering,
    first_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
    state_mut: &mut LayeredBoundsState,
    queued_result_mut: &mut Option<LayeredBoundsStateChangeAtRelativeBound>,
) -> LayeredBoundsStateChangeAtRelativeBound {
    type Change = LayeredBoundsStateChangeAtRelativeBound;

    match end_start_cmp.disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient) {
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
            let finite_first_layer_end = first_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .end()
                .expect("Matched for `RelativeBound::End(_)`, destructured to something else")
                .finite()
                .expect("An RelativeStartBound and an RelativeEndBound can only be equal if they are finite");

            let finite_second_layer_start = second_layer
                .next()
                .expect("Peeked `Some`, got `None` after calling `next()`")
                .start()
                .expect("Matched for `RelativeBound::Start(_)`, destructured to something else")
                .finite()
                .expect("An RelativeStartBound and an RelativeEndBound can only be equal if they are finite");

            if finite_first_layer_end == finite_second_layer_start {
                let mut end_of_first_layer = finite_first_layer_end; // Copy
                end_of_first_layer.set_inclusivity(BoundInclusivity::Exclusive);

                let change_to_return = Change::new(
                    old_state,
                    LayeredBoundsState::BothLayers,
                    Some(RelativeEndBound::Finite(end_of_first_layer)),
                    // We use `finite_second_layer_start` here because it overlaps with the first layer's end
                    // for a single instant
                    Some(RelativeStartBound::Finite(finite_second_layer_start)),
                );

                let mut start_of_second_layer = finite_second_layer_start; // Copy
                start_of_second_layer.set_inclusivity(BoundInclusivity::Exclusive);

                // Since the queued result will always be emptied before any of this logic is run again,
                // we can safely modify `state_mut` here.
                *state_mut = LayeredBoundsState::SecondLayer;

                *queued_result_mut = Some(Change::new(
                    LayeredBoundsState::BothLayers,
                    *state_mut,
                    Some(RelativeEndBound::Finite(finite_second_layer_start)),
                    Some(RelativeStartBound::Finite(start_of_second_layer)),
                ));

                change_to_return
            } else {
                *state_mut = (*state_mut)
                    .sub(LayeredBoundsState::FirstLayer)
                    .add(LayeredBoundsState::SecondLayer);

                Change::new(
                    old_state,
                    *state_mut,
                    Some(RelativeEndBound::Finite(finite_first_layer_end)),
                    Some(RelativeStartBound::Finite(finite_second_layer_start)),
                )
            }
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

/// Computes the state change - both layers peeked, first layer end bound, second layer start bound
///
/// Computes the [`LayeredBoundsStateChangeAtRelativeBound`] when both layers have a peeked value
/// and both are end bounds.
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
    first_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
    second_layer: &mut Peekable<impl Iterator<Item = RelativeBound>>,
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

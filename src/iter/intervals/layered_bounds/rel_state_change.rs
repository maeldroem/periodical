//! State change for layered relative bounds iterators

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::relative::{RelativeEndBound, RelativeStartBound};
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

/// State change of a
/// [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::relative::LayeredRelativeBounds)
///
/// This state change is situated using relative bounds: [`RelativeStartBound`]
/// and [`RelativeEndBound`].
///
/// A state change represents a point in the iterator where the
/// [`LayeredBoundsState`] changes. It also stores with it _when_ the change
/// happened, more precisely, when the old state ends, given by
/// [`old_state_end`](LayeredBoundsStateChangeAtRelativeBound::old_state_end),
/// and when the new state begins,
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
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_end_bound()),
    ///     Some(
    ///         RelativeFiniteBoundPosition::new_with_inclusivity(
    ///             SignedDuration::from_hours(8),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
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
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_end_bound()),
    ///     Some(
    ///         RelativeFiniteBoundPosition::new_with_inclusivity(
    ///             SignedDuration::from_hours(8),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
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
    /// Returns an [`RelativeEndBound`] wrapped in an [`Option`] that
    /// corresponds to the end of the old state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at
    /// [`RelativeStartBound::InfinitePast`], therefore there is nothing
    /// that can be positioned _before_ infinite past.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_end_bound()),
    ///     Some(
    ///         RelativeFiniteBoundPosition::new_with_inclusivity(
    ///             SignedDuration::from_hours(8),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
    /// );
    ///
    /// assert_eq!(
    ///     change.old_state_end(),
    ///     Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8),).to_end_bound()),
    /// );
    /// ```
    #[must_use]
    pub fn old_state_end(&self) -> Option<RelativeEndBound> {
        self.old_state_end
    }

    /// Returns the start of the new state
    ///
    /// Returns an [`RelativeStartBound`] wrapped in an [`Option`] that
    /// corresponds to the start of the new state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at
    /// [`RelativeEndBound::InfiniteFuture`], therefore there is nothing
    /// that can be positioned _after_ infinite future.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtRelativeBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtRelativeBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_end_bound()),
    ///     Some(
    ///         RelativeFiniteBoundPosition::new_with_inclusivity(
    ///             SignedDuration::from_hours(8),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
    /// );
    ///
    /// assert_eq!(
    ///     change.new_state_start(),
    ///     Some(
    ///         RelativeFiniteBoundPosition::new_with_inclusivity(
    ///             SignedDuration::from_hours(8),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound()
    ///     ),
    /// );
    /// ```
    #[must_use]
    pub fn new_state_start(&self) -> Option<RelativeStartBound> {
        self.new_state_start
    }
}

//! State change for layered absolute bounds iterators

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsEndBound, AbsStartBound};
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

/// State change of a
/// [`LayeredAbsBounds`](crate::iter::intervals::layered_bounds::absolute::LayeredAbsBounds)
///
/// This state change is situated using absolute bounds: [`AbsStartBound`]
/// and [`AbsEndBound`].
///
/// A state change represents a point in the iterator where the
/// [`LayeredBoundsState`] changes. It also stores with it _when_ the change
/// happened, more precisely, when the old state ends, given by
/// [`old_state_end`](LayeredBoundsStateChangeAtAbsBound::old_state_end),
/// and when the new state begins,
/// given by [`new_state_start`](LayeredBoundsStateChangeAtAbsBound::new_state_start).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct LayeredBoundsStateChangeAtAbsBound {
    old_state: LayeredBoundsState,
    new_state: LayeredBoundsState,
    old_state_end: Option<AbsEndBound>,
    new_state_start: Option<AbsStartBound>,
    // Could add a `cause` field containing the original AbsBound, but idk if it's useful to do that now
}

impl LayeredBoundsStateChangeAtAbsBound {
    /// Creates a new [`LayeredBoundsStateChangeAtAbsBound`]
    #[must_use]
    pub fn new(
        old_state: LayeredBoundsState,
        new_state: LayeredBoundsState,
        old_state_end: Option<AbsEndBound>,
        new_state_start: Option<AbsStartBound>,
    ) -> Self {
        LayeredBoundsStateChangeAtAbsBound {
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
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     Some(
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
    /// );
    ///
    /// assert_eq!(change.old_state(), LayeredBoundsState::NoLayers);
    /// # Ok::<(), Box<dyn Error>>(())
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
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     Some(
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
    /// );
    ///
    /// assert_eq!(change.new_state(), LayeredBoundsState::FirstLayer);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new_state(&self) -> LayeredBoundsState {
        self.new_state
    }

    /// Returns the end of the old state
    ///
    /// Returns an [`AbsEndBound`] wrapped in an [`Option`] that
    /// corresponds to the end of the old state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at
    /// [`AbsStartBound::InfinitePast`], therefore there is nothing
    /// that can be positioned _before_ infinite past.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     Some(
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
    /// );
    ///
    /// assert_eq!(
    ///     change.old_state_end(),
    ///     Some(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound()
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn old_state_end(&self) -> Option<AbsEndBound> {
        self.old_state_end
    }

    /// Returns the start of the new state
    ///
    /// Returns an [`AbsStartBound`] wrapped in an [`Option`] that
    /// corresponds to the start of the new state.
    ///
    /// It is wrapped in an [`Option`] as the change can happen at
    /// [`AbsEndBound::InfiniteFuture`], therefore there is nothing
    /// that can be positioned _after_ infinite future.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::iter::intervals::layered_bounds::{
    /// #     LayeredBoundsState, LayeredBoundsStateChangeAtAbsBound,
    /// # };
    /// let change = LayeredBoundsStateChangeAtAbsBound::new(
    ///     LayeredBoundsState::NoLayers,
    ///     LayeredBoundsState::FirstLayer,
    ///     Some(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    ///     Some(
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound(),
    ///     ),
    /// );
    ///
    /// assert_eq!(
    ///     change.new_state_start(),
    ///     Some(
    ///         AbsFiniteBoundPos::new_with_incl(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///             BoundInclusivity::Exclusive,
    ///         )
    ///         .to_start_bound()
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn new_state_start(&self) -> Option<AbsStartBound> {
        self.new_state_start
    }
}

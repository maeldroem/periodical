//! Layered bounds iterator
//!
//! Iterator used for tracking layer changes between two sets of bounds,
//! interpreted as two separate _layers_.
//!
//! This iterator is very useful for [set operations](crate::iter::intervals::layered_bounds_set_ops) but also
//! for making the process of dealing with bounds flexible, as layered bounds
//! iterator return changes in the [`LayeredBoundsState`] using either
//! [`LayeredBoundsStateChangeAtAbsBound`] for absolute bounds,
//! or [`LayeredBoundsStateChangeAtRelBound`] for relative bounds.
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
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
//!         .collect::<Vec<_>>(),
//!     vec![
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::NoLayers,
//!             LayeredBoundsState::SecondLayer,
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 07:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 07:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::SecondLayer,
//!             LayeredBoundsState::BothLayers,
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 08:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 08:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::BothLayers,
//!             LayeredBoundsState::FirstLayer,
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 11:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 11:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::FirstLayer,
//!             LayeredBoundsState::NoLayers,
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 12:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 12:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::NoLayers,
//!             LayeredBoundsState::FirstLayer,
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 13:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 13:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::FirstLayer,
//!             LayeredBoundsState::BothLayers,
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 14:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 14:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::BothLayers,
//!             LayeredBoundsState::SecondLayer,
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 16:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 16:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsBound::new(
//!             LayeredBoundsState::SecondLayer,
//!             LayeredBoundsState::NoLayers,
//!             Some(
//!                 AbsFiniteBoundPos::new(
//!                     "2025-01-01 18:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsFiniteBoundPos::new_with_incl(
//!                     "2025-01-01 18:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!     ],
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

pub mod abs_state_change;
pub mod absolute;
pub mod rel_state_change;
pub mod relative;
pub mod state;

#[cfg(test)]
mod abs_state_change_tests;
#[cfg(test)]
mod absolute_tests;
#[cfg(test)]
mod rel_state_change_tests;
#[cfg(test)]
mod relative_tests;
#[cfg(test)]
mod state_tests;

#[doc(inline)]
pub use abs_state_change::LayeredBoundsStateChangeAtAbsBound;
#[doc(inline)]
pub use absolute::LayeredAbsBounds;
#[doc(inline)]
pub use rel_state_change::LayeredBoundsStateChangeAtRelBound;
#[doc(inline)]
pub use relative::LayeredRelBounds;
#[doc(inline)]
pub use state::LayeredBoundsState;

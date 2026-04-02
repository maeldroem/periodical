//! Layered bounds iterator
//!
//! Iterator used for tracking layer changes between two sets of bounds,
//! interpreted as two separate _layers_.
//!
//! This iterator is very useful for [set operations](crate::iter::intervals::layered_bounds_set_ops) but also
//! for making the process of dealing with bounds flexible, as layered bounds
//! iterator return changes in the [`LayeredBoundsState`] using either
//! [`LayeredBoundsStateChangeAtAbsoluteBound`] for absolute bounds,
//! or [`LayeredBoundsStateChangeAtRelativeBound`] for relative bounds.
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
//! # use periodical::iter::intervals::layered_bounds::{
//! #     LayeredAbsoluteBounds, LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
//! # };
//! let first_layer_intervals = [
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 12:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 13:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//! ];
//!
//! let second_layer_intervals = [
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 07:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 11:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 14:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new(
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
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::NoLayers,
//!             LayeredBoundsState::SecondLayer,
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 07:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 07:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::SecondLayer,
//!             LayeredBoundsState::BothLayers,
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 08:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 08:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::BothLayers,
//!             LayeredBoundsState::FirstLayer,
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 11:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 11:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::FirstLayer,
//!             LayeredBoundsState::NoLayers,
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 12:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 12:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::NoLayers,
//!             LayeredBoundsState::FirstLayer,
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 13:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 13:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::FirstLayer,
//!             LayeredBoundsState::BothLayers,
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 14:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 14:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::BothLayers,
//!             LayeredBoundsState::SecondLayer,
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 16:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
//!                     "2025-01-01 16:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                     BoundInclusivity::Exclusive,
//!                 )
//!                 .to_start_bound()
//!             ),
//!         ),
//!         LayeredBoundsStateChangeAtAbsoluteBound::new(
//!             LayeredBoundsState::SecondLayer,
//!             LayeredBoundsState::NoLayers,
//!             Some(
//!                 AbsoluteFiniteBound::new(
//!                     "2025-01-01 18:00:00[Europe/Oslo]"
//!                         .parse::<Zoned>()?
//!                         .timestamp(),
//!                 )
//!                 .to_end_bound()
//!             ),
//!             Some(
//!                 AbsoluteFiniteBound::new_with_inclusivity(
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

use crate::utils::{inline_docs, tests};

pub mod abs_state_change;
pub mod absolute;
pub mod rel_state_change;
pub mod relative;
pub mod state;

tests! {
    mod abs_state_change_tests;
    mod absolute_tests;
    mod rel_state_change_tests;
    mod relative_tests;
    mod state_tests;
}

inline_docs! {
    pub use abs_state_change::LayeredBoundsStateChangeAtAbsoluteBound;
    pub use absolute::LayeredAbsoluteBounds;
    pub use rel_state_change::LayeredBoundsStateChangeAtRelativeBound;
    pub use relative::LayeredRelativeBounds;
    pub use state::LayeredBoundsState;
}

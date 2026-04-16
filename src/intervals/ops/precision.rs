//! Precision change for intervals and bounds
//!
//! This module is in charge of handling the act of changing the precision of
//! intervals and bounds: (re-)_precising_.
//!
//! Precising intervals and bounds works differently depending
//! on their [`Relativity`](crate::intervals::meta::Relativity).
//!
//! For absolute structures, [`PreciseAbsoluteInterval`] handles intervals,
//! [`PreciseAbsoluteBound`] handles bounds.
//!
//! The precision itself is defined by [`Precision`](crate::ops::Precision).
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use std::time::Duration;
//! # use jiff::Zoned;
//! # use jiff::tz::TimeZone;
//! # use periodical::ops::{Precision, PrecisionMode};
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:03:29.591[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 15:57:44.041[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! assert_eq!(
//!     interval.precise_interval(
//!         TimeZone::get("Europe/Oslo")?,
//!         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
//!     ),
//!     Ok(AbsoluteBoundPair::new(
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBound::new(
//!             "2025-01-01 15:55:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     )),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::utils::inline_docs;

pub mod absolute;
pub mod relative;

inline_docs! {
    pub use absolute::{PreciseAbsoluteBound, PreciseAbsoluteInterval};
    pub use relative::{PreciseRelativeBound, PreciseRelativeInterval};
}

//! Precision change for intervals and bounds
//!
//! This module is in charge of handling the act of changing the precision of
//! intervals and bounds: (re-)_precising_.
//!
//! Precising intervals and bounds work differently depending
//! on their [`Relativity`](crate::intervals::meta::Relativity).
//!
//! For absolute structures, [`PreciseAbsInterval`] handles intervals,
//! [`PreciseAbsBound`] handles bounds.
//!
//! For relative structures, [`PreciseRelInterval`] handles intervals,
//! [`PreciseRelBound`] handles bounds.
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
//! # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
//! # use periodical::intervals::ops::precision::PreciseAbsInterval;
//! let interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 08:03:29.591[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 15:57:44.041[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! assert_eq!(
//!     interval.precise(
//!         TimeZone::get("Europe/Oslo")?,
//!         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
//!     ),
//!     Ok(AbsBoundPair::new(
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsFiniteBoundPos::new(
//!             "2025-01-01 15:55:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     )),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

pub mod absolute;
pub mod relative;

#[doc(inline)]
pub use absolute::{PreciseAbsBound, PreciseAbsInterval};
#[doc(inline)]
pub use relative::{PreciseRelBound, PreciseRelInterval};

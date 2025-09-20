//! Intervals
//!
//! # Interval structure and terminology
//!
//! Interval refers to an interval, a range, like in mathematics. But if we are talking strictly about this crate,
//! then an interval, such as [`AbsoluteInterval`] and [`RelativeInterval`] are enumerators over specific intervals,
//! like [`BoundedAbsoluteInterval`] or [`HalfBoundedRelativeInterval`].
//!
//! Those specific intervals must conserve their invariants.
//! A bounded interval must remain bounded, a half-bounded interval must remain half-bounded.
//!
//! All such intervals are can be interpreted of a pair of bounds, like [`AbsoluteBounds`] and [`RelativeBounds`],
//! but in practice, specific intervals only store the kind of data they absolutely need.
//! Every interval can be converted to and created from a pair of bounds, though.
//!
//! They may also come in _emptiable_ variants, like [`EmptiableAbsoluteBounds`] and [`EmptiableRelativeBounds`],
//! that are similar to the previously mentioned pair of bounds, but support the representation
//! of [empty intervals](special::EmptyInterval).
//!
//! Those pairs of bounds are comprised of individual start and end bounds,
//! representing the start and end point of intervals.
//!
//! When coming from an interval, they have the following invariants:
//!
//! 1. The start and end must be in chronological order
//! 2. If both points are at the same position,
//!    their [bound inclusivities](meta::BoundInclusivity) can only be [inclusive](meta::BoundInclusivity::Inclusive)
//!
//! Bounds can be modified however you want, as they don't need to conserve invariants regarding [openness](Openness)
//! of their bounds.
//!
//! A way to represent an individual bound, regardless of its _source_ (start/end) exists:
//! [`AbsoluteBound`] and [`RelativeBound`].
//!
//! While processing intervals through operations like unions and intersections can yield a different kind of interval,
//! they never mutate themselves in order to represent this new state, as they have to conserve their invariant
//! regarding [bound openness](Openness). This is the difference between an interval and bounds in this crate.
//!
//! Pairs of bounds are composed of both a start bound (e.g. [`AbsoluteStartBound`], [`RelativeStartBound`])
//! and an end bound (e.g. [`AbsoluteEndBound`], [`RelativeEndBound`]).
//!
//! Those individual bounds represent the start and end of their parent, supporting an infinite start/end via their
//! `InfinitePast` (for start bounds) or `InfiniteFuture` (for end bounds) variants.
//! In the case of a finite bound, they contain an [`AbsoluteFiniteBound`](absolute::AbsoluteFiniteBound)
//! for absolute bounds, or a [`RelativeFiniteBound`](relative::RelativeFiniteBound) for relative bounds.
//!
//! The reason why start and end bounds are separate is simple: [exclusivity](meta::BoundInclusivity::Exclusive)
//! doesn't mean the same thing depending on the _direction_ of the bound.
//! For example, an exclusive start bound at `2025-01-01 00:00:00` would mean everything _after_ this point in time,
//! while an exclusive end bound at `2025-01-01 00:00:00` would mean everything _before_ this point in time.
//!
//! While they are separate, their finite variants are not. This means their [inclusivity](meta::BoundInclusivity)
//! are ambiguous. This is why, when comparing them, only their time/offset is taken into account.
//!
//! [Empty intervals](EmptyInterval) are equivalent to no interval, to an empty set.
//! They do not possess a specific point in time.
//! This is the reason why they can't be compared with other intervals, or are mostly ignored.
//!
//! The reason why empty intervals exist is to provide a way to represent _no interval_,
//! without the use of an [`Option`] to represent it.
//! This also makes it compatible with other interval operations, for example you can still get the
//! complement of an empty interval, which results in an [unbounded interval](`UnboundedInterval`).
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
//! #     BoundedAbsoluteInterval,
//! # };
//! let from = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
//! let to = "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?;
//!
//! // Creating an interval from a specific interval type
//! let first_interval = AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(from, to));
//!
//! // Creating a pair of bounds..
//! let bounds_for_second_interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(from)),
//!     AbsoluteEndBound::InfiniteFuture,
//! );
//!
//! // ..For creating an interval
//! let second_interval = AbsoluteInterval::from(bounds_for_second_interval);
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

pub mod absolute;
pub mod bound_position;
pub mod meta;
pub mod ops;
pub mod prelude;
pub mod relative;
pub mod special;

#[cfg(test)]
mod absolute_tests;
#[cfg(test)]
mod bound_position_tests;
#[cfg(test)]
mod meta_tests;
#[cfg(test)]
mod relative_tests;
#[cfg(test)]
mod special_tests;

pub use absolute::{
    AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, BoundedAbsoluteInterval,
    EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
pub use meta::{Emptiable, HasBoundInclusivity, HasDuration, HasOpenness, HasRelativity, Openness, Relativity};
pub use relative::{
    BoundedRelativeInterval, EmptiableRelativeBounds, HalfBoundedRelativeInterval, HasEmptiableRelativeBounds,
    HasRelativeBounds, RelativeBound, RelativeBounds, RelativeEndBound, RelativeInterval, RelativeStartBound,
};
pub use special::{EmptyInterval, UnboundedInterval};

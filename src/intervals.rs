//! Intervals
//!
//! # Interval structure and terminology
//!
//! Interval refers to an interval, a range, like in mathematics. But if we are
//! talking strictly about this crate, then an interval, such as
//! [`AbsoluteInterval`](absolute::AbsoluteInterval)
//! and [`RelativeInterval`][relative::RelativeInterval] are enumerators
//! over specific intervals, like
//! [`BoundedAbsoluteInterval`][absolute::BoundedAbsoluteInterval]
//! or [`HalfBoundedRelativeInterval`][relative::HalfBoundedRelativeInterval].
//!
//! Those specific intervals must conserve their invariants.
//! A bounded interval must remain bounded, a half-bounded interval must remain
//! half-bounded.
//!
//! All such intervals are can be interpreted of a pair of bounds, like
//! [`AbsoluteBoundPair`](absolute::AbsoluteBoundPair)
//! and [`RelativeBoundPair`][relative::RelativeBoundPair], but in practice,
//! specific intervals only store the kind of data they absolutely need.
//! Every interval can be converted to and created from a pair of bounds,
//! though.
//!
//! They may also come in _emptiable_ variants, like
//! [`EmptiableAbsoluteBoundPair`](absolute::EmptiableAbsoluteBoundPair)
//! and [`EmptiableRelativeBoundPair`](relative::EmptiableRelativeBoundPair),
//! that are similar to the previously mentioned pair of bounds, but support the
//! representation of [empty intervals](special::EmptyInterval).
//!
//! Those pairs of bounds are comprised of individual start and end bounds,
//! representing the start and end point of intervals.
//!
//! When coming from an interval, they have the following invariants:
//!
//! 1. The start and end must be in chronological order
//! 2. If both points are at the same position, their [bound
//!    inclusivities](meta::BoundInclusivity) can only be
//!    [inclusive](meta::BoundInclusivity::Inclusive)
//!
//! Bounds can be modified however you want, as they don't need to conserve
//! invariants regarding [openness](meta::Openness) of their bounds.
//!
//! A way to represent an individual bound, regardless of its _source_
//! (start/end) exists: [`AbsoluteBound`](absolute::AbsoluteBoundPair) and
//! [`RelativeBound`](relative::RelativeBoundPair).
//!
//! While processing intervals through operations like unions and intersections
//! can yield a different kind of interval, they never mutate themselves in
//! order to represent this new state, as they have to conserve their invariant
//! regarding [bound openness](meta::Openness). This is the difference between
//! an interval and bounds in this crate.
//!
//! Pairs of bounds are composed of both a start bound (e.g.
//! [`AbsoluteStartBound`](absolute::AbsoluteStartBound),
//! [`RelativeStartBound`](relative::RelativeStartBound))
//! and an end bound (e.g. [`AbsoluteEndBound`](absolute::AbsoluteEndBound),
//! [`RelativeEndBound`](relative::RelativeEndBound)).
//!
//! Those individual bounds represent the start and end of their parent,
//! supporting an infinite start/end via their `InfinitePast` (for start bounds)
//! or `InfiniteFuture` (for end bounds) variants. In the case of a finite
//! bound, they contain an
//! [`AbsoluteFiniteBound`](absolute::AbsoluteFiniteBound) for absolute bounds,
//! or a [`RelativeFiniteBound`](relative::RelativeFiniteBound) for relative
//! bounds.
//!
//! The reason why start and end bounds are separate is simple:
//! [exclusivity](meta::BoundInclusivity::Exclusive) doesn't mean the same thing
//! depending on the _direction_ of the bound. For example, an exclusive start
//! bound at `2025-01-01 00:00:00` would mean everything _after_ this point in
//! time, while an exclusive end bound at `2025-01-01 00:00:00` would mean
//! everything _before_ this point in time.
//!
//! While they are separate, their finite variants are not. This means their
//! [inclusivity](meta::BoundInclusivity) are ambiguous. This is why, when
//! comparing them, only their time/offset is taken into account.
//!
//! [Empty intervals](special::EmptyInterval) are equivalent to no interval, to
//! an empty set. They do not possess a specific point in time.
//! This is the reason why they can't be compared with other intervals, or are
//! mostly ignored.
//!
//! The reason why empty intervals exist is to provide a way to represent _no
//! interval_, without the use of an [`Option`] to represent it.
//! This also makes it compatible with other interval operations, for example
//! you can still get the complement of an empty interval, which results in an
//! [unbounded interval](special::UnboundedInterval).
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Timestamp;
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
//! #     BoundedAbsoluteInterval,
//! # };
//! let from = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
//! let to = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
//!
//! // Creating an interval from a specific interval type
//! let first_interval = BoundedAbsoluteInterval::new(from, to).to_interval();
//!
//! // Creating a pair of bounds..
//! let bounds_for_second_interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(from).to_start_bound(),
//!     AbsoluteEndBound::InfiniteFuture,
//! );
//!
//! // ..For creating an interval
//! let second_interval = AbsoluteInterval::from(bounds_for_second_interval);
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::utils::tests;

pub mod absolute;
pub mod bound_position;
pub mod convenience;
pub mod meta;
pub mod ops;
pub mod relative;
pub mod special;

tests! {
    mod absolute_tests;
    mod bound_position_tests;
    mod meta_tests;
    mod relative_tests;
    mod special_tests;
}

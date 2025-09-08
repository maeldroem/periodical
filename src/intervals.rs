//! Intervals
//!
//! # Interval structure and terminology
//!
//! Interval refers to an interval, a range, like in mathematics. But if we are talking strictly about this crate,
//! then an interval, such as [`AbsoluteInterval`](absolute::AbsoluteInterval) and [`RelativeInterval`](relative::RelativeInterval) are enumerators over specific intervals,
//! like [`BoundedAbsoluteInterval`] or [`HalfBoundedRelativeInterval`].
//!
//! Those specific intervals must conserve their invariants. A bounded interval must remain bounded, a half-bounded interval
//! must remain half-bounded.
//!
//! All such intervals are composed of bounds (e.g. [`AbsoluteBounds`], [`RelativeBounds`]).
//! They may also come in _emptiable_ variants (e.g. [`EmptiableAbsoluteBounds`], [`EmptiableRelativeBounds`]).
//! Bounds represent the start and end point of intervals, and they have the following invariants:
//!
//! 1. The start and end must be in chronological order
//! 2. If both points are at the same position, their _bound inclusivities_ can only be [inclusive](BoundInclusivity::Inclusive)
//!
//! Bounds can be modified however you want, as they don't conserve invariants regarding [openness](Openness)
//! of their bounds.
//!
//! _Emptiable_ bounds are bounds that can also represent an [empty interval](EmptyInterval).
//!
//! While processing intervals through operations like unions and intersections can yield a different kind of interval,
//! they never mutate themselves in order to represent this new state, as they have to conserve their invariant
//! regarding [bound openness](Openness). This is the difference between an interval and bounds.
//!
//! Bounds are composed of both a start bound (e.g. [`AbsoluteStartBound`], [`RelativeStartBound`]) and an end bound
//! (e.g. [`AbsoluteEndBound`], [`RelativeEndBound`]).
//!
//! Those individual bounds represent the start and end of their parent, so they cary only a [time](chrono::DateTime)
//! (or [offset](chrono::Duration) for relative bounds) as well as a [bound inclusivity](BoundInclusivity)
//! in order to determinate whether they contain or not their time/offset.
//!
//! The reason why start and end bounds are separate and not the same structure is double:
//!
//! - To determinate the bound inclusivity _direction_: an exclusive start bound at `10.0` would mean `>10.0`,
//!   while an exclusive end bound at `10.0` would mean `<10.0`
//! - To ease processing when destructuring multiple intervals in a table of individual bounds
//!
//! Individual bounds also support being at infinite points in time, such as infinitely in the future or infinitely
//! in the past.
//!
//! While they are separate, their finite variants are composed of finite bounds (e.g. [`AbsoluteFiniteBound`],
//! [`RelativeFiniteBound`]). This is because they are meant for representing a point in time with an on-off-like
//! bound inclusivity system. This is why, when comparing them, only their time/offset is taken into account.
//!
//! [Empty intervals](EmptyInterval) are equivalent to no interval, to an empty set. They do not possess
//! a specific point in time. This is the reason why they can't be compared with other intervals, or are mostly ignored.
//!
//! The reason why empty intervals exist is to provide a way to represent _no duration_ without having to use [`Option`]
//! to represent it. This also makes it compatible with other interval operations, for example you can still get the
//! complement of an empty interval, which results in an [unbounded interval](`UnboundedInterval`).

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
    AbsoluteBound, AbsoluteBounds, AbsoluteInterval, BoundedAbsoluteInterval, EmptiableAbsoluteBounds,
    HalfBoundedAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
pub use meta::{Emptiable, HasBoundInclusivity, HasDuration, HasOpenness, HasRelativity};
pub use relative::{
    BoundedRelativeInterval, EmptiableRelativeBounds, HalfBoundedRelativeInterval, HasEmptiableRelativeBounds,
    HasRelativeBounds, RelativeBound, RelativeBounds, RelativeInterval,
};

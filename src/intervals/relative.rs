//! Relative intervals
//!
//! Relative intervals are set in relative time, that is to say that are bound to
//! [offset(s) as `SignedDuration`](jiff::SignedDuration) when applicable.
//!
//! The most common relative interval objects you will encounter are
//!
//! - [`RelBoundPair`]
//! - [`EmptiableRelBoundPair`]
//! - [`BoundedRelInterval`]
//! - [`HalfBoundedRelInterval`]
//!
//! Refer to [the `intervals` module](crate::intervals) for more information about how intervals are structured.

use std::error::Error;
use std::fmt::Display;

use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::{BoundOrd, BoundOrdering, BoundOverlapAmbiguity};

pub mod bound;
pub mod bound_pair;
pub mod bounded_interval;
pub mod emptiable_bound_pair;
pub mod emptiable_interval;
pub mod end_bound;
pub mod finite_bound;
pub mod finite_bound_position;
pub mod finite_end_bound;
pub mod finite_start_bound;
pub mod half_bounded_interval;
pub mod half_bounded_to_future_interval;
pub mod half_bounded_to_past_interval;
pub mod interval;
pub mod start_bound;

#[cfg(test)]
mod bound_pair_tests;
#[cfg(test)]
mod bound_tests;
#[cfg(test)]
mod bounded_interval_tests;
#[cfg(test)]
mod emptiable_bound_pair_tests;
#[cfg(test)]
mod emptiable_interval_tests;
#[cfg(test)]
mod end_bound_tests;
#[cfg(test)]
mod finite_bound_position_tests;
#[cfg(test)]
mod finite_bound_tests;
#[cfg(test)]
mod finite_end_bound_tests;
#[cfg(test)]
mod finite_start_bound_tests;
#[cfg(test)]
mod half_bounded_interval_tests;
#[cfg(test)]
mod half_bounded_to_future_interval_tests;
#[cfg(test)]
mod half_bounded_to_past_interval_tests;
#[cfg(test)]
mod interval_tests;
#[cfg(test)]
mod start_bound_tests;

#[doc(inline)]
pub use bound::RelBound;
#[doc(inline)]
pub use bound_pair::{HasRelBoundPair, RelBoundPair};
#[doc(inline)]
pub use bounded_interval::BoundedRelInterval;
#[doc(inline)]
pub use emptiable_bound_pair::{EmptiableRelBoundPair, HasEmptiableRelBoundPair};
#[doc(inline)]
pub use emptiable_interval::EmptiableRelInterval;
#[doc(inline)]
pub use end_bound::RelEndBound;
#[doc(inline)]
pub use finite_bound::RelFiniteBound;
#[doc(inline)]
pub use finite_bound_position::RelFiniteBoundPos;
#[doc(inline)]
pub use finite_end_bound::RelFiniteEndBound;
#[doc(inline)]
pub use finite_start_bound::RelFiniteStartBound;
#[doc(inline)]
pub use half_bounded_interval::HalfBoundedRelInterval;
#[doc(inline)]
pub use half_bounded_to_future_interval::HalfBoundedToFutureRelInterval;
#[doc(inline)]
pub use half_bounded_to_past_interval::HalfBoundedToPastRelInterval;
#[doc(inline)]
pub use interval::RelInterval;
#[doc(inline)]
pub use start_bound::RelStartBound;

/// Swaps a relative finite start bound with a relative finite end bound
///
/// # Examples
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     swap_rel_finite_start_end_bounds,
/// # };
/// let first_offset = SignedDuration::from_hours(2);
/// let second_offset = SignedDuration::from_hours(7);
///
/// let mut start = RelFiniteBoundPos::new(first_offset).to_finite_start_bound();
/// let mut end = RelFiniteBoundPos::new(second_offset).to_finite_end_bound();
///
/// swap_rel_finite_start_end_bounds(&mut start, &mut end);
///
/// assert_eq!(start.pos().offset(), second_offset);
/// assert_eq!(end.pos().offset(), first_offset);
/// ```
pub fn swap_rel_finite_start_end_bounds(finite_start: &mut RelFiniteStartBound, finite_end: &mut RelFiniteEndBound) {
    let RelFiniteStartBound(finite_start_pos) = finite_start;
    let RelFiniteEndBound(finite_end_pos) = finite_end;

    std::mem::swap(finite_start_pos, finite_end_pos);
}

/// Swaps a relative start bound with a relative end bound
///
/// This method is primarily used in the case where a start bound and an end
/// bound are not in chronological order.
///
/// # Examples
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{RelFiniteBoundPos, swap_rel_start_end_bounds};
/// let start_offset = SignedDuration::from_hours(2);
/// let end_offset = SignedDuration::from_hours(7);
///
/// let mut start = RelFiniteBoundPos::new(start_offset).to_start_bound();
/// let mut end = RelFiniteBoundPos::new(end_offset).to_end_bound();
///
/// swap_rel_start_end_bounds(&mut start, &mut end);
///
/// assert_eq!(start, RelFiniteBoundPos::new(end_offset).to_start_bound());
/// assert_eq!(end, RelFiniteBoundPos::new(start_offset).to_end_bound());
/// ```
pub fn swap_rel_start_end_bounds(start: &mut RelStartBound, end: &mut RelEndBound) {
    // We temporarily reborrow start and end for the match arms so that when a
    // pattern matches, they move out of their temporary scope and we can use
    // the original mutable references without guard patterns shenanigans.
    // When destructuring, however, the scope of the reborrowed value extends up to
    // where it is used within the body, So we always finish our business with
    // the reborrowed values first before accessing the original ones.
    match (&mut *start, &mut *end) {
        (RelStartBound::InfinitePast, RelEndBound::InfiniteFuture) => {},
        (RelStartBound::InfinitePast, RelEndBound::Finite(finite_end)) => {
            *start = finite_end.pos().to_start_bound();
            *end = RelEndBound::InfiniteFuture;
        },
        (RelStartBound::Finite(finite_start), RelEndBound::InfiniteFuture) => {
            *end = finite_start.pos().to_end_bound();
            *start = RelStartBound::InfinitePast;
        },
        (RelStartBound::Finite(finite_start), RelEndBound::Finite(finite_end)) => {
            swap_rel_finite_start_end_bounds(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start
/// and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelStartEndBoundsCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same offset but don't have only inclusive bound inclusivities
    SameOffsetButNotDoublyInclusive,
}

impl Display for RelStartEndBoundsCheckForIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StartPastEnd => write!(f, "Start bound is past the end bound"),
            Self::SameOffsetButNotDoublyInclusive => write!(
                f,
                "Both bounds are on the same offset but don't have only inclusive bound inclusivities"
            ),
        }
    }
}

impl Error for RelStartEndBoundsCheckForIntervalCreationError {}

/// Checks whether the given finite start and finite end bounds are fit for creating an interval
///
/// # Errors
///
/// Returns [`StartPastEnd`](RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// if the start bound is positioned after the end bound.
///
/// Returns [`SameOffsetButNotDoublyInclusive`](RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
/// if the bounds are positioned on the same offset but are not doubly inclusive.
///
/// # Examples
///
/// ## Start past end
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     RelStartEndBoundsCheckForIntervalCreationError,
/// #     check_rel_finite_start_end_bounds_for_interval_creation,
/// # };
/// let start = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_start_bound();
/// let end = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_end_bound();
///
/// assert_eq!(
///     check_rel_finite_start_end_bounds_for_interval_creation(&start, &end),
///     Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// );
/// ```
///
/// ## Same time but not doubly inclusive
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     RelStartEndBoundsCheckForIntervalCreationError,
/// #     check_rel_finite_start_end_bounds_for_interval_creation,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// let offset = SignedDuration::from_hours(10);
/// let start = RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive)
///     .to_finite_start_bound();
/// let end = RelFiniteBoundPos::new(offset).to_finite_end_bound();
///
/// assert_eq!(
///     check_rel_finite_start_end_bounds_for_interval_creation(&start, &end),
///     Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
/// );
/// ```
///
/// ## OK
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     check_rel_finite_start_end_bounds_for_interval_creation,
/// # };
/// let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_start_bound();
/// let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_end_bound();
///
/// assert_eq!(
///     check_rel_finite_start_end_bounds_for_interval_creation(&start, &end),
///     Ok(())
/// );
/// ```
pub fn check_rel_finite_start_end_bounds_for_interval_creation(
    start: &RelFiniteStartBound,
    end: &RelFiniteEndBound,
) -> Result<(), RelStartEndBoundsCheckForIntervalCreationError> {
    match start.bound_cmp(end) {
        BoundOrdering::Less => Ok(()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(start_incl, end_incl))) => {
            if start_incl == BoundInclusivity::Inclusive && end_incl == BoundInclusivity::Inclusive {
                Ok(())
            } else {
                Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
            }
        },
        BoundOrdering::Equal(_) => unreachable!(),
        BoundOrdering::Greater => Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
    }
}

/// Checks whether the given start and end bounds are fit for creating an interval
///
/// # Errors
///
/// Returns [`StartPastEnd`](RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// if the start bound is positioned after the end bound.
///
/// Returns [`SameOffsetButNotDoublyInclusive`](RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
/// if the bounds are positioned on the same offset but are not doubly inclusive.
///
/// # Examples
///
/// ## Start past end
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     RelStartEndBoundsCheckForIntervalCreationError,
/// #     check_rel_start_end_bounds_for_interval_creation,
/// # };
/// let start = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_start_bound();
/// let end = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_end_bound();
///
/// assert_eq!(
///     check_rel_start_end_bounds_for_interval_creation(&start, &end),
///     Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// );
/// ```
///
/// ## Same time but not doubly inclusive
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     RelStartEndBoundsCheckForIntervalCreationError,
/// #     check_rel_start_end_bounds_for_interval_creation,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// let offset = SignedDuration::from_hours(10);
/// let start =
///     RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive).to_start_bound();
/// let end = RelFiniteBoundPos::new(offset).to_end_bound();
///
/// assert_eq!(
///     check_rel_start_end_bounds_for_interval_creation(&start, &end),
///     Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
/// );
/// ```
///
/// ## OK
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     check_rel_start_end_bounds_for_interval_creation,
/// # };
/// let start = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound();
/// let end = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound();
///
/// assert_eq!(
///     check_rel_start_end_bounds_for_interval_creation(&start, &end),
///     Ok(())
/// );
/// ```
pub fn check_rel_start_end_bounds_for_interval_creation(
    start: &RelStartBound,
    end: &RelEndBound,
) -> Result<(), RelStartEndBoundsCheckForIntervalCreationError> {
    match (start, end) {
        (RelStartBound::InfinitePast, _) | (_, RelEndBound::InfiniteFuture) => Ok(()),
        (RelStartBound::Finite(finite_start), RelEndBound::Finite(finite_end)) => {
            check_rel_finite_start_end_bounds_for_interval_creation(finite_start, finite_end)
        },
    }
}

/// Prepares a finite start and a finite end bound to be used for an interval
///
/// Checks whether the bounds are fit for creating an interval and automatically corrects
/// any problem.
///
/// If the start bound is past the end bound, they are swapped.
/// If the bounds are positioned on the same time but are not doubly inclusive, their bound inclusivities
/// are set to [`Inclusive`](BoundInclusivity::Inclusive).
///
/// Returns whether a change has occurred.
///
/// # Examples
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     RelStartEndBoundsCheckForIntervalCreationError,
/// #     prepare_rel_finite_start_end_bounds_for_interval_creation,
/// # };
/// let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_finite_start_bound();
/// let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_finite_end_bound();
///
/// prepare_rel_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);
///
/// assert_eq!(start.pos().offset(), SignedDuration::from_hours(8));
/// assert_eq!(end.pos().offset(), SignedDuration::from_hours(16));
/// ```
pub fn prepare_rel_finite_start_end_bounds_for_interval_creation(
    start: &mut RelFiniteStartBound,
    end: &mut RelFiniteEndBound,
) -> bool {
    match check_rel_finite_start_end_bounds_for_interval_creation(start, end) {
        Ok(()) => false,
        Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_rel_finite_start_end_bounds(start, end);
            true
        },
        Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive) => {
            let RelFiniteStartBound(finite_start) = start;
            let RelFiniteEndBound(finite_end) = end;

            finite_start.set_inclusivity(BoundInclusivity::Inclusive);
            finite_end.set_inclusivity(BoundInclusivity::Inclusive);

            true
        },
    }
}

/// Prepares a start and an end bound to be used for an interval
///
/// Checks whether the bounds are fit for creating an interval and automatically corrects
/// any problem.
///
/// If the start bound is past the end bound, they are swapped.
/// If the bounds are positioned on the same time but are not doubly inclusive, their bound inclusivities
/// are set to [`Inclusive`](BoundInclusivity::Inclusive).
///
/// Returns whether a change has occurred.
///
/// # Examples
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelFiniteBoundPos,
/// #     RelStartEndBoundsCheckForIntervalCreationError,
/// #     prepare_rel_bound_pair_for_interval_creation,
/// # };
/// let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_start_bound();
/// let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_end_bound();
///
/// prepare_rel_bound_pair_for_interval_creation(&mut start, &mut end);
///
/// assert_eq!(
///     start,
///     RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound()
/// );
/// assert_eq!(
///     end,
///     RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound()
/// );
/// ```
pub fn prepare_rel_start_end_bounds_for_interval_creation(start: &mut RelStartBound, end: &mut RelEndBound) -> bool {
    match check_rel_start_end_bounds_for_interval_creation(start, end) {
        Ok(()) => false,
        Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_rel_start_end_bounds(start, end);
            true
        },
        Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive) => {
            if let RelStartBound::Finite(RelFiniteStartBound(finite_start_mut)) = start {
                finite_start_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            if let RelEndBound::Finite(RelFiniteEndBound(finite_end_mut)) = end {
                finite_end_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            true
        },
    }
}

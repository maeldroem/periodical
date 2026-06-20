//! Absolute intervals
//!
//! Absolute intervals are set in absolute time, that is to say that are bound to [`Timestamp`](jiff::Timestamp)(s)
//! when applicable.
//!
//! The most common absolute interval objects you will encounter are
//!
//! - [`AbsBoundPair`]
//! - [`EmptiableAbsBoundPair`]
//! - [`BoundedAbsInterval`]
//! - [`HalfBoundedAbsInterval`]
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
mod interval_tests;
#[cfg(test)]
mod start_bound_tests;

#[doc(inline)]
pub use bound::AbsBound;
#[doc(inline)]
pub use bound_pair::{AbsBoundPair, HasAbsBoundPair};
#[doc(inline)]
pub use bounded_interval::BoundedAbsInterval;
#[doc(inline)]
pub use emptiable_bound_pair::{EmptiableAbsBoundPair, HasEmptiableAbsBoundPair};
#[doc(inline)]
pub use emptiable_interval::EmptiableAbsInterval;
#[doc(inline)]
pub use end_bound::AbsEndBound;
#[doc(inline)]
pub use finite_bound::AbsFiniteBound;
#[doc(inline)]
pub use finite_bound_position::AbsFiniteBoundPos;
#[doc(inline)]
pub use finite_end_bound::AbsFiniteEndBound;
#[doc(inline)]
pub use finite_start_bound::AbsFiniteStartBound;
#[doc(inline)]
pub use half_bounded_interval::HalfBoundedAbsInterval;
#[doc(inline)]
pub use half_bounded_to_future_interval::HalfBoundedToFutureAbsInterval;
#[doc(inline)]
pub use half_bounded_to_past_interval::HalfBoundedToPastAbsInterval;
#[doc(inline)]
pub use interval::AbsInterval;
#[doc(inline)]
pub use start_bound::AbsStartBound;

/// Swaps an absolute finite start bound with an absolute finite end bound
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     swap_abs_finite_start_end_bounds,
/// # };
/// let first_time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
/// let second_time = "2026-05-01 00:00:00Z".parse::<Timestamp>()?;
///
/// let mut start = AbsFiniteBoundPos::new(first_time).to_finite_start_bound();
/// let mut end = AbsFiniteBoundPos::new(second_time).to_finite_end_bound();
///
/// swap_abs_finite_start_end_bounds(&mut start, &mut end);
///
/// assert_eq!(start.pos().time(), second_time);
/// assert_eq!(end.pos().time(), first_time);
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn swap_abs_finite_start_end_bounds(finite_start: &mut AbsFiniteStartBound, finite_end: &mut AbsFiniteEndBound) {
    let AbsFiniteStartBound(finite_start_pos) = finite_start;
    let AbsFiniteEndBound(finite_end_pos) = finite_end;

    std::mem::swap(finite_start_pos, finite_end_pos);
}

/// Swaps an absolute start bound with an absolute end bound
///
/// This method is primarily used in the case where a start bound and an end
/// bound are not in chronological order.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{AbsFiniteBoundPos, swap_abs_start_end_bounds};
/// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
/// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
///
/// let mut start = AbsFiniteBoundPos::new(start_time).to_start_bound();
/// let mut end = AbsFiniteBoundPos::new(end_time).to_end_bound();
///
/// swap_abs_start_end_bounds(&mut start, &mut end);
///
/// assert_eq!(start, AbsFiniteBoundPos::new(end_time).to_start_bound());
/// assert_eq!(end, AbsFiniteBoundPos::new(start_time).to_end_bound());
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn swap_abs_start_end_bounds(start: &mut AbsStartBound, end: &mut AbsEndBound) {
    // We temporarily reborrow start and end for the match arms so that when a
    // pattern matches, they move out of their temporary scope and we can use
    // the original mutable references without guard patterns shenanigans.
    // When destructuring, however, the scope of the reborrowed value extends up to
    // where it is used within the body, So we always finish our business with
    // the reborrowed values first before accessing the original ones.
    match (&mut *start, &mut *end) {
        (AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture) => {},
        (AbsStartBound::InfinitePast, AbsEndBound::Finite(finite_end)) => {
            *start = finite_end.pos().to_start_bound();
            *end = AbsEndBound::InfiniteFuture;
        },
        (AbsStartBound::Finite(finite_start), AbsEndBound::InfiniteFuture) => {
            *end = finite_start.pos().to_end_bound();
            *start = AbsStartBound::InfinitePast;
        },
        (AbsStartBound::Finite(finite_start), AbsEndBound::Finite(finite_end)) => {
            swap_abs_finite_start_end_bounds(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start
/// and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsStartEndBoundsCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same time but don't have only inclusive bound inclusivities
    SameTimeButNotDoublyInclusive,
}

impl Display for AbsStartEndBoundsCheckForIntervalCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StartPastEnd => write!(f, "Start bound is past the end bound"),
            Self::SameTimeButNotDoublyInclusive => write!(
                f,
                "Both bounds are on the same time but don't have only inclusive bound inclusivities"
            ),
        }
    }
}

impl Error for AbsStartEndBoundsCheckForIntervalCreationError {}

/// Checks whether the given finite start and finite end bounds are fit for creating an interval
///
/// # Errors
///
/// Returns [`StartPastEnd`](AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// if the start bound is positioned after the end bound.
///
/// Returns [`SameTimeButNotDoublyInclusive`](AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive)
/// if the bounds are positioned on the same time but are not doubly inclusive.
///
/// # Examples
///
/// ## Start past end
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     AbsStartEndBoundsCheckForIntervalCreationError,
/// #     check_abs_finite_start_end_bounds_for_interval_creation,
/// # };
/// let start = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
///     .to_finite_start_bound();
/// let end =
///     AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
///
/// assert_eq!(
///     check_abs_finite_start_end_bounds_for_interval_creation(&start, &end),
///     Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Same time but not doubly inclusive
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     AbsStartEndBoundsCheckForIntervalCreationError,
/// #     check_abs_finite_start_end_bounds_for_interval_creation,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
/// let start =
///     AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_finite_start_bound();
/// let end = AbsFiniteBoundPos::new(time).to_finite_end_bound();
///
/// assert_eq!(
///     check_abs_finite_start_end_bounds_for_interval_creation(&start, &end),
///     Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive)
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## OK
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     check_abs_finite_start_end_bounds_for_interval_creation,
/// # };
/// let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
///     .to_finite_start_bound();
/// let end =
///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
///
/// assert_eq!(
///     check_abs_finite_start_end_bounds_for_interval_creation(&start, &end),
///     Ok(())
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn check_abs_finite_start_end_bounds_for_interval_creation(
    start: &AbsFiniteStartBound,
    end: &AbsFiniteEndBound,
) -> Result<(), AbsStartEndBoundsCheckForIntervalCreationError> {
    match start.bound_cmp(end) {
        BoundOrdering::Less => Ok(()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(start_incl, end_incl))) => {
            if start_incl == BoundInclusivity::Inclusive && end_incl == BoundInclusivity::Inclusive {
                Ok(())
            } else {
                Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive)
            }
        },
        BoundOrdering::Equal(_) => unreachable!(),
        BoundOrdering::Greater => Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
    }
}

/// Checks whether the given start and end bounds are fit for creating an interval
///
/// # Errors
///
/// Returns [`StartPastEnd`](AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// if the start bound is positioned after the end bound.
///
/// Returns [`SameTimeButNotDoublyInclusive`](AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive)
/// if the bounds are positioned on the same time but are not doubly inclusive.
///
/// # Examples
///
/// ## Start past end
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     AbsStartEndBoundsCheckForIntervalCreationError,
/// #     check_abs_start_end_bounds_for_interval_creation,
/// # };
/// let start =
///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_start_bound();
/// let end = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound();
///
/// assert_eq!(
///     check_abs_start_end_bounds_for_interval_creation(&start, &end),
///     Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd)
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Same time but not doubly inclusive
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     AbsStartEndBoundsCheckForIntervalCreationError,
/// #     check_abs_start_end_bounds_for_interval_creation,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// let time = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
/// let start =
///     AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_start_bound();
/// let end = AbsFiniteBoundPos::new(time).to_end_bound();
///
/// assert_eq!(
///     check_abs_start_end_bounds_for_interval_creation(&start, &end),
///     Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive)
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## OK
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     check_abs_start_end_bounds_for_interval_creation,
/// # };
/// let start =
///     AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
/// let end = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_end_bound();
///
/// assert_eq!(
///     check_abs_start_end_bounds_for_interval_creation(&start, &end),
///     Ok(())
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn check_abs_start_end_bounds_for_interval_creation(
    start: &AbsStartBound,
    end: &AbsEndBound,
) -> Result<(), AbsStartEndBoundsCheckForIntervalCreationError> {
    match (start, end) {
        (AbsStartBound::InfinitePast, _) | (_, AbsEndBound::InfiniteFuture) => Ok(()),
        (AbsStartBound::Finite(finite_start), AbsEndBound::Finite(finite_end)) => {
            check_abs_finite_start_end_bounds_for_interval_creation(finite_start, finite_end)
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
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     AbsStartEndBoundsCheckForIntervalCreationError,
/// #     prepare_abs_finite_start_end_bounds_for_interval_creation,
/// # };
/// let mut start = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
///     .to_finite_start_bound();
/// let mut end =
///     AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
///
/// prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);
///
/// assert_eq!(
///     start.pos().time(),
///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?
/// );
/// assert_eq!(
///     end.pos().time(),
///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn prepare_abs_finite_start_end_bounds_for_interval_creation(
    start: &mut AbsFiniteStartBound,
    end: &mut AbsFiniteEndBound,
) -> bool {
    match check_abs_finite_start_end_bounds_for_interval_creation(start, end) {
        Ok(()) => false,
        Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_abs_finite_start_end_bounds(start, end);
            true
        },
        Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive) => {
            let AbsFiniteStartBound(finite_start) = start;
            let AbsFiniteEndBound(finite_end) = end;

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
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsFiniteBoundPos,
/// #     AbsStartEndBoundsCheckForIntervalCreationError,
/// #     prepare_abs_bound_pair_for_interval_creation,
/// # };
/// let mut start =
///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_start_bound();
/// let mut end =
///     AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound();
///
/// prepare_abs_bound_pair_for_interval_creation(&mut start, &mut end);
///
/// assert_eq!(
///     start,
///     AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound()
/// );
/// assert_eq!(
///     end,
///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_end_bound()
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn prepare_abs_start_end_bounds_for_interval_creation(start: &mut AbsStartBound, end: &mut AbsEndBound) -> bool {
    match check_abs_start_end_bounds_for_interval_creation(start, end) {
        Ok(()) => false,
        Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_abs_start_end_bounds(start, end);
            true
        },
        Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive) => {
            if let AbsStartBound::Finite(AbsFiniteStartBound(finite_start_mut)) = start {
                finite_start_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            if let AbsEndBound::Finite(AbsFiniteEndBound(finite_end_mut)) = end {
                finite_end_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            true
        },
    }
}

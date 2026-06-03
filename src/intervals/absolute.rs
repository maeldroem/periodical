//! Absolute intervals
//!
//! Absolute intervals are pinned to time, that is to say they have a start
//! datetime and an end datetime.
//!
//! The most common absolute interval objects you will encounter are
//!
//! - [`AbsBoundPair`]
//! - [`EmptiableAbsBoundPair`]
//! - [`BoundedAbsInterval`]
//! - [`HalfBoundedAbsInterval`]

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
mod half_bounded_interval_tests;
#[cfg(test)]
mod interval_tests;
#[cfg(test)]
mod start_bound_tests;

#[doc(inline)]
pub use bound::*;
#[doc(inline)]
pub use bound_pair::*;
#[doc(inline)]
pub use bounded_interval::*;
#[doc(inline)]
pub use emptiable_bound_pair::*;
#[doc(inline)]
pub use emptiable_interval::*;
#[doc(inline)]
pub use end_bound::*;
#[doc(inline)]
pub use finite_bound::*;
#[doc(inline)]
pub use finite_bound_position::*;
#[doc(inline)]
pub use finite_end_bound::*;
#[doc(inline)]
pub use finite_start_bound::*;
#[doc(inline)]
pub use half_bounded_interval::*;
#[doc(inline)]
pub use half_bounded_to_future_interval::*;
#[doc(inline)]
pub use half_bounded_to_past_interval::*;
#[doc(inline)]
pub use interval::*;
#[doc(inline)]
pub use start_bound::*;

pub fn swap_absolute_finite_start_end_bounds(
    finite_start: &mut AbsFiniteStartBound,
    finite_end: &mut AbsFiniteEndBound,
) {
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
/// # use periodical::intervals::absolute::{AbsFiniteBoundPos, swap_absolute_bound_pair};
/// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
/// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
///
/// let mut start = AbsFiniteBoundPos::new(start_time).to_start_bound();
/// let mut end = AbsFiniteBoundPos::new(end_time).to_end_bound();
///
/// swap_absolute_bound_pair(&mut start, &mut end);
///
/// assert_eq!(start, AbsFiniteBoundPos::new(end_time).to_start_bound());
/// assert_eq!(end, AbsFiniteBoundPos::new(start_time).to_end_bound());
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn swap_absolute_start_end_bounds(start: &mut AbsStartBound, end: &mut AbsEndBound) {
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
            swap_absolute_finite_start_end_bounds(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start
/// and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsStartEndBoundsCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same time but don't have only inclusive bound
    /// inclusivities
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

pub fn check_absolute_finite_start_end_bounds_for_interval_creation(
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

/// Checks if the given start and end bound are ready for creating an interval
///
/// This method is used as part of
/// [`prepare_absolute_bound_pair_for_interval_creation`], which is used by
/// [`AbsBoundPair::new`], but also in other places where we want to make
/// sure that a start and end bound are ready to be used as part of the interval
/// without using methods like [`AbsBoundPair::new`] that already go
/// through this process.
///
/// # Errors
///
/// If the start bound is past the end bound,
/// it returns
/// [`StartPastEnd`](AbsBoundPairCheckForIntervalCreationError::StartPastEnd).
///
///
/// If both bounds have the same time, but at least one of them has an exclusive
/// bound inclusivity, it returns
/// [`SameTimeButNotDoublyInclusive`](AbsBoundPairCheckForIntervalCreationError::SameTimeButNotDoublyInclusive).
///
/// # Examples
///
/// ```
/// # use periodical::intervals::absolute::{
/// #     AbsBoundPairCheckForIntervalCreationError, AbsEndBound, AbsStartBound,
/// #     check_absolute_bound_pair_for_interval_creation,
/// # };
/// fn validate_bounds_from_user(start: &AbsStartBound, end: &AbsEndBound) -> Result<(), String> {
///     type IntervalCreaErr = AbsBoundPairCheckForIntervalCreationError;
///     match check_absolute_bound_pair_for_interval_creation(start, end) {
///         Ok(()) => Ok(()),
///         Err(IntervalCreaErr::StartPastEnd) => {
///             Err("Start and end must be in chronological order!".to_string())
///         },
///         Err(IntervalCreaErr::SameTimeButNotDoublyInclusive) => Err("To represent a single \
///                                                                     point in time, both \
///                                                                     inclusivities must be \
///                                                                     inclusive!"
///             .to_string()),
///     }
/// }
/// ```
pub fn check_absolute_start_end_bounds_for_interval_creation(
    start: &AbsStartBound,
    end: &AbsEndBound,
) -> Result<(), AbsStartEndBoundsCheckForIntervalCreationError> {
    match (start, end) {
        (AbsStartBound::InfinitePast, _) | (_, AbsEndBound::InfiniteFuture) => Ok(()),
        (AbsStartBound::Finite(finite_start), AbsEndBound::Finite(finite_end)) => {
            check_absolute_finite_start_end_bounds_for_interval_creation(finite_start, finite_end)
        },
    }
}

pub fn prepare_absolute_finite_start_end_bounds_for_interval_creation(
    start: &mut AbsFiniteStartBound,
    end: &mut AbsFiniteEndBound,
) -> bool {
    match check_absolute_finite_start_end_bounds_for_interval_creation(start, end) {
        Ok(()) => false,
        Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_absolute_finite_start_end_bounds(start, end);
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

/// Prepares a start and end bound for being used as part of an interval
///
/// If some problems are present, see
/// [`check_absolute_bound_pair_for_interval_creation`], it resolves them
/// automatically by modifying the passed mutable references for the start and
/// end bound.
///
/// The returned boolean indicates whether a change was operated in order to fix
/// the given bounds.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{AbsFiniteBoundPos, prepare_absolute_bound_pair_for_interval_creation};
/// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
/// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
///
/// // Warning: not in chronological order!
/// let mut start = AbsFiniteBoundPos::new(start_time).to_start_bound();
/// let mut end = AbsFiniteBoundPos::new(end_time).to_end_bound();
///
/// let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);
///
/// if was_changed {
///     // Prompt the user for confirmation regarding the fixed bounds
/// }
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn prepare_absolute_bound_pair_for_interval_creation(start: &mut AbsStartBound, end: &mut AbsEndBound) -> bool {
    match check_absolute_start_end_bounds_for_interval_creation(start, end) {
        Ok(()) => false,
        Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_absolute_start_end_bounds(start, end);
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

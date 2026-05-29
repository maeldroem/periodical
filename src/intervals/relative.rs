//! Relative intervals
//!
//! Relative intervals contain an offset duration and a length instead of being
//! fixed in time.
//!
//! The most common relative interval objects you will encounter are
//!
//! - [`RelativeBoundPair`]
//! - [`EmptiableRelativeBoundPair`]
//! - [`BoundedRelativeInterval`]
//! - [`HalfBoundedRelativeInterval`]

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

pub mod bound;
pub mod bound_pair;
pub mod bounded_interval;
pub mod emptiable_bound_pair;
pub mod emptiable_interval;
pub mod end_bound;
pub mod finite_bound_position;
pub mod half_bounded_interval;
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
mod finite_bound_tests;
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
pub use finite_bound_position::*;
#[doc(inline)]
pub use half_bounded_interval::*;
#[doc(inline)]
pub use interval::*;
#[doc(inline)]
pub use start_bound::*;

/// Swaps a relative start bound with a relative end bound
///
/// This method is primarily used in the case where a start bound and an end
/// bound are not in chronological order.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, swap_relative_bound_pair};
/// let start_offset = SignedDuration::from_hours(16);
/// let end_offset = SignedDuration::from_hours(8);
///
/// let mut start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
/// let mut end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
///
/// swap_relative_bound_pair(&mut start, &mut end);
///
/// assert_eq!(start, RelativeFiniteBoundPosition::new(end_offset).to_start_bound());
/// assert_eq!(end, RelativeFiniteBoundPosition::new(start_offset).to_end_bound());
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn swap_relative_bound_pair(start: &mut RelativeStartBound, end: &mut RelativeEndBound) {
    // We temporarily reborrow start and end for the match arms so that when a
    // pattern matches, they move out of their temporary scope and we can use
    // the original mutable references without guard patterns shenanigans.
    // When destructuring, however, the scope of the reborrowed value extends up to
    // where it is used within the body, So we always finish our business with
    // the reborrowed values first before accessing the original ones.
    match (&mut *start, &mut *end) {
        (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => {},
        (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(finite_end)) => {
            *start = finite_end.to_start_bound();
            *end = RelativeEndBound::InfiniteFuture;
        },
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::InfiniteFuture) => {
            *end = finite_start.to_end_bound();
            *start = RelativeStartBound::InfinitePast;
        },
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
            std::mem::swap(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start
/// and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeBoundPairCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same offset but don't have only inclusive bound
    /// inclusivities
    SameOffsetButNotDoublyInclusive,
}

impl Display for RelativeBoundPairCheckForIntervalCreationError {
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

impl Error for RelativeBoundPairCheckForIntervalCreationError {}

/// Checks if the given start and end bound are ready for creating an interval
///
/// This method is used as part of
/// [`prepare_relative_bound_pair_for_interval_creation`], which is used by
/// [`RelativeBoundPair::new`], but also in other places where we want to make
/// sure that a start and end bound are ready to be used as part of the interval
/// without using methods like [`RelativeBoundPair::new`] that already go
/// through this process.
///
/// # Errors
///
/// If the start bound is past the end bound,
/// it returns
/// [`StartPastEnd`](RelativeBoundPairCheckForIntervalCreationError::StartPastEnd).
///
///
/// If both bounds have the same offset, but at least one of them has an
/// exclusive bound inclusivity, it returns
/// [`SameOffsetButNotDoublyInclusive`](RelativeBoundPairCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive).
///
/// # Examples
///
/// ```
/// # use periodical::intervals::relative::{
/// #     RelativeBoundPairCheckForIntervalCreationError, RelativeEndBound, RelativeStartBound,
/// #     check_relative_bound_pair_for_interval_creation,
/// # };
/// fn validate_bounds_from_user(
///     start: &RelativeStartBound,
///     end: &RelativeEndBound,
/// ) -> Result<(), String> {
///     type IntervalCreaErr = RelativeBoundPairCheckForIntervalCreationError;
///     match check_relative_bound_pair_for_interval_creation(start, end) {
///         Ok(()) => Ok(()),
///         Err(IntervalCreaErr::StartPastEnd) => Err(
///             "Start and end must be in chronological order!".to_string()
///         ),
///         Err(IntervalCreaErr::SameOffsetButNotDoublyInclusive) => Err(
///             "To represent a single point in relative time, both inclusivities must be inclusive!".to_string()
///         ),
///     }
/// }
/// ```
pub fn check_relative_bound_pair_for_interval_creation(
    start: &RelativeStartBound,
    end: &RelativeEndBound,
) -> Result<(), RelativeBoundPairCheckForIntervalCreationError> {
    match (start, end) {
        (RelativeStartBound::InfinitePast, _) | (_, RelativeEndBound::InfiniteFuture) => Ok(()),
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
            match finite_start.offset().cmp(&finite_end.offset()) {
                Ordering::Less => Ok(()),
                Ordering::Equal => {
                    if finite_start.inclusivity() == BoundInclusivity::Inclusive
                        && finite_end.inclusivity() == BoundInclusivity::Inclusive
                    {
                        Ok(())
                    } else {
                        Err(RelativeBoundPairCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
                    }
                },
                Ordering::Greater => Err(RelativeBoundPairCheckForIntervalCreationError::StartPastEnd),
            }
        },
    }
}

/// Prepares a start and end bound for being used as part of an interval
///
/// If some problems are present, see
/// [`check_relative_bound_pair_for_interval_creation`], it resolves them
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
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::{RelativeFiniteBoundPosition, prepare_relative_bound_pair_for_interval_creation};
/// let start_offset = SignedDuration::from_hours(16);
/// let end_offset = SignedDuration::from_hours(8);
///
/// // Warning: not in chronological order!
/// let mut start = RelativeFiniteBoundPosition::new(start_offset).to_start_bound();
/// let mut end = RelativeFiniteBoundPosition::new(end_offset).to_end_bound();
///
/// let was_changed = prepare_relative_bound_pair_for_interval_creation(&mut start, &mut end);
///
/// if was_changed {
///     // Prompt the user for confirmation regarding the fixed bounds
/// }
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn prepare_relative_bound_pair_for_interval_creation(
    start_mut: &mut RelativeStartBound,
    end_mut: &mut RelativeEndBound,
) -> bool {
    match check_relative_bound_pair_for_interval_creation(start_mut, end_mut) {
        Ok(()) => false,
        Err(RelativeBoundPairCheckForIntervalCreationError::StartPastEnd) => {
            swap_relative_bound_pair(start_mut, end_mut);
            true
        },
        Err(RelativeBoundPairCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive) => {
            if let RelativeStartBound::Finite(finite_start_mut) = start_mut {
                finite_start_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            if let RelativeEndBound::Finite(finite_end_mut) = end_mut {
                finite_end_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            true
        },
    }
}

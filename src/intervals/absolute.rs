//! Absolute intervals
//!
//! Absolute intervals are pinned to time, that is to say they have a start datetime and an end datetime.
//!
//! The most common absolute interval objects you will encounter are
//!
//! - [`AbsoluteBoundPair`]
//! - [`EmptiableAbsoluteBoundPair`]
//! - [`BoundedAbsoluteInterval`]
//! - [`HalfBoundedAbsoluteInterval`]

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;

use crate::intervals::meta::BoundInclusivity;
use crate::utils::{inline_docs, tests};

pub mod bound;
pub mod bounded_interval;
pub mod bound_pair;
pub mod end_bound;
pub mod emptiable_bound_pair;
pub mod finite_bound;
pub mod half_bounded_interval;
pub mod interval;
pub mod start_bound;

tests! {
    mod bound_pair_tests;
    mod bound_tests;
    mod bounded_interval_tests;
    mod emptiable_bound_pair_tests;
    mod end_bound_tests;
    mod finite_bound_tests;
    mod half_bounded_interval_tests;
    mod interval_tests;
    mod start_bound_tests;
}

inline_docs! {
    pub use bound::AbsoluteBound;
    pub use bounded_interval::BoundedAbsoluteInterval;
    pub use bound_pair::{HasAbsoluteBounds, AbsoluteBounds};
    pub use end_bound::AbsoluteEndBound;
    pub use emptiable_bound_pair::{HasEmptiableAbsoluteBounds, EmptiableAbsoluteBounds};
    pub use finite_bound::AbsoluteFiniteBound;
    pub use half_bounded_interval::HalfBoundedAbsoluteInterval;
    pub use interval::AbsoluteInterval;
    pub use start_bound::AbsoluteStartBound;
}

/// Swaps an absolute start bound with an absolute end bound
///
/// This method is primarily used in the case where a start bound and an end bound are not in chronological order.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{AbsoluteFiniteBound, swap_absolute_bound_pair};
/// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
/// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
///
/// let mut start = AbsoluteFiniteBound::new(start_time).to_start_bound();
/// let mut end = AbsoluteFiniteBound::new(end_time).to_end_bound();
///
/// swap_absolute_bound_pair(&mut start, &mut end);
///
/// assert_eq!(start, AbsoluteFiniteBound::new(end_time).to_start_bound());
/// assert_eq!(end, AbsoluteFiniteBound::new(start_time).to_end_bound());
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn swap_absolute_bound_pair(start: &mut AbsoluteStartBound, end: &mut AbsoluteEndBound) {
    // We temporarily reborrow start and end for the match arms so that when a pattern matches, they move out of their
    // temporary scope and we can use the original mutable references without guard patterns shenanigans.
    // When destructuring, however, the scope of the reborrowed value extends up to where it is used within the body,
    // So we always finish our business with the reborrowed values first before accessing the original ones.
    match (&mut *start, &mut *end) {
        (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture) => {},
        (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(finite_end)) => {
            *start = AbsoluteStartBound::Finite(*finite_end);
            *end = AbsoluteEndBound::InfiniteFuture;
        },
        (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::InfiniteFuture) => {
            *end = AbsoluteEndBound::Finite(*finite_start);
            *start = AbsoluteStartBound::InfinitePast;
        },
        (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
            std::mem::swap(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsoluteBoundPairCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same time but don't have only inclusive bound inclusivities
    SameTimeButNotDoublyInclusive,
}

impl Display for AbsoluteBoundPairCheckForIntervalCreationError {
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

impl Error for AbsoluteBoundPairCheckForIntervalCreationError {}

/// Checks if the given start and end bound are ready for creating an interval
///
/// This method is used as part of [`prepare_absolute_bound_pair_for_interval_creation`], which is used by
/// [`AbsoluteBoundPair::new`], but also in other places where we want to make sure that a start and end bound
/// are ready to be used as part of the interval without using methods like [`AbsoluteBoundPair::new`] that
/// already go through this process.
///
/// # Errors
///
/// If the start bound is past the end bound,
/// it returns [`StartPastEnd`](AbsoluteBoundPairCheckForIntervalCreationError::StartPastEnd).
///
/// If both bounds have the same time, but at least one of them has an exclusive bound inclusivity, it returns
/// [`SameTimeButNotDoublyInclusive`](AbsoluteBoundPairCheckForIntervalCreationError::SameTimeButNotDoublyInclusive).
///
/// # Examples
///
/// ```
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBoundPairCheckForIntervalCreationError, AbsoluteEndBound, AbsoluteStartBound,
/// #     check_absolute_bound_pair_for_interval_creation,
/// # };
/// fn validate_bounds_from_user(
///     start: &AbsoluteStartBound,
///     end: &AbsoluteEndBound,
/// ) -> Result<(), String> {
///     type IntervalCreaErr = AbsoluteBoundPairCheckForIntervalCreationError;
///     match check_absolute_bound_pair_for_interval_creation(start, end) {
///         Ok(()) => Ok(()),
///         Err(IntervalCreaErr::StartPastEnd) => Err(
///             "Start and end must be in chronological order!".to_string()
///         ),
///         Err(IntervalCreaErr::SameTimeButNotDoublyInclusive) => Err(
///             "To represent a single point in time, both inclusivities must be inclusive!".to_string()
///         ),
///     }
/// }
/// ```
pub fn check_absolute_bound_pair_for_interval_creation(
    start: &AbsoluteStartBound,
    end: &AbsoluteEndBound,
) -> Result<(), AbsoluteBoundPairCheckForIntervalCreationError> {
    match (start, end) {
        (AbsoluteStartBound::InfinitePast, _) | (_, AbsoluteEndBound::InfiniteFuture) => Ok(()),
        (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
            match finite_start.time().cmp(&finite_end.time()) {
                Ordering::Less => Ok(()),
                Ordering::Equal => {
                    if finite_start.inclusivity() == BoundInclusivity::Inclusive
                        && finite_end.inclusivity() == BoundInclusivity::Inclusive
                    {
                        Ok(())
                    } else {
                        Err(AbsoluteBoundPairCheckForIntervalCreationError::SameTimeButNotDoublyInclusive)
                    }
                },
                Ordering::Greater => Err(AbsoluteBoundPairCheckForIntervalCreationError::StartPastEnd),
            }
        },
    }
}

/// Prepares a start and end bound for being used as part of an interval
///
/// If some problems are present, see [`check_absolute_bound_pair_for_interval_creation`], it resolves them automatically
/// by modifying the passed mutable references for the start and end bound.
///
/// The returned boolean indicates whether a change was operated in order to fix the given bounds.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{AbsoluteFiniteBound, prepare_absolute_bound_pair_for_interval_creation};
/// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
/// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
///
/// // Warning: not in chronological order!
/// let mut start = AbsoluteFiniteBound::new(start_time).to_start_bound();
/// let mut end = AbsoluteFiniteBound::new(end_time).to_end_bound();
///
/// let was_changed = prepare_absolute_bound_pair_for_interval_creation(&mut start, &mut end);
///
/// if was_changed {
///     // Prompt the user for confirmation regarding the fixed bounds
/// }
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub fn prepare_absolute_bound_pair_for_interval_creation(
    start_mut: &mut AbsoluteStartBound,
    end_mut: &mut AbsoluteEndBound,
) -> bool {
    match check_absolute_bound_pair_for_interval_creation(start_mut, end_mut) {
        Ok(()) => false,
        Err(AbsoluteBoundPairCheckForIntervalCreationError::StartPastEnd) => {
            swap_absolute_bound_pair(start_mut, end_mut);
            true
        },
        Err(AbsoluteBoundPairCheckForIntervalCreationError::SameTimeButNotDoublyInclusive) => {
            if let AbsoluteStartBound::Finite(finite_start_mut) = start_mut {
                finite_start_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            if let AbsoluteEndBound::Finite(finite_end_mut) = end_mut {
                finite_end_mut.set_inclusivity(BoundInclusivity::Inclusive);
            }

            true
        },
    }
}

//! Relative intervals
//!
//! Relative intervals contain an offset duration and a length instead of being fixed in time.
//!
//! The most common relative interval objects you will encounter are
//!
//! - [`RelativeBounds`]
//! - [`EmptiableRelativeBounds`]
//! - [`BoundedRelativeInterval`]
//! - [`HalfBoundedRelativeInterval`]

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
    pub use bound::RelativeBound;
    pub use bounded_interval::BoundedRelativeInterval;
    pub use bound_pair::{HasRelativeBounds, RelativeBounds};
    pub use end_bound::RelativeEndBound;
    pub use emptiable_bound_pair::{HasEmptiableRelativeBounds, EmptiableRelativeBounds};
    pub use finite_bound::RelativeFiniteBound;
    pub use half_bounded_interval::HalfBoundedRelativeInterval;
    pub use interval::RelativeInterval;
    pub use start_bound::RelativeStartBound;
}

/// Swaps a relative start bound with a relative end bound
///
/// This method is primarily used in the case where a start bound and an end bound are not in chronological order.
///
/// # Examples
///
/// ```
/// # use chrono::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelativeEndBound, RelativeFiniteBound, RelativeStartBound, swap_relative_bounds,
/// # };
/// let start_offset = SignedDuration::hours(16);
/// let end_offset = SignedDuration::hours(8);
///
/// let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
/// let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
///
/// swap_relative_bounds(&mut start, &mut end);
///
/// assert_eq!(
///     start,
///     RelativeStartBound::Finite(RelativeFiniteBound::new(end_offset)),
/// );
/// assert_eq!(
///     end,
///     RelativeEndBound::Finite(RelativeFiniteBound::new(start_offset)),
/// );
/// ```
pub fn swap_relative_bounds(start: &mut RelativeStartBound, end: &mut RelativeEndBound) {
    // We temporarily reborrow start and end for the match arms so that when a pattern matches, they move out of their
    // temporary scope and we can use the original mutable references without guard patterns shenanigans.
    // When destructuring, however, the scope of the reborrowed value extends up to where it is used within the body,
    // So we always finish our business with the reborrowed values first before accessing the original ones.
    match (&mut *start, &mut *end) {
        (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => {},
        (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(finite_end)) => {
            *start = RelativeStartBound::Finite(*finite_end);
            *end = RelativeEndBound::InfiniteFuture;
        },
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::InfiniteFuture) => {
            *end = RelativeEndBound::Finite(*finite_start);
            *start = RelativeStartBound::InfinitePast;
        },
        (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
            std::mem::swap(finite_start, finite_end);
        },
    }
}

/// Possible problems that can prevent creating an interval from the given start and end bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeBoundsCheckForIntervalCreationError {
    /// Start bound is past the end bound
    StartPastEnd,
    /// Both bounds are on the same offset but don't have only inclusive bound inclusivities
    SameOffsetButNotDoublyInclusive,
}

impl Display for RelativeBoundsCheckForIntervalCreationError {
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

impl Error for RelativeBoundsCheckForIntervalCreationError {}

/// Checks if the given start and end bound are ready for creating an interval
///
/// This method is used as part of [`prepare_relative_bounds_for_interval_creation`], which is used by
/// [`RelativeBounds::new`], but also in other places where we want to make sure that a start and end bound
/// are ready to be used as part of the interval without using methods like [`RelativeBounds::new`] that
/// already go through this process.
///
/// # Errors
///
/// If the start bound is past the end bound,
/// it returns [`StartPastEnd`](RelativeBoundsCheckForIntervalCreationError::StartPastEnd).
///
/// If both bounds have the same offset, but at least one of them has an exclusive bound inclusivity, it returns
/// [`SameOffsetButNotDoublyInclusive`](RelativeBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive).
///
/// # Examples
///
/// ```
/// # use periodical::intervals::relative::{
/// #     RelativeBoundsCheckForIntervalCreationError, RelativeEndBound, RelativeStartBound,
/// #     check_relative_bounds_for_interval_creation,
/// # };
/// fn validate_bounds_from_user(
///     start: &RelativeStartBound,
///     end: &RelativeEndBound,
/// ) -> Result<(), String> {
///     type IntervalCreaErr = RelativeBoundsCheckForIntervalCreationError;
///     match check_relative_bounds_for_interval_creation(start, end) {
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
pub fn check_relative_bounds_for_interval_creation(
    start: &RelativeStartBound,
    end: &RelativeEndBound,
) -> Result<(), RelativeBoundsCheckForIntervalCreationError> {
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
                        Err(RelativeBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive)
                    }
                },
                Ordering::Greater => Err(RelativeBoundsCheckForIntervalCreationError::StartPastEnd),
            }
        },
    }
}

/// Prepares a start and end bound for being used as part of an interval
///
/// If some problems are present, see [`check_relative_bounds_for_interval_creation`], it resolves them automatically
/// by modifying the passed mutable references for the start and end bound.
///
/// The returned boolean indicates whether a change was operated in order to fix the given bounds.
///
/// # Examples
///
/// ```
/// # use chrono::SignedDuration;
/// # use periodical::intervals::relative::{
/// #     RelativeEndBound, RelativeFiniteBound, RelativeStartBound, prepare_relative_bounds_for_interval_creation,
/// # };
/// let start_offset = SignedDuration::hours(16);
/// let end_offset = SignedDuration::hours(8);
///
/// // Warning: not in chronological order!
/// let mut start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
/// let mut end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
///
/// let was_changed = prepare_relative_bounds_for_interval_creation(&mut start, &mut end);
///
/// if was_changed {
///     // Prompt the user for confirmation regarding the fixed bounds
/// }
/// ```
pub fn prepare_relative_bounds_for_interval_creation(
    start_mut: &mut RelativeStartBound,
    end_mut: &mut RelativeEndBound,
) -> bool {
    match check_relative_bounds_for_interval_creation(start_mut, end_mut) {
        Ok(()) => false,
        Err(RelativeBoundsCheckForIntervalCreationError::StartPastEnd) => {
            swap_relative_bounds(start_mut, end_mut);
            true
        },
        Err(RelativeBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive) => {
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

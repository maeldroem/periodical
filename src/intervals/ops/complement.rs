//! Complement of an interval
//!
//! Returns the [complementary] intervals of a given interval using
//! [`ComplementResult`] to store the result.
//!
//! [complementary]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427
//!
//! # Examples
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::ops::ComplementResult;
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound, EmptiableAbsoluteBoundPair
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::complement::Complementable;
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBoundPosition::new_with_inclusivity(
//!         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         BoundInclusivity::Exclusive,
//!     ).to_start_bound(),
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_end_bound(),
//! );
//!
//! assert_eq!(
//!     interval.complement(),
//!     ComplementResult::Split(
//!         EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
//!             AbsoluteStartBound::InfinitePast,
//!             AbsoluteFiniteBoundPosition::new(
//!                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_end_bound(),
//!         )),
//!         EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
//!             AbsoluteFiniteBoundPosition::new_with_inclusivity(
//!                 "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             ).to_start_bound(),
//!             AbsoluteEndBound::InfiniteFuture,
//!         )),
//!     ),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{HasOpeningDirection, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::ops::ComplementResult;

/// Capacity to get the complementary intervals
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::ops::ComplementResult;
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound, EmptiableAbsoluteBoundPair,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::complement::Complementable;
/// let interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new_with_inclusivity(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         BoundInclusivity::Exclusive,
///     ).to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.complement(),
///     ComplementResult::Split(
///         EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
///             AbsoluteStartBound::InfinitePast,
///             AbsoluteFiniteBoundPosition::new(
///                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///             ).to_end_bound(),
///         )),
///         EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
///             AbsoluteFiniteBoundPosition::new_with_inclusivity(
///                 "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///                 BoundInclusivity::Exclusive,
///             ).to_start_bound(),
///             AbsoluteEndBound::InfiniteFuture,
///         )),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Complementable {
    /// Output type
    type Output;

    /// Returns the complementary interval(s) of `self`
    #[must_use]
    fn complement(&self) -> ComplementResult<Self::Output>;
}

impl Complementable for AbsoluteBoundPair {
    type Output = EmptiableAbsoluteBoundPair;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_abs_bound_pair(self)
    }
}

impl Complementable for EmptiableAbsoluteBoundPair {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bound_pair(self)
    }
}

impl Complementable for AbsoluteInterval {
    type Output = EmptiableAbsoluteInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_abs_bound_pair(&self.abs_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for EmptiableAbsoluteInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for BoundedAbsoluteInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_bounded_abs_interval(self)
    }
}

impl Complementable for HalfBoundedAbsoluteInterval {
    type Output = HalfBoundedAbsoluteInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_half_bounded_abs_interval(self)
    }
}

impl Complementable for RelativeBoundPair {
    type Output = EmptiableRelativeBoundPair;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_rel_bound_pair(self)
    }
}

impl Complementable for EmptiableRelativeBoundPair {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bound_pair(self)
    }
}

impl Complementable for RelativeInterval {
    type Output = EmptiableRelativeInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_rel_bound_pair(&self.rel_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for EmptiableRelativeInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for BoundedRelativeInterval {
    type Output = HalfBoundedRelativeInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_bounded_rel_interval(self)
    }
}

impl Complementable for HalfBoundedRelativeInterval {
    type Output = HalfBoundedRelativeInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_half_bounded_rel_interval(self)
    }
}

impl Complementable for UnboundedInterval {
    type Output = EmptyInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        ComplementResult::Single(EmptyInterval)
    }
}

impl Complementable for EmptyInterval {
    type Output = UnboundedInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        ComplementResult::Single(UnboundedInterval)
    }
}

/// Returns the complementary intervals of an [`AbsoluteBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_abs_bound_pair(bounds: &AbsoluteBoundPair) -> ComplementResult<EmptiableAbsoluteBoundPair> {
    type Sb = AbsoluteStartBound;
    type Eb = AbsoluteEndBound;

    match (bounds.abs_start(), bounds.abs_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_abs_bound_pair()),
        (Sb::InfinitePast, Eb::Finite(finite_end)) => ComplementResult::Single(
            AbsoluteBoundPair::new(finite_end.opposite().to_start_bound(), AbsoluteEndBound::InfiniteFuture)
                .to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::InfiniteFuture) => ComplementResult::Single(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, finite_start.opposite().to_end_bound())
                .to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, finite_start.opposite().to_end_bound())
                .to_emptiable(),
            AbsoluteBoundPair::new(finite_end.opposite().to_start_bound(), AbsoluteEndBound::InfiniteFuture)
                .to_emptiable(),
        ),
    }
}

/// Returns the complementary intervals of an [`EmptiableAbsoluteBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsoluteBoundPair,
) -> ComplementResult<EmptiableAbsoluteBoundPair> {
    let EmptiableAbsoluteBoundPair::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(UnboundedInterval.emptiable_abs_bound_pair());
    };

    complement_abs_bound_pair(bounds)
}

#[must_use]
pub fn complement_bounded_abs_interval(
    interval: &BoundedAbsoluteInterval,
) -> ComplementResult<HalfBoundedAbsoluteInterval> {
    let until_start = HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
        interval.start_time(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    );

    let since_end = HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
        interval.end_time(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    );

    ComplementResult::Split(until_start, since_end)
}

#[must_use]
pub fn complement_half_bounded_abs_interval(
    interval: &HalfBoundedAbsoluteInterval,
) -> ComplementResult<HalfBoundedAbsoluteInterval> {
    ComplementResult::Single(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
        interval.reference_time(),
        interval.reference_inclusivity().opposite(),
        interval.opening_direction().opposite(),
    ))
}

/// Returns the complementary intervals of a [`RelativeBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_rel_bound_pair(bounds: &RelativeBoundPair) -> ComplementResult<EmptiableRelativeBoundPair> {
    type Sb = RelativeStartBound;
    type Eb = RelativeEndBound;

    match (bounds.rel_start(), bounds.rel_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_rel_bound_pair()),
        (Sb::InfinitePast, Eb::Finite(finite_end)) => ComplementResult::Single(
            RelativeBoundPair::new(finite_end.opposite().to_start_bound(), RelativeEndBound::InfiniteFuture)
                .to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::InfiniteFuture) => ComplementResult::Single(
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, finite_start.opposite().to_end_bound())
                .to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, finite_start.opposite().to_end_bound())
                .to_emptiable(),
            RelativeBoundPair::new(finite_end.opposite().to_start_bound(), RelativeEndBound::InfiniteFuture)
                .to_emptiable(),
        ),
    }
}

/// Returns the complementary intervals of an [`EmptiableRelativeBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelativeBoundPair,
) -> ComplementResult<EmptiableRelativeBoundPair> {
    let EmptiableRelativeBoundPair::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(UnboundedInterval.emptiable_rel_bound_pair());
    };

    complement_rel_bound_pair(bounds)
}

#[must_use]
pub fn complement_bounded_rel_interval(
    interval: &BoundedRelativeInterval,
) -> ComplementResult<HalfBoundedRelativeInterval> {
    let until_start = HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
        interval.start_offset(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    );

    let since_end = HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
        interval.end_offset(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    );

    ComplementResult::Split(until_start, since_end)
}

#[must_use]
pub fn complement_half_bounded_rel_interval(
    interval: &HalfBoundedRelativeInterval,
) -> ComplementResult<HalfBoundedRelativeInterval> {
    ComplementResult::Single(HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
        interval.reference_offset(),
        interval.reference_inclusivity().opposite(),
        interval.opening_direction().opposite(),
    ))
}

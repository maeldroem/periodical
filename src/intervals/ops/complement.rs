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
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
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
        (Sb::InfinitePast, Eb::Finite(finite)) => {
            ComplementResult::Single(EmptiableAbsoluteBoundPair::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    finite.time(),
                    finite.inclusivity().opposite(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            )))
        },
        (Sb::Finite(finite), Eb::InfiniteFuture) => {
            ComplementResult::Single(EmptiableAbsoluteBoundPair::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    finite.time(),
                    finite.inclusivity().opposite(),
                )),
            )))
        },
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            EmptiableAbsoluteBoundPair::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity().opposite(),
                )),
            )),
            EmptiableAbsoluteBoundPair::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    finite_end.time(),
                    finite_end.inclusivity().opposite(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            )),
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
    let until_start = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        interval.start(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    );

    let since_end = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        interval.end(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    );

    ComplementResult::Split(until_start, since_end)
}

#[must_use]
pub fn complement_half_bounded_abs_interval(
    interval: &HalfBoundedAbsoluteInterval,
) -> ComplementResult<HalfBoundedAbsoluteInterval> {
    ComplementResult::Single(HalfBoundedAbsoluteInterval::new_with_inclusivity(
        interval.reference(),
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
        (Sb::InfinitePast, Eb::Finite(finite)) => {
            ComplementResult::Single(EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
                RelativeStartBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                    finite.offset(),
                    finite.inclusivity().opposite(),
                )),
                RelativeEndBound::InfiniteFuture,
            )))
        },
        (Sb::Finite(finite), Eb::InfiniteFuture) => {
            ComplementResult::Single(EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                    finite.offset(),
                    finite.inclusivity().opposite(),
                )),
            )))
        },
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity().opposite(),
                )),
            )),
            EmptiableRelativeBoundPair::from(RelativeBoundPair::new(
                RelativeStartBound::from(RelativeFiniteBoundPosition::new_with_inclusivity(
                    finite_end.offset(),
                    finite_end.inclusivity().opposite(),
                )),
                RelativeEndBound::InfiniteFuture,
            )),
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
    let until_start = HalfBoundedRelativeInterval::new_with_inclusivity(
        interval.start(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    );

    let since_end = HalfBoundedRelativeInterval::new_with_inclusivity(
        interval.end(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    );

    ComplementResult::Split(until_start, since_end)
}

#[must_use]
pub fn complement_half_bounded_rel_interval(
    interval: &HalfBoundedRelativeInterval,
) -> ComplementResult<HalfBoundedRelativeInterval> {
    ComplementResult::Single(HalfBoundedRelativeInterval::new_with_inclusivity(
        interval.reference(),
        interval.reference_inclusivity().opposite(),
        interval.opening_direction().opposite(),
    ))
}

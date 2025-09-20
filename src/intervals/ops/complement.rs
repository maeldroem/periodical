//! Complement of an interval
//!
//! Returns the [complementary] intervals of a given interval using [`ComplementResult`] to store the result.
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::ops::ComplementResult;
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::complement::Complementable;
//! let interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         BoundInclusivity::Exclusive,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! assert_eq!(
//!     interval.complement(),
//!     ComplementResult::Split(
//!         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!             AbsoluteStartBound::InfinitePast,
//!             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!             )),
//!         )),
//!         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
//!             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
//!                 BoundInclusivity::Exclusive,
//!             )),
//!             AbsoluteEndBound::InfiniteFuture,
//!         )),
//!     ),
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```
//!
//! [complementary]: https://en.wikipedia.org/w/index.php?title=Complement_(set_theory)&oldid=1272128427

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfBoundedAbsoluteInterval, HasEmptiableAbsoluteBounds,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfBoundedRelativeInterval, RelativeBounds, RelativeEndBound, RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{AbsoluteInterval, BoundedAbsoluteInterval, BoundedRelativeInterval, RelativeInterval};
use crate::ops::ComplementResult;

/// Capacity to get the complementary intervals
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::ops::ComplementResult;
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::complement::Complementable;
/// let interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///         BoundInclusivity::Exclusive,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// assert_eq!(
///     interval.complement(),
///     ComplementResult::Split(
///         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
///             AbsoluteStartBound::InfinitePast,
///             AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///                 "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///             )),
///         )),
///         EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
///             AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///                 BoundInclusivity::Exclusive,
///             )),
///             AbsoluteEndBound::InfiniteFuture,
///         )),
///     ),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait Complementable {
    /// Output type
    type Output;

    /// Returns the complementary intervals of `self`
    #[must_use]
    fn complement(&self) -> ComplementResult<Self::Output>;
}

impl Complementable for AbsoluteBounds {
    type Output = EmptiableAbsoluteBounds;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_abs_bounds(self)
    }
}

impl Complementable for EmptiableAbsoluteBounds {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(self)
    }
}

impl Complementable for AbsoluteInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(&self.emptiable_abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl Complementable for BoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(&self.emptiable_abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl Complementable for HalfBoundedAbsoluteInterval {
    type Output = AbsoluteInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bounds(&self.emptiable_abs_bounds()).map(AbsoluteInterval::from)
    }
}

impl Complementable for RelativeBounds {
    type Output = EmptiableRelativeBounds;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_rel_bounds(self)
    }
}

impl Complementable for EmptiableRelativeBounds {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(self)
    }
}

impl Complementable for RelativeInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(&self.emptiable_rel_bounds()).map(RelativeInterval::from)
    }
}

impl Complementable for BoundedRelativeInterval {
    type Output = RelativeInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(&self.emptiable_rel_bounds()).map(RelativeInterval::from)
    }
}

impl Complementable for HalfBoundedRelativeInterval {
    type Output = RelativeInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bounds(&self.emptiable_rel_bounds()).map(RelativeInterval::from)
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

/// Returns the complementary intervals of an [`AbsoluteBounds`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_abs_bounds(bounds: &AbsoluteBounds) -> ComplementResult<EmptiableAbsoluteBounds> {
    type Sb = AbsoluteStartBound;
    type Eb = AbsoluteEndBound;

    match (bounds.abs_start(), bounds.abs_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_abs_bounds()),
        (Sb::InfinitePast, Eb::Finite(finite)) => {
            ComplementResult::Single(EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite.time(),
                    finite.inclusivity().opposite(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            )))
        },
        (Sb::Finite(finite), Eb::InfiniteFuture) => {
            ComplementResult::Single(EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite.time(),
                    finite.inclusivity().opposite(),
                )),
            )))
        },
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite_start.time(),
                    finite_start.inclusivity().opposite(),
                )),
            )),
            EmptiableAbsoluteBounds::from(AbsoluteBounds::new(
                AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
                    finite_end.time(),
                    finite_end.inclusivity().opposite(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            )),
        ),
    }
}

/// Returns the complementary intervals of an [`EmptiableAbsoluteBounds`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_emptiable_abs_bounds(
    emptiable_bounds: &EmptiableAbsoluteBounds,
) -> ComplementResult<EmptiableAbsoluteBounds> {
    let EmptiableAbsoluteBounds::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(UnboundedInterval.emptiable_abs_bounds());
    };

    complement_abs_bounds(bounds)
}

/// Returns the complementary intervals of a [`RelativeBounds`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_rel_bounds(bounds: &RelativeBounds) -> ComplementResult<EmptiableRelativeBounds> {
    type Sb = RelativeStartBound;
    type Eb = RelativeEndBound;

    match (bounds.rel_start(), bounds.rel_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_rel_bounds()),
        (Sb::InfinitePast, Eb::Finite(finite)) => {
            ComplementResult::Single(EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite.offset(),
                    finite.inclusivity().opposite(),
                )),
                RelativeEndBound::InfiniteFuture,
            )))
        },
        (Sb::Finite(finite), Eb::InfiniteFuture) => {
            ComplementResult::Single(EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite.offset(),
                    finite.inclusivity().opposite(),
                )),
            )))
        },
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity().opposite(),
                )),
            )),
            EmptiableRelativeBounds::from(RelativeBounds::new(
                RelativeStartBound::from(RelativeFiniteBound::new_with_inclusivity(
                    finite_end.offset(),
                    finite_end.inclusivity().opposite(),
                )),
                RelativeEndBound::InfiniteFuture,
            )),
        ),
    }
}

/// Returns the complementary intervals of an [`EmptiableRelativeBounds`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_emptiable_rel_bounds(
    emptiable_bounds: &EmptiableRelativeBounds,
) -> ComplementResult<EmptiableRelativeBounds> {
    let EmptiableRelativeBounds::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(UnboundedInterval.emptiable_rel_bounds());
    };

    complement_rel_bounds(bounds)
}

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
//! #     AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound, EmptiableAbsBoundPair
//! # };
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::complement::Complementable;
//! let interval = AbsBoundPair::new(
//!     AbsFiniteBoundPos::new_with_incl(
//!         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!         BoundInclusivity::Exclusive,
//!     ).to_start_bound(),
//!     AbsFiniteBoundPos::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     ).to_end_bound(),
//! );
//!
//! assert_eq!(
//!     interval.complement(),
//!     ComplementResult::Split(
//!         EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
//!             AbsStartBound::InfinitePast,
//!             AbsFiniteBoundPos::new(
//!                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!             ).to_end_bound(),
//!         )),
//!         EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
//!             AbsFiniteBoundPos::new_with_incl(
//!                 "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             ).to_start_bound(),
//!             AbsEndBound::InfiniteFuture,
//!         )),
//!     ),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{HasOpeningDirection, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelInterval,
    RelStartBound,
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
/// #     AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound, EmptiableAbsBoundPair,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::complement::Complementable;
/// let interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new_with_incl(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         BoundInclusivity::Exclusive,
///     ).to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.complement(),
///     ComplementResult::Split(
///         EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
///             AbsStartBound::InfinitePast,
///             AbsFiniteBoundPos::new(
///                 "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///             ).to_end_bound(),
///         )),
///         EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
///             AbsFiniteBoundPos::new_with_incl(
///                 "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///                 BoundInclusivity::Exclusive,
///             ).to_start_bound(),
///             AbsEndBound::InfiniteFuture,
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

impl Complementable for AbsBoundPair {
    type Output = EmptiableAbsBoundPair;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_abs_bound_pair(self)
    }
}

impl Complementable for EmptiableAbsBoundPair {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bound_pair(self)
    }
}

impl Complementable for AbsInterval {
    type Output = EmptiableAbsInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_abs_bound_pair(&self.abs_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for EmptiableAbsInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for BoundedAbsInterval {
    type Output = HalfBoundedAbsInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_bounded_abs_interval(self)
    }
}

impl Complementable for HalfBoundedAbsInterval {
    type Output = HalfBoundedAbsInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_half_bounded_abs_interval(self)
    }
}

impl Complementable for RelBoundPair {
    type Output = EmptiableRelBoundPair;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_rel_bound_pair(self)
    }
}

impl Complementable for EmptiableRelBoundPair {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bound_pair(self)
    }
}

impl Complementable for RelInterval {
    type Output = EmptiableRelInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_rel_bound_pair(&self.rel_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for EmptiableRelInterval {
    type Output = Self;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair()).map(Self::Output::from)
    }
}

impl Complementable for BoundedRelInterval {
    type Output = HalfBoundedRelInterval;

    fn complement(&self) -> ComplementResult<Self::Output> {
        complement_bounded_rel_interval(self)
    }
}

impl Complementable for HalfBoundedRelInterval {
    type Output = HalfBoundedRelInterval;

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

/// Returns the complementary intervals of an [`AbsBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_abs_bound_pair(bounds: &AbsBoundPair) -> ComplementResult<EmptiableAbsBoundPair> {
    type Sb = AbsStartBound;
    type Eb = AbsEndBound;

    match (bounds.abs_start(), bounds.abs_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_abs_bound_pair()),
        (Sb::InfinitePast, Eb::Finite(finite_end)) => ComplementResult::Single(
            AbsBoundPair::new(finite_end.opposite().to_start_bound(), AbsEndBound::InfiniteFuture).to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::InfiniteFuture) => ComplementResult::Single(
            AbsBoundPair::new(AbsStartBound::InfinitePast, finite_start.opposite().to_end_bound()).to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            AbsBoundPair::new(AbsStartBound::InfinitePast, finite_start.opposite().to_end_bound()).to_emptiable(),
            AbsBoundPair::new(finite_end.opposite().to_start_bound(), AbsEndBound::InfiniteFuture).to_emptiable(),
        ),
    }
}

/// Returns the complementary intervals of an [`EmptiableAbsBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_emptiable_abs_bound_pair(
    emptiable_bounds: &EmptiableAbsBoundPair,
) -> ComplementResult<EmptiableAbsBoundPair> {
    let EmptiableAbsBoundPair::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(UnboundedInterval.emptiable_abs_bound_pair());
    };

    complement_abs_bound_pair(bounds)
}

#[must_use]
pub fn complement_bounded_abs_interval(interval: &BoundedAbsInterval) -> ComplementResult<HalfBoundedAbsInterval> {
    let until_start = HalfBoundedAbsInterval::new_from_time_and_inclusivity(
        interval.start_time(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    );

    let since_end = HalfBoundedAbsInterval::new_from_time_and_inclusivity(
        interval.end_time(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    );

    ComplementResult::Split(until_start, since_end)
}

#[must_use]
pub fn complement_half_bounded_abs_interval(
    interval: &HalfBoundedAbsInterval,
) -> ComplementResult<HalfBoundedAbsInterval> {
    ComplementResult::Single(HalfBoundedAbsInterval::new_from_time_and_inclusivity(
        interval.reference_time(),
        interval.reference_inclusivity().opposite(),
        interval.opening_direction().opposite(),
    ))
}

/// Returns the complementary intervals of a [`RelBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_rel_bound_pair(bounds: &RelBoundPair) -> ComplementResult<EmptiableRelBoundPair> {
    type Sb = RelStartBound;
    type Eb = RelEndBound;

    match (bounds.rel_start(), bounds.rel_end()) {
        (Sb::InfinitePast, Eb::InfiniteFuture) => ComplementResult::Single(EmptyInterval.emptiable_rel_bound_pair()),
        (Sb::InfinitePast, Eb::Finite(finite_end)) => ComplementResult::Single(
            RelBoundPair::new(finite_end.opposite().to_start_bound(), RelEndBound::InfiniteFuture).to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::InfiniteFuture) => ComplementResult::Single(
            RelBoundPair::new(RelStartBound::InfinitePast, finite_start.opposite().to_end_bound()).to_emptiable(),
        ),
        (Sb::Finite(finite_start), Eb::Finite(finite_end)) => ComplementResult::Split(
            RelBoundPair::new(RelStartBound::InfinitePast, finite_start.opposite().to_end_bound()).to_emptiable(),
            RelBoundPair::new(finite_end.opposite().to_start_bound(), RelEndBound::InfiniteFuture).to_emptiable(),
        ),
    }
}

/// Returns the complementary intervals of an [`EmptiableRelBoundPair`]
///
/// See [`Complementable`] for more info.
#[must_use]
pub fn complement_emptiable_rel_bound_pair(
    emptiable_bounds: &EmptiableRelBoundPair,
) -> ComplementResult<EmptiableRelBoundPair> {
    let EmptiableRelBoundPair::Bound(bounds) = emptiable_bounds else {
        return ComplementResult::Single(UnboundedInterval.emptiable_rel_bound_pair());
    };

    complement_rel_bound_pair(bounds)
}

#[must_use]
pub fn complement_bounded_rel_interval(interval: &BoundedRelInterval) -> ComplementResult<HalfBoundedRelInterval> {
    let until_start = HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        interval.start_offset(),
        interval.start_inclusivity().opposite(),
        OpeningDirection::ToPast,
    );

    let since_end = HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        interval.end_offset(),
        interval.end_inclusivity().opposite(),
        OpeningDirection::ToFuture,
    );

    ComplementResult::Split(until_start, since_end)
}

#[must_use]
pub fn complement_half_bounded_rel_interval(
    interval: &HalfBoundedRelInterval,
) -> ComplementResult<HalfBoundedRelInterval> {
    ComplementResult::Single(HalfBoundedRelInterval::new_from_offset_and_inclusivity(
        interval.reference_offset(),
        interval.reference_inclusivity().opposite(),
        interval.opening_direction().opposite(),
    ))
}

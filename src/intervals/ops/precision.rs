//! Precision change for intervals and bounds
//!
//! This module is in charge of handling the act of changing the precision of intervals and bounds: (re-)_precising_.
//!
//! Precising intervals and bounds works differently depending
//! on their [`Relativity`](crate::intervals::meta::Relativity).
//!
//! For absolute structures, [`PreciseAbsoluteInterval`] handles intervals, [`PreciseAbsoluteBound`] handles bounds.
//!
//! For relative structures, the sibling traits do not exist as of version `0.1`, but are planned for future versions.
//!
//! The precision itself is defined by [`Precision`].
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Duration, Utc};
//! # use periodical::ops::Precision;
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
//! let interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 08:03:29.591Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 15:57:44.041Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! assert_eq!(
//!     interval.precise_interval(Precision::ToPast(Duration::minutes(5))),
//!     Ok(AbsoluteBounds::new(
//!         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!             "2025-01-01 15:55:00Z".parse::<DateTime<Utc>>()?,
//!         )),
//!     )),
//! );
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use chrono::{DateTime, Utc};

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::special::EmptyInterval;
use crate::ops::{Precision, PrecisionError};

/// Ability to precise absolute intervals
///
/// The precision itself is defined by [`Precision`].
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Duration, Utc};
/// # use periodical::ops::Precision;
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
/// let interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 08:03:29.591Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 15:57:44.041Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// assert_eq!(
///     interval.precise_interval(Precision::ToPast(Duration::minutes(5))),
///     Ok(AbsoluteBounds::new(
///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 15:55:00Z".parse::<DateTime<Utc>>()?,
///         )),
///     )),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait PreciseAbsoluteInterval {
    /// Output of methods precising an interval
    type PrecisedIntervalOutput;

    /// Precises the start and end bounds with different [`Precision`]s
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::ops::Precision;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:03:29.591Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 15:57:44.041Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval_with_different_precisions(
    ///         Precision::ToPast(Duration::minutes(5)),
    ///         Precision::ToFuture(Duration::minutes(5)),
    ///     ),
    ///     Ok(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     )),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn precise_interval_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput;

    /// Precises the start and end bounds with the given [`Precision`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::ops::Precision;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:03:29.591Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 15:57:44.041Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval(Precision::ToPast(Duration::minutes(5))),
    ///     Ok(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 15:55:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     )),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn precise_interval(&self, precision: Precision) -> Self::PrecisedIntervalOutput {
        self.precise_interval_with_different_precisions(precision, precision)
    }

    /// Precises the start and end bounds with different precisions and base times for both of them
    ///
    /// See [`Precision::precise_time_with_base_time`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::ops::Precision;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:11:29.591Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 15:57:44.041Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval_with_different_precisions_with_base_time(
    ///         Precision::ToFuture(Duration::minutes(7)),
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         Precision::ToPast(Duration::minutes(7)),
    ///         "2025-01-01 15:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ),
    ///     Ok(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:14:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 15:56:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     )),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedIntervalOutput;

    /// Precises the start and end bound with the given precision and base time
    ///
    /// See [`Precision::precise_time`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::ops::Precision;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:11:29.591Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 15:57:44.041Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval_with_base_time(
    ///         Precision::ToFuture(Duration::minutes(7)),
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ),
    ///     Ok(AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:14:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:03:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     )),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn precise_interval_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedIntervalOutput {
        self.precise_interval_with_different_precisions_with_base_time(precision, base, precision, base)
    }
}

impl PreciseAbsoluteInterval for AbsoluteBounds {
    type PrecisedIntervalOutput = Result<Self, PrecisionError>;

    fn precise_interval_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        precise_abs_bounds(self, precision_start, precision_end)
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedIntervalOutput {
        precise_abs_bounds_with_base_time(self, precision_start, base_start, precision_end, base_end)
    }
}

impl PreciseAbsoluteInterval for EmptiableAbsoluteBounds {
    type PrecisedIntervalOutput = Result<Self, PrecisionError>;

    fn precise_interval_with_different_precisions(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(EmptiableAbsoluteBounds::Bound(precise_abs_bounds(
                abs_bounds,
                start_precision,
                end_precision,
            )?));
        }

        Ok(EmptiableAbsoluteBounds::Empty)
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(EmptiableAbsoluteBounds::Bound(precise_abs_bounds_with_base_time(
                abs_bounds,
                precision_start,
                base_start,
                precision_end,
                base_end,
            )?));
        }

        Ok(EmptiableAbsoluteBounds::Empty)
    }
}

impl PreciseAbsoluteInterval for AbsoluteInterval {
    type PrecisedIntervalOutput = Result<Self, PrecisionError>;

    fn precise_interval_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBounds::Bound(ref abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(AbsoluteInterval::from(precise_abs_bounds(
                abs_bounds,
                precision_start,
                precision_end,
            )?));
        }

        Ok(AbsoluteInterval::Empty(EmptyInterval))
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBounds::Bound(ref abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(AbsoluteInterval::from(precise_abs_bounds_with_base_time(
                abs_bounds,
                precision_start,
                base_start,
                precision_end,
                base_end,
            )?));
        }

        Ok(AbsoluteInterval::Empty(EmptyInterval))
    }
}

/// Ability to precise absolute bounds
///
/// The precision itself is defined by [`Precision`].
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Duration, Utc};
/// # use periodical::ops::Precision;
/// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::precision::PreciseAbsoluteBound;
/// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///     "2025-01-01 08:24:41Z".parse::<DateTime<Utc>>()?,
///     BoundInclusivity::Exclusive,
/// ));
///
/// assert_eq!(
///     bound.precise_bound(Precision::ToFuture(Duration::minutes(5))),
///     Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///         "2025-01-01 08:25:00Z".parse::<DateTime<Utc>>()?,
///         BoundInclusivity::Exclusive,
///     ))),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait PreciseAbsoluteBound {
    type PrecisedBoundOutput;

    /// Precises the bound with the given precision
    ///
    /// See [`Precision::precise_time`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::ops::Precision;
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteBound;
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:24:41Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert_eq!(
    ///     bound.precise_bound(Precision::ToFuture(Duration::minutes(5))),
    ///     Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:25:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput;

    /// Precises the bound with the given precision and base time
    ///
    /// See [`Precision::precise_time_with_base_time`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::ops::Precision;
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteBound;
    /// let bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:24:41Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert_eq!(
    ///     bound.precise_bound_with_base_time(
    ///         Precision::ToFuture(Duration::minutes(7)),
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     ),
    ///     Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:28:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn precise_bound_with_base_time(&self, precision: Precision, base: DateTime<Utc>) -> Self::PrecisedBoundOutput;
}

impl PreciseAbsoluteBound for AbsoluteFiniteBound {
    type PrecisedBoundOutput = Result<Self, PrecisionError>;

    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_finite_bound(self, precision)
    }

    fn precise_bound_with_base_time(&self, precision: Precision, base: DateTime<Utc>) -> Self::PrecisedBoundOutput {
        precise_abs_finite_bound_with_base_time(self, precision, base)
    }
}

impl PreciseAbsoluteBound for AbsoluteStartBound {
    type PrecisedBoundOutput = Result<Self, PrecisionError>;

    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_start_bound(self, precision)
    }

    fn precise_bound_with_base_time(&self, precision: Precision, base: DateTime<Utc>) -> Self::PrecisedBoundOutput {
        precise_abs_start_bound_with_base_time(self, precision, base)
    }
}

impl PreciseAbsoluteBound for AbsoluteEndBound {
    type PrecisedBoundOutput = Result<Self, PrecisionError>;

    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_end_bound(self, precision)
    }

    fn precise_bound_with_base_time(&self, precision: Precision, base: DateTime<Utc>) -> Self::PrecisedBoundOutput {
        precise_abs_end_bound_with_base_time(self, precision, base)
    }
}

/// Precises [`AbsoluteBounds`] with the given [`Precision`]s
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_bounds(
    bounds: &AbsoluteBounds,
    precision_start: Precision,
    precision_end: Precision,
) -> Result<AbsoluteBounds, PrecisionError> {
    Ok(AbsoluteBounds::new(
        precise_abs_start_bound(bounds.start(), precision_start)?,
        precise_abs_end_bound(bounds.end(), precision_end)?,
    ))
}

/// Precises an [`AbsoluteFiniteBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_finite_bound(
    bound: &AbsoluteFiniteBound,
    precision: Precision,
) -> Result<AbsoluteFiniteBound, PrecisionError> {
    Ok(AbsoluteFiniteBound::new_with_inclusivity(
        precision.precise_time(bound.time())?,
        bound.inclusivity(),
    ))
}

/// Precises an [`AbsoluteStartBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_start_bound(
    bound: &AbsoluteStartBound,
    precision: Precision,
) -> Result<AbsoluteStartBound, PrecisionError> {
    match bound {
        AbsoluteStartBound::InfinitePast => Ok(*bound),
        AbsoluteStartBound::Finite(finite_bound) => {
            precise_abs_finite_bound(finite_bound, precision).map(AbsoluteStartBound::Finite)
        },
    }
}

/// Precises an [`AbsoluteEndBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_end_bound(
    bound: &AbsoluteEndBound,
    precision: Precision,
) -> Result<AbsoluteEndBound, PrecisionError> {
    match bound {
        AbsoluteEndBound::InfiniteFuture => Ok(*bound),
        AbsoluteEndBound::Finite(finite_bound) => {
            precise_abs_finite_bound(finite_bound, precision).map(AbsoluteEndBound::Finite)
        },
    }
}

/// Precises [`AbsoluteBounds`] with the given [`Precision`]s and base times
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_bounds_with_base_time(
    bounds: &AbsoluteBounds,
    precision_start: Precision,
    base_start: DateTime<Utc>,
    precision_end: Precision,
    base_end: DateTime<Utc>,
) -> Result<AbsoluteBounds, PrecisionError> {
    Ok(AbsoluteBounds::new(
        precise_abs_start_bound_with_base_time(bounds.start(), precision_start, base_start)?,
        precise_abs_end_bound_with_base_time(bounds.end(), precision_end, base_end)?,
    ))
}

/// Precises an [`AbsoluteFiniteBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_finite_bound_with_base_time(
    bound: &AbsoluteFiniteBound,
    precision: Precision,
    base: DateTime<Utc>,
) -> Result<AbsoluteFiniteBound, PrecisionError> {
    Ok(AbsoluteFiniteBound::new_with_inclusivity(
        precision.precise_time_with_base_time(bound.time(), base)?,
        bound.inclusivity(),
    ))
}

/// Precises an [`AbsoluteStartBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_start_bound_with_base_time(
    bound: &AbsoluteStartBound,
    precision: Precision,
    base: DateTime<Utc>,
) -> Result<AbsoluteStartBound, PrecisionError> {
    match bound {
        AbsoluteStartBound::InfinitePast => Ok(*bound),
        AbsoluteStartBound::Finite(finite_bound) => {
            precise_abs_finite_bound_with_base_time(finite_bound, precision, base).map(AbsoluteStartBound::Finite)
        },
    }
}

/// Precises an [`AbsoluteEndBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_end_bound_with_base_time(
    bound: &AbsoluteEndBound,
    precision: Precision,
    base: DateTime<Utc>,
) -> Result<AbsoluteEndBound, PrecisionError> {
    match bound {
        AbsoluteEndBound::InfiniteFuture => Ok(*bound),
        AbsoluteEndBound::Finite(finite_bound) => {
            precise_abs_finite_bound_with_base_time(finite_bound, precision, base).map(AbsoluteEndBound::Finite)
        },
    }
}

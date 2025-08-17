//! Interval bound re-precising

use chrono::{DateTime, Utc};

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::special::EmptyInterval;
use crate::ops::{Precision, PrecisionError};

/// Trait to try to re-precise absolute bounds
pub trait PreciseAbsoluteBounds {
    /// Output of methods precising the bounds
    type PrecisedBoundsOutput;

    /// Output of methods precising the start bound
    type PrecisedStartBoundOutput;

    /// Output of methods precising the end bound
    type PrecisedEndBoundOutput;

    /// Precises the start and end bound with different precisions for both of them
    #[must_use]
    fn precise_bounds_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedBoundsOutput;

    /// Precises the start and end bound with the given precision
    #[must_use]
    fn precise_bounds(&self, precision: Precision) -> Self::PrecisedBoundsOutput {
        self.precise_bounds_with_different_precisions(precision, precision)
    }

    /// Precises the start bound with the given precision
    #[must_use]
    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput;

    /// Precises the end bound with the given precision
    #[must_use]
    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput;

    /// Precises the start and end bound with different precisions and base times for both of them
    #[must_use]
    fn precise_bounds_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedBoundsOutput;

    /// Precises the start and end bound with the given precision and base time
    #[must_use]
    fn precise_bounds_with_base_time(&self, precision: Precision, base: DateTime<Utc>) -> Self::PrecisedBoundsOutput {
        self.precise_bounds_with_different_precisions_with_base_time(precision, base, precision, base)
    }

    /// Precises the start bound with the given precision and base time
    #[must_use]
    fn precise_start_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedStartBoundOutput;

    /// Precises the end bound with the given precision and base time
    #[must_use]
    fn precise_end_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedEndBoundOutput;
}

impl PreciseAbsoluteBounds for AbsoluteBounds {
    type PrecisedBoundsOutput = Result<Self, PrecisionError>;
    type PrecisedStartBoundOutput = Result<AbsoluteStartBound, PrecisionError>;
    type PrecisedEndBoundOutput = Result<AbsoluteEndBound, PrecisionError>;

    fn precise_bounds_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedBoundsOutput {
        precise_abs_bounds(self, precision_start, precision_end)
    }

    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput {
        precise_abs_start_bound(self.start(), precision)
    }

    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput {
        precise_abs_end_bound(self.end(), precision)
    }

    fn precise_bounds_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedBoundsOutput {
        precise_abs_bounds_with_base_time(self, precision_start, base_start, precision_end, base_end)
    }

    fn precise_start_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedStartBoundOutput {
        precise_abs_start_bound_with_base_time(self.start(), precision, base)
    }

    fn precise_end_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedEndBoundOutput {
        precise_abs_end_bound_with_base_time(self.end(), precision, base)
    }
}

impl PreciseAbsoluteBounds for EmptiableAbsoluteBounds {
    type PrecisedBoundsOutput = Result<Self, PrecisionError>;
    type PrecisedStartBoundOutput = Result<Option<AbsoluteStartBound>, PrecisionError>;
    type PrecisedEndBoundOutput = Result<Option<AbsoluteEndBound>, PrecisionError>;

    fn precise_bounds_with_different_precisions(
        &self,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Self::PrecisedBoundsOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(EmptiableAbsoluteBounds::Bound(precise_abs_bounds(
                abs_bounds,
                start_precision,
                end_precision,
            )?));
        }

        Ok(EmptiableAbsoluteBounds::Empty)
    }

    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(Some(precise_abs_start_bound(abs_bounds.start(), precision)?));
        }

        Ok(None)
    }

    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(Some(precise_abs_end_bound(abs_bounds.end(), precision)?));
        }

        Ok(None)
    }

    fn precise_bounds_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedBoundsOutput {
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

    fn precise_start_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedStartBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(Some(precise_abs_start_bound_with_base_time(
                abs_bounds.start(),
                precision,
                base,
            )?));
        }

        Ok(None)
    }

    fn precise_end_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedEndBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self {
            return Ok(Some(precise_abs_end_bound_with_base_time(
                abs_bounds.end(),
                precision,
                base,
            )?));
        }

        Ok(None)
    }
}

impl PreciseAbsoluteBounds for AbsoluteInterval {
    type PrecisedBoundsOutput = Result<Self, PrecisionError>;
    type PrecisedStartBoundOutput = Result<Option<AbsoluteStartBound>, PrecisionError>;
    type PrecisedEndBoundOutput = Result<Option<AbsoluteEndBound>, PrecisionError>;

    fn precise_bounds_with_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedBoundsOutput {
        if let EmptiableAbsoluteBounds::Bound(ref abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(AbsoluteInterval::from(precise_abs_bounds(
                abs_bounds,
                precision_start,
                precision_end,
            )?));
        }

        Ok(AbsoluteInterval::Empty(EmptyInterval))
    }

    fn precise_start_bound(&self, precision: Precision) -> Self::PrecisedStartBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(Some(precise_abs_start_bound(abs_bounds.start(), precision)?));
        }

        Ok(None)
    }

    fn precise_end_bound(&self, precision: Precision) -> Self::PrecisedEndBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(Some(precise_abs_end_bound(abs_bounds.end(), precision)?));
        }

        Ok(None)
    }

    fn precise_bounds_with_different_precisions_with_base_time(
        &self,
        precision_start: Precision,
        base_start: DateTime<Utc>,
        precision_end: Precision,
        base_end: DateTime<Utc>,
    ) -> Self::PrecisedBoundsOutput {
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

    fn precise_start_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedStartBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(Some(precise_abs_start_bound_with_base_time(
                abs_bounds.start(),
                precision,
                base,
            )?));
        }

        Ok(None)
    }

    fn precise_end_bound_with_base_time(
        &self,
        precision: Precision,
        base: DateTime<Utc>,
    ) -> Self::PrecisedEndBoundOutput {
        if let EmptiableAbsoluteBounds::Bound(abs_bounds) = self.emptiable_abs_bounds() {
            return Ok(Some(precise_abs_end_bound_with_base_time(
                abs_bounds.end(),
                precision,
                base,
            )?));
        }

        Ok(None)
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
            Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                precision.precise_time(finite_bound.time())?,
                finite_bound.inclusivity(),
            )))
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
            Ok(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                precision.precise_time(finite_bound.time())?,
                finite_bound.inclusivity(),
            )))
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
            Ok(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                precision.precise_time_with_base_time(finite_bound.time(), base)?,
                finite_bound.inclusivity(),
            )))
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
            Ok(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                precision.precise_time_with_base_time(finite_bound.time(), base)?,
                finite_bound.inclusivity(),
            )))
        },
    }
}

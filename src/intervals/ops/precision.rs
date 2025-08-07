//! Interval bound re-precising

use chrono::RoundingError;

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    EmptiableAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::special::EmptyInterval;
use crate::ops::Precision;

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
}

impl PreciseAbsoluteBounds for AbsoluteBounds {
    type PrecisedBoundsOutput = Result<Self, RoundingError>;
    type PrecisedStartBoundOutput = Result<AbsoluteStartBound, RoundingError>;
    type PrecisedEndBoundOutput = Result<AbsoluteEndBound, RoundingError>;

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
}

impl PreciseAbsoluteBounds for EmptiableAbsoluteBounds {
    type PrecisedBoundsOutput = Result<Self, RoundingError>;
    type PrecisedStartBoundOutput = Result<Option<AbsoluteStartBound>, RoundingError>;
    type PrecisedEndBoundOutput = Result<Option<AbsoluteEndBound>, RoundingError>;

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
}

impl PreciseAbsoluteBounds for AbsoluteInterval {
    type PrecisedBoundsOutput = Result<Self, RoundingError>;
    type PrecisedStartBoundOutput = Result<Option<AbsoluteStartBound>, RoundingError>;
    type PrecisedEndBoundOutput = Result<Option<AbsoluteEndBound>, RoundingError>;

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
}

/// Precises [`AbsoluteBounds`] with the given [`Precision`]s
///
/// # Errors
///
/// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
/// if the given duration used is too big, negative or zero, etc.
///
/// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
pub fn precise_abs_bounds(
    bounds: &AbsoluteBounds,
    precision_start: Precision,
    precision_end: Precision,
) -> Result<AbsoluteBounds, RoundingError> {
    Ok(AbsoluteBounds::new(
        precise_abs_start_bound(bounds.start(), precision_start)?,
        precise_abs_end_bound(bounds.end(), precision_end)?,
    ))
}

/// Precises an [`AbsoluteStartBound`] with the given [`Precision`]
///
/// # Errors
///
/// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
/// if the given duration used is too big, negative or zero, etc.
///
/// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
pub fn precise_abs_start_bound(
    bound: &AbsoluteStartBound,
    precision: Precision,
) -> Result<AbsoluteStartBound, RoundingError> {
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
/// Time conversions can fail for different reasons, for example if the time would overflow after conversion,
/// if the given duration used is too big, negative or zero, etc.
///
/// For more details, check [`chrono`'s limitations on the `DurationRound` trait](https://docs.rs/chrono/latest/chrono/round/trait.DurationRound.html#limitations).
pub fn precise_abs_end_bound(
    bound: &AbsoluteEndBound,
    precision: Precision,
) -> Result<AbsoluteEndBound, RoundingError> {
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

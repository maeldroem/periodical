//! Precision change for absolute bounds

use jiff::Timestamp;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::HasBoundInclusivity;
use crate::ops::{Precision, PrecisionOutOfRangeDateError};

/// Ability to precise absolute bounds
///
/// The precision itself is defined by [`Precision`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use std::time::Duration;
/// # use jiff::Zoned;
/// # use jiff::tz::TimeZone;
/// # use periodical::ops::{Precision, PrecisionMode};
/// # use periodical::intervals::absolute::AbsoluteFiniteBound;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::precision::PreciseAbsoluteBound;
/// let bound = AbsoluteFiniteBound::new_with_inclusivity(
///     "2025-01-01 08:24:41[Europe/Oslo]"
///         .parse::<Zoned>()?
///         .timestamp(),
///     BoundInclusivity::Exclusive,
/// )
/// .to_start_bound();
///
/// assert_eq!(
///     bound.precise_bound(
///         TimeZone::get("Europe/Oslo")?,
///         Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
///     ),
///     Ok(AbsoluteFiniteBound::new_with_inclusivity(
///         "2025-01-01 08:25:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///         BoundInclusivity::Exclusive,
///     )
///     .to_start_bound()),
/// );
/// # Ok::<(), Box<dyn Error>>(())
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
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteBound;
    /// let bound = AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:24:41[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     bound.precise_bound(
    ///         TimeZone::get("Europe/Oslo")?,
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
    ///     ),
    ///     Ok(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:25:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_start_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput;

    /// Precises the bound with the given precision and base time
    ///
    /// See [`Precision::precise_time_with_base_time`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteBound;
    /// let bound = AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:24:41[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     bound.precise_bound_with_base_time(
    ///         TimeZone::get("Europe/Oslo")?,
    ///         Precision::new(Duration::from_mins(7), PrecisionMode::ToFuture)?,
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     ),
    ///     Ok(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:28:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_start_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput;
}

impl PreciseAbsoluteBound for AbsoluteFiniteBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeDateError>;

    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_finite_bound(self, tz, precision)
    }

    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput {
        precise_abs_finite_bound_with_base_time(self, tz, precision, base)
    }
}

impl PreciseAbsoluteBound for AbsoluteStartBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeDateError>;

    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_start_bound(self, tz, precision)
    }

    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput {
        precise_abs_start_bound_with_base_time(self, tz, precision, base)
    }
}

impl PreciseAbsoluteBound for AbsoluteEndBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeDateError>;

    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_end_bound(self, tz, precision)
    }

    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput {
        precise_abs_end_bound_with_base_time(self, tz, precision, base)
    }
}

/// Precises [`AbsoluteBoundPair`] with the given [`Precision`]s
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_bound_pair(
    bounds: &AbsoluteBoundPair,
    tz: TimeZone,
    precision_start: Precision,
    precision_end: Precision,
) -> Result<AbsoluteBoundPair, PrecisionOutOfRangeDateError> {
    Ok(AbsoluteBoundPair::new(
        precise_abs_start_bound(&bounds.start(), tz.clone(), precision_start)?,
        precise_abs_end_bound(&bounds.end(), tz, precision_end)?,
    ))
}

/// Precises an [`AbsoluteFiniteBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_finite_bound(
    bound: &AbsoluteFiniteBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteFiniteBound, PrecisionOutOfRangeDateError> {
    Ok(AbsoluteFiniteBound::new_with_inclusivity(
        precision
            .precise_time(&bound.time().to_zoned(tz))?
            .compatible()
            .or(Err(PrecisionOutOfRangeDateError))?
            .timestamp(),
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
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteStartBound, PrecisionOutOfRangeDateError> {
    match bound {
        AbsoluteStartBound::InfinitePast => Ok(*bound),
        AbsoluteStartBound::Finite(finite_bound) => {
            precise_abs_finite_bound(finite_bound, tz, precision).map(AbsoluteStartBound::Finite)
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
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteEndBound, PrecisionOutOfRangeDateError> {
    match bound {
        AbsoluteEndBound::InfiniteFuture => Ok(*bound),
        AbsoluteEndBound::Finite(finite_bound) => {
            precise_abs_finite_bound(finite_bound, tz, precision).map(AbsoluteEndBound::Finite)
        },
    }
}

/// Precises [`AbsoluteBoundPair`] with the given [`Precision`]s and base times
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_bound_pair_with_base_time(
    bounds: &AbsoluteBoundPair,
    tz: TimeZone,
    precision_start: Precision,
    base_start: Timestamp,
    precision_end: Precision,
    base_end: Timestamp,
) -> Result<AbsoluteBoundPair, PrecisionOutOfRangeDateError> {
    Ok(AbsoluteBoundPair::new(
        precise_abs_start_bound_with_base_time(&bounds.start(), tz.clone(), precision_start, base_start)?,
        precise_abs_end_bound_with_base_time(&bounds.end(), tz, precision_end, base_end)?,
    ))
}

/// Precises an [`AbsoluteFiniteBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_finite_bound_with_base_time(
    bound: &AbsoluteFiniteBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteFiniteBound, PrecisionOutOfRangeDateError> {
    Ok(AbsoluteFiniteBound::new_with_inclusivity(
        precision
            .precise_time_with_base_time(&bound.time().to_zoned(tz), base)?
            .timestamp(),
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
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteStartBound, PrecisionOutOfRangeDateError> {
    match bound {
        AbsoluteStartBound::InfinitePast => Ok(*bound),
        AbsoluteStartBound::Finite(finite_bound) => {
            precise_abs_finite_bound_with_base_time(finite_bound, tz, precision, base).map(AbsoluteStartBound::Finite)
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
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteEndBound, PrecisionOutOfRangeDateError> {
    match bound {
        AbsoluteEndBound::InfiniteFuture => Ok(*bound),
        AbsoluteEndBound::Finite(finite_bound) => {
            precise_abs_finite_bound_with_base_time(finite_bound, tz, precision, base).map(AbsoluteEndBound::Finite)
        },
    }
}

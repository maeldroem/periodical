//! Precision change for absolute bounds

use jiff::Timestamp;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteFiniteEndBound,
    AbsoluteFiniteStartBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::HasBoundInclusivity;
use crate::ops::{Precision, PrecisionOutOfRangeError};

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
/// # use periodical::intervals::absolute::AbsoluteFiniteBoundPosition;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::PreciseAbsoluteBound;
/// let bound = AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
///     Ok(AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
    /// Output of methods precising a bound
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
    /// # use periodical::intervals::absolute::AbsoluteFiniteBoundPosition;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseAbsoluteBound;
    /// let bound = AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
    ///     Ok(AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
    /// # use periodical::intervals::absolute::AbsoluteFiniteBoundPosition;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseAbsoluteBound;
    /// let bound = AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
    ///     Ok(AbsoluteFiniteBoundPosition::new_with_inclusivity(
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

impl PreciseAbsoluteBound for AbsoluteFiniteBoundPosition {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_finite_bound_position(self, tz, precision)
    }

    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput {
        precise_abs_finite_bound_position_with_base_time(self, tz, precision, base)
    }
}

impl PreciseAbsoluteBound for AbsoluteFiniteStartBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_finite_start_bound(self, tz, precision)
    }

    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput {
        precise_abs_finite_start_bound_with_base_time(self, tz, precision, base)
    }
}

impl PreciseAbsoluteBound for AbsoluteFiniteEndBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_finite_end_bound(self, tz, precision)
    }

    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput {
        precise_abs_finite_end_bound_with_base_time(self, tz, precision, base)
    }
}

impl PreciseAbsoluteBound for AbsoluteFiniteBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

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
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

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
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

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

impl PreciseAbsoluteBound for AbsoluteBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_bound(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_abs_bound(self, tz, precision)
    }

    fn precise_bound_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedBoundOutput {
        precise_abs_bound_with_base_time(self, tz, precision, base)
    }
}

/// Precises an [`AbsoluteFiniteBoundPosition`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_finite_bound_position(
    pos: &AbsoluteFiniteBoundPosition,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteFiniteBoundPosition, PrecisionOutOfRangeError> {
    Ok(AbsoluteFiniteBoundPosition::new_with_inclusivity(
        precision
            .precise_time(&pos.time().to_zoned(tz))?
            .compatible()
            .or(Err(PrecisionOutOfRangeError))?
            .timestamp(),
        pos.inclusivity(),
    ))
}

/// Precises an [`AbsoluteFiniteBoundPosition`] with the given [`Precision`] and base time
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_finite_bound_position_with_base_time(
    pos: &AbsoluteFiniteBoundPosition,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteFiniteBoundPosition, PrecisionOutOfRangeError> {
    Ok(AbsoluteFiniteBoundPosition::new_with_inclusivity(
        precision
            .precise_time_with_base_time(&pos.time().to_zoned(tz), base)?
            .timestamp(),
        pos.inclusivity(),
    ))
}

pub fn precise_abs_finite_start_bound(
    bound: &AbsoluteFiniteStartBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteFiniteStartBound, PrecisionOutOfRangeError> {
    Ok(AbsoluteFiniteStartBound::new(precise_abs_finite_bound_position(
        &bound.pos(),
        tz,
        precision,
    )?))
}

pub fn precise_abs_finite_start_bound_with_base_time(
    bound: &AbsoluteFiniteStartBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteFiniteStartBound, PrecisionOutOfRangeError> {
    Ok(AbsoluteFiniteStartBound::new(
        precise_abs_finite_bound_position_with_base_time(&bound.pos(), tz, precision, base)?,
    ))
}

pub fn precise_abs_finite_end_bound(
    bound: &AbsoluteFiniteEndBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteFiniteEndBound, PrecisionOutOfRangeError> {
    Ok(AbsoluteFiniteEndBound::new(precise_abs_finite_bound_position(
        &bound.pos(),
        tz,
        precision,
    )?))
}

pub fn precise_abs_finite_end_bound_with_base_time(
    bound: &AbsoluteFiniteEndBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteFiniteEndBound, PrecisionOutOfRangeError> {
    Ok(AbsoluteFiniteEndBound::new(
        precise_abs_finite_bound_position_with_base_time(&bound.pos(), tz, precision, base)?,
    ))
}

pub fn precise_abs_finite_bound(
    bound: &AbsoluteFiniteBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteFiniteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteFiniteBound::Start(finite_start) => {
            AbsoluteFiniteBound::Start(precise_abs_finite_start_bound(finite_start, tz, precision)?)
        },
        AbsoluteFiniteBound::End(finite_end) => {
            AbsoluteFiniteBound::End(precise_abs_finite_end_bound(finite_end, tz, precision)?)
        },
    })
}

pub fn precise_abs_finite_bound_with_base_time(
    bound: &AbsoluteFiniteBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteFiniteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteFiniteBound::Start(finite_start) => AbsoluteFiniteBound::Start(
            precise_abs_finite_start_bound_with_base_time(finite_start, tz, precision, base)?,
        ),
        AbsoluteFiniteBound::End(finite_end) => AbsoluteFiniteBound::End(precise_abs_finite_end_bound_with_base_time(
            finite_end, tz, precision, base,
        )?),
    })
}

pub fn precise_abs_start_bound(
    bound: &AbsoluteStartBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteStartBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteStartBound::Finite(finite_start) => {
            AbsoluteStartBound::Finite(precise_abs_finite_start_bound(finite_start, tz, precision)?)
        },
        AbsoluteStartBound::InfinitePast => *bound,
    })
}

pub fn precise_abs_start_bound_with_base_time(
    bound: &AbsoluteStartBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteStartBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteStartBound::Finite(finite_start) => AbsoluteStartBound::Finite(
            precise_abs_finite_start_bound_with_base_time(finite_start, tz, precision, base)?,
        ),
        AbsoluteStartBound::InfinitePast => *bound,
    })
}

pub fn precise_abs_end_bound(
    bound: &AbsoluteEndBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteEndBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteEndBound::Finite(finite_end) => {
            AbsoluteEndBound::Finite(precise_abs_finite_end_bound(finite_end, tz, precision)?)
        },
        AbsoluteEndBound::InfiniteFuture => *bound,
    })
}

pub fn precise_abs_end_bound_with_base_time(
    bound: &AbsoluteEndBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteEndBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteEndBound::Finite(finite_end) => AbsoluteEndBound::Finite(precise_abs_finite_end_bound_with_base_time(
            finite_end, tz, precision, base,
        )?),
        AbsoluteEndBound::InfiniteFuture => *bound,
    })
}

pub fn precise_abs_bound(
    bound: &AbsoluteBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsoluteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteBound::Start(start_bound) => AbsoluteBound::Start(precise_abs_start_bound(start_bound, tz, precision)?),
        AbsoluteBound::End(end_bound) => AbsoluteBound::End(precise_abs_end_bound(end_bound, tz, precision)?),
    })
}

pub fn precise_abs_bound_with_base_time(
    bound: &AbsoluteBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsoluteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsoluteBound::Start(start_bound) => AbsoluteBound::Start(precise_abs_start_bound_with_base_time(
            start_bound,
            tz,
            precision,
            base,
        )?),
        AbsoluteBound::End(end_bound) => {
            AbsoluteBound::End(precise_abs_end_bound_with_base_time(end_bound, tz, precision, base)?)
        },
    })
}

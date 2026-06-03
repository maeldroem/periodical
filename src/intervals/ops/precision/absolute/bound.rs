//! Precision change for absolute bounds

use jiff::Timestamp;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{
    AbsBound,
    AbsEndBound,
    AbsFiniteBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
    AbsStartBound,
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
/// # use periodical::intervals::absolute::AbsFiniteBoundPos;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::PreciseAbsBound;
/// let bound = AbsFiniteBoundPos::new_with_incl(
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
///     Ok(AbsFiniteBoundPos::new_with_incl(
///         "2025-01-01 08:25:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///         BoundInclusivity::Exclusive,
///     )
///     .to_start_bound()),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait PreciseAbsBound {
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
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseAbsBound;
    /// let bound = AbsFiniteBoundPos::new_with_incl(
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
    ///     Ok(AbsFiniteBoundPos::new_with_incl(
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
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseAbsBound;
    /// let bound = AbsFiniteBoundPos::new_with_incl(
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
    ///     Ok(AbsFiniteBoundPos::new_with_incl(
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

impl PreciseAbsBound for AbsFiniteBoundPos {
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

impl PreciseAbsBound for AbsFiniteStartBound {
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

impl PreciseAbsBound for AbsFiniteEndBound {
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

impl PreciseAbsBound for AbsFiniteBound {
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

impl PreciseAbsBound for AbsStartBound {
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

impl PreciseAbsBound for AbsEndBound {
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

impl PreciseAbsBound for AbsBound {
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

/// Precises an [`AbsFiniteBoundPos`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_finite_bound_position(
    pos: &AbsFiniteBoundPos,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsFiniteBoundPos, PrecisionOutOfRangeError> {
    Ok(AbsFiniteBoundPos::new_with_incl(
        precision
            .precise_time(&pos.time().to_zoned(tz))?
            .compatible()
            .or(Err(PrecisionOutOfRangeError))?
            .timestamp(),
        pos.inclusivity(),
    ))
}

/// Precises an [`AbsFiniteBoundPos`] with the given [`Precision`] and base time
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_finite_bound_position_with_base_time(
    pos: &AbsFiniteBoundPos,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsFiniteBoundPos, PrecisionOutOfRangeError> {
    Ok(AbsFiniteBoundPos::new_with_incl(
        precision
            .precise_time_with_base_time(&pos.time().to_zoned(tz), base)?
            .timestamp(),
        pos.inclusivity(),
    ))
}

pub fn precise_abs_finite_start_bound(
    bound: &AbsFiniteStartBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsFiniteStartBound, PrecisionOutOfRangeError> {
    Ok(AbsFiniteStartBound::new(precise_abs_finite_bound_position(
        &bound.pos(),
        tz,
        precision,
    )?))
}

pub fn precise_abs_finite_start_bound_with_base_time(
    bound: &AbsFiniteStartBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsFiniteStartBound, PrecisionOutOfRangeError> {
    Ok(AbsFiniteStartBound::new(
        precise_abs_finite_bound_position_with_base_time(&bound.pos(), tz, precision, base)?,
    ))
}

pub fn precise_abs_finite_end_bound(
    bound: &AbsFiniteEndBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsFiniteEndBound, PrecisionOutOfRangeError> {
    Ok(AbsFiniteEndBound::new(precise_abs_finite_bound_position(
        &bound.pos(),
        tz,
        precision,
    )?))
}

pub fn precise_abs_finite_end_bound_with_base_time(
    bound: &AbsFiniteEndBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsFiniteEndBound, PrecisionOutOfRangeError> {
    Ok(AbsFiniteEndBound::new(
        precise_abs_finite_bound_position_with_base_time(&bound.pos(), tz, precision, base)?,
    ))
}

pub fn precise_abs_finite_bound(
    bound: &AbsFiniteBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsFiniteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsFiniteBound::Start(finite_start) => {
            AbsFiniteBound::Start(precise_abs_finite_start_bound(finite_start, tz, precision)?)
        },
        AbsFiniteBound::End(finite_end) => {
            AbsFiniteBound::End(precise_abs_finite_end_bound(finite_end, tz, precision)?)
        },
    })
}

pub fn precise_abs_finite_bound_with_base_time(
    bound: &AbsFiniteBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsFiniteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsFiniteBound::Start(finite_start) => AbsFiniteBound::Start(precise_abs_finite_start_bound_with_base_time(
            finite_start,
            tz,
            precision,
            base,
        )?),
        AbsFiniteBound::End(finite_end) => AbsFiniteBound::End(precise_abs_finite_end_bound_with_base_time(
            finite_end, tz, precision, base,
        )?),
    })
}

pub fn precise_abs_start_bound(
    bound: &AbsStartBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsStartBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsStartBound::Finite(finite_start) => {
            AbsStartBound::Finite(precise_abs_finite_start_bound(finite_start, tz, precision)?)
        },
        AbsStartBound::InfinitePast => *bound,
    })
}

pub fn precise_abs_start_bound_with_base_time(
    bound: &AbsStartBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsStartBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsStartBound::Finite(finite_start) => AbsStartBound::Finite(precise_abs_finite_start_bound_with_base_time(
            finite_start,
            tz,
            precision,
            base,
        )?),
        AbsStartBound::InfinitePast => *bound,
    })
}

pub fn precise_abs_end_bound(
    bound: &AbsEndBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsEndBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsEndBound::Finite(finite_end) => {
            AbsEndBound::Finite(precise_abs_finite_end_bound(finite_end, tz, precision)?)
        },
        AbsEndBound::InfiniteFuture => *bound,
    })
}

pub fn precise_abs_end_bound_with_base_time(
    bound: &AbsEndBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsEndBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsEndBound::Finite(finite_end) => AbsEndBound::Finite(precise_abs_finite_end_bound_with_base_time(
            finite_end, tz, precision, base,
        )?),
        AbsEndBound::InfiniteFuture => *bound,
    })
}

pub fn precise_abs_bound(
    bound: &AbsBound,
    tz: TimeZone,
    precision: Precision,
) -> Result<AbsBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsBound::Start(start_bound) => AbsBound::Start(precise_abs_start_bound(start_bound, tz, precision)?),
        AbsBound::End(end_bound) => AbsBound::End(precise_abs_end_bound(end_bound, tz, precision)?),
    })
}

pub fn precise_abs_bound_with_base_time(
    bound: &AbsBound,
    tz: TimeZone,
    precision: Precision,
    base: Timestamp,
) -> Result<AbsBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        AbsBound::Start(start_bound) => AbsBound::Start(precise_abs_start_bound_with_base_time(
            start_bound,
            tz,
            precision,
            base,
        )?),
        AbsBound::End(end_bound) => {
            AbsBound::End(precise_abs_end_bound_with_base_time(end_bound, tz, precision, base)?)
        },
    })
}

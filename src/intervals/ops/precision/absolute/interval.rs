//! Precision change for absolute intervals

use jiff::Timestamp;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::ops::precision::absolute::bound::{
    precise_abs_end_bound,
    precise_abs_end_bound_with_base_time,
    precise_abs_start_bound,
    precise_abs_start_bound_with_base_time,
};
use crate::intervals::special::EmptyInterval;
use crate::ops::{Precision, PrecisionOutOfRangeError};

/// Ability to precise absolute intervals
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
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::precision::PreciseAbsInterval;
/// let interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:03:29.591[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsFiniteBoundPos::new(
///         "2025-01-01 15:57:44.041[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.precise_interval(
///         TimeZone::get("Europe/Oslo")?,
///         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
///     ),
///     Ok(AbsBoundPair::new(
///         AbsFiniteBoundPos::new(
///             "2025-01-01 08:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsFiniteBoundPos::new(
///             "2025-01-01 15:55:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_end_bound(),
///     )),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait PreciseAbsInterval {
    /// Output of methods precising an interval
    type PrecisedIntervalOutput;

    /// Precises the start and end bounds with different [`Precision`]s
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
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::precision::PreciseAbsInterval;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:03:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 15:57:44.041[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval_with_different_precisions(
    ///         TimeZone::get("Europe/Oslo")?,
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
    ///     ),
    ///     Ok(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput;

    /// Precises the start and end bounds with the given [`Precision`]
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
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::precision::PreciseAbsInterval;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:03:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 15:57:44.041[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval(
    ///         TimeZone::get("Europe/Oslo")?,
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
    ///     ),
    ///     Ok(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 15:55:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_interval(&self, tz: TimeZone, precision: Precision) -> Self::PrecisedIntervalOutput {
        self.precise_interval_with_different_precisions(tz, precision, precision)
    }

    /// Precises the start and end bounds with different precisions and base
    /// times for both of them
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
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::precision::PreciseAbsInterval;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:11:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 15:57:44.041[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval_with_different_precisions_with_base_time(
    ///         TimeZone::get("Europe/Oslo")?,
    ///         Precision::new(Duration::from_mins(7), PrecisionMode::ToFuture)?,
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///         Precision::new(Duration::from_mins(7), PrecisionMode::ToPast)?,
    ///         "2025-01-01 15:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     ),
    ///     Ok(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:14:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 15:56:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput;

    /// Precises the start and end bound with the given precision and base time
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
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::precision::PreciseAbsInterval;
    /// let interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:11:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 15:57:44.041[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_interval_with_base_time(
    ///         TimeZone::get("Europe/Oslo")?,
    ///         Precision::new(Duration::from_mins(7), PrecisionMode::ToFuture)?,
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     ),
    ///     Ok(AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:14:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 16:03:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_interval_with_base_time(
        &self,
        tz: TimeZone,
        precision: Precision,
        base: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        self.precise_interval_with_different_precisions_with_base_time(tz, precision, base, precision, base)
    }
}

impl PreciseAbsInterval for AbsBoundPair {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        precise_abs_bound_pair(self, tz, precision_start, precision_end)
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        precise_abs_bound_pair_with_base_time(self, tz, precision_start, base_start, precision_end, base_end)
    }
}

impl PreciseAbsInterval for EmptiableAbsBoundPair {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let Self::Bound(abs_bound_pair) = self {
            Ok(precise_abs_bound_pair(abs_bound_pair, tz, start_precision, end_precision)?.to_emptiable())
        } else {
            Ok(Self::Empty)
        }
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        if let Self::Bound(abs_bound_pair) = self {
            Ok(precise_abs_bound_pair_with_base_time(
                abs_bound_pair,
                tz,
                precision_start,
                base_start,
                precision_end,
                base_end,
            )?
            .to_emptiable())
        } else {
            Ok(Self::Empty)
        }
    }
}

impl PreciseAbsInterval for AbsInterval {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        Ok(precise_abs_bound_pair(&self.abs_bound_pair(), tz, precision_start, precision_end)?.to_interval())
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        Ok(precise_abs_bound_pair_with_base_time(
            &self.abs_bound_pair(),
            tz,
            precision_start,
            base_start,
            precision_end,
            base_end,
        )?
        .to_interval())
    }
}

impl PreciseAbsInterval for EmptiableAbsInterval {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsBoundPair::Bound(ref abs_bound_pair) = self.emptiable_abs_bound_pair() {
            Ok(precise_abs_bound_pair(abs_bound_pair, tz, precision_start, precision_end)?.to_emptiable_interval())
        } else {
            Ok(Self::Empty(EmptyInterval))
        }
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsBoundPair::Bound(ref abs_bound_pair) = self.emptiable_abs_bound_pair() {
            Ok(precise_abs_bound_pair_with_base_time(
                abs_bound_pair,
                tz,
                precision_start,
                base_start,
                precision_end,
                base_end,
            )?
            .to_emptiable_interval())
        } else {
            Ok(Self::Empty(EmptyInterval))
        }
    }
}

/// Precises [`AbsBoundPair`] with the given [`Precision`]s
///
/// # Errors
///
/// See [`Precision::precise_time`]
pub fn precise_abs_bound_pair(
    bound_pair: &AbsBoundPair,
    tz: TimeZone,
    precision_start: Precision,
    precision_end: Precision,
) -> Result<AbsBoundPair, PrecisionOutOfRangeError> {
    Ok(AbsBoundPair::new(
        precise_abs_start_bound(&bound_pair.start(), tz.clone(), precision_start)?,
        precise_abs_end_bound(&bound_pair.end(), tz, precision_end)?,
    ))
}

/// Precises [`AbsBoundPair`] with the given [`Precision`]s and base times
///
/// # Errors
///
/// See [`Precision::precise_time_with_base_time`]
pub fn precise_abs_bound_pair_with_base_time(
    bound_pair: &AbsBoundPair,
    tz: TimeZone,
    precision_start: Precision,
    base_start: Timestamp,
    precision_end: Precision,
    base_end: Timestamp,
) -> Result<AbsBoundPair, PrecisionOutOfRangeError> {
    Ok(AbsBoundPair::new(
        precise_abs_start_bound_with_base_time(&bound_pair.start(), tz.clone(), precision_start, base_start)?,
        precise_abs_end_bound_with_base_time(&bound_pair.end(), tz, precision_end, base_end)?,
    ))
}

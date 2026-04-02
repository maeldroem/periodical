//! Precision change for absolute intervals

use jiff::Timestamp;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::ops::precision::absolute::bound::{
    precise_abs_bound_pair,
    precise_abs_bound_pair_with_base_time,
};
use crate::intervals::special::EmptyInterval;
use crate::ops::{Precision, PrecisionOutOfRangeDateError};

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
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
/// let interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:03:29.591[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBound::new(
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
///     Ok(AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsoluteFiniteBound::new(
///             "2025-01-01 15:55:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_end_bound(),
///     )),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait PreciseAbsoluteInterval {
    /// Output of methods precising an interval
    type PrecisedIntervalOutput;

    /// Precises the start and end bounds with different [`Precision`]s
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:03:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
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
    ///     Ok(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
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
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::Zoned;
    /// # use jiff::tz::TimeZone;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:03:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
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
    ///     Ok(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
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
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:11:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
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
    ///     Ok(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:14:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
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
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::precision::PreciseAbsoluteInterval;
    /// let interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:11:29.591[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
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
    ///     Ok(AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:14:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
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
        self.precise_interval_with_different_precisions_with_base_time(tz, precision, base.clone(), precision, base)
    }
}

impl PreciseAbsoluteInterval for AbsoluteBoundPair {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeDateError>;

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

impl PreciseAbsoluteInterval for EmptiableAbsoluteBoundPair {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeDateError>;

    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        start_precision: Precision,
        end_precision: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBoundPair::Bound(abs_bound_pair) = self {
            return Ok(EmptiableAbsoluteBoundPair::Bound(precise_abs_bound_pair(
                abs_bound_pair,
                tz,
                start_precision,
                end_precision,
            )?));
        }

        Ok(EmptiableAbsoluteBoundPair::Empty)
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBoundPair::Bound(abs_bound_pair) = self {
            return Ok(EmptiableAbsoluteBoundPair::Bound(
                precise_abs_bound_pair_with_base_time(
                    abs_bound_pair,
                    tz,
                    precision_start,
                    base_start,
                    precision_end,
                    base_end,
                )?,
            ));
        }

        Ok(EmptiableAbsoluteBoundPair::Empty)
    }
}

impl PreciseAbsoluteInterval for AbsoluteInterval {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeDateError>;

    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        Ok(AbsoluteInterval::from(precise_abs_bound_pair(
            &self.abs_bound_pair(),
            tz,
            precision_start,
            precision_end,
        )?))
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        Ok(AbsoluteInterval::from(precise_abs_bound_pair_with_base_time(
            &self.abs_bound_pair(),
            tz,
            precision_start,
            base_start,
            precision_end,
            base_end,
        )?))
    }
}

impl PreciseAbsoluteInterval for EmptiableAbsoluteInterval {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeDateError>;

    fn precise_interval_with_different_precisions(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBoundPair::Bound(ref abs_bound_pair) = self.emptiable_abs_bound_pair() {
            return Ok(EmptiableAbsoluteInterval::from(precise_abs_bound_pair(
                abs_bound_pair,
                tz,
                precision_start,
                precision_end,
            )?));
        }

        Ok(EmptiableAbsoluteInterval::Empty(EmptyInterval))
    }

    fn precise_interval_with_different_precisions_with_base_time(
        &self,
        tz: TimeZone,
        precision_start: Precision,
        base_start: Timestamp,
        precision_end: Precision,
        base_end: Timestamp,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableAbsoluteBoundPair::Bound(ref abs_bound_pair) = self.emptiable_abs_bound_pair() {
            return Ok(EmptiableAbsoluteInterval::from(precise_abs_bound_pair_with_base_time(
                abs_bound_pair,
                tz,
                precision_start,
                base_start,
                precision_end,
                base_end,
            )?));
        }

        Ok(EmptiableAbsoluteInterval::Empty(EmptyInterval))
    }
}

//! Precision change for relative intervals
//!
//! See [module documentation](crate::intervals::ops::precision) for more info.

use jiff::SignedDuration;

use crate::intervals::ops::precision::relative::bound::{
    precise_rel_end_bound,
    precise_rel_end_bound_with_base_offset,
    precise_rel_start_bound,
    precise_rel_start_bound_with_base_offset,
};
use crate::intervals::relative::{
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelInterval,
};
use crate::intervals::special::EmptyInterval;
use crate::ops::{Precision, PrecisionOutOfRangeError};

/// Ability to precise relative intervals
///
/// The precision itself is defined by [`Precision`].
///
/// See [module documentation](crate::intervals::ops::precision) for more info.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use std::time::Duration;
/// # use jiff::SignedDuration;
/// # use periodical::ops::{Precision, PrecisionMode};
/// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
/// # use periodical::intervals::ops::PreciseRelInterval;
/// let interval = RelBoundPair::new(
///     RelFiniteBoundPos::new(SignedDuration::from_mins(3)).to_start_bound(),
///     RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(57))
///         .to_end_bound(),
/// );
///
/// assert_eq!(
///     interval.precise(Precision::new(
///         Duration::from_mins(5),
///         PrecisionMode::ToPast
///     )?),
///     Ok(RelBoundPair::new(
///         RelFiniteBoundPos::new(SignedDuration::ZERO).to_start_bound(),
///         RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(55))
///             .to_end_bound(),
///     )),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait PreciseRelInterval {
    /// Precised interval type
    type PrecisedIntervalOutput;

    /// Precises the start and end bounds with different [`Precision`]s
    ///
    /// See [`Precision::precise_signed_duration`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// # use periodical::intervals::ops::PreciseRelInterval;
    /// let interval = RelBoundPair::new(
    ///     RelFiniteBoundPos::new(SignedDuration::from_mins(3)).to_start_bound(),
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(57))
    ///         .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_different_precisions(
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
    ///     ),
    ///     Ok(RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::ZERO).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput;

    /// Precises the start and end bounds with the given [`Precision`]
    ///
    /// See [`Precision::precise_signed_duration`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// # use periodical::intervals::ops::PreciseRelInterval;
    /// let interval = RelBoundPair::new(
    ///     RelFiniteBoundPos::new(SignedDuration::from_mins(3)).to_start_bound(),
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(57))
    ///         .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise(Precision::new(
    ///         Duration::from_mins(5),
    ///         PrecisionMode::ToPast
    ///     )?),
    ///     Ok(RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::ZERO).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(55))
    ///             .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise(&self, precision: Precision) -> Self::PrecisedIntervalOutput {
        self.precise_different_precisions(precision, precision)
    }

    /// Precises the start and end bounds with different precisions and base
    /// offsets for both of them
    ///
    /// See [`Precision::precise_signed_duration_with_base_offset`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// # use periodical::intervals::ops::PreciseRelInterval;
    /// let interval = RelBoundPair::new(
    ///     RelFiniteBoundPos::new(SignedDuration::from_mins(13)).to_start_bound(),
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(57))
    ///         .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_different_precisions_with_base_offset(
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
    ///         SignedDuration::from_mins(2),
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
    ///         SignedDuration::from_mins(1),
    ///     ),
    ///     Ok(RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_mins(12)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(8) + SignedDuration::from_mins(1))
    ///             .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_different_precisions_with_base_offset(
        &self,
        precision_start: Precision,
        base_start: SignedDuration,
        precision_end: Precision,
        base_end: SignedDuration,
    ) -> Self::PrecisedIntervalOutput;

    /// Precises the start and end bound with the given precision and base time
    ///
    /// See [`Precision::precise_signed_duration_with_base_offset`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use std::time::Duration;
    /// # use jiff::SignedDuration;
    /// # use periodical::ops::{Precision, PrecisionMode};
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// # use periodical::intervals::ops::PreciseRelInterval;
    /// let interval = RelBoundPair::new(
    ///     RelFiniteBoundPos::new(SignedDuration::from_mins(13)).to_start_bound(),
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(58))
    ///         .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     interval.precise_with_base_offset(
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToPast)?,
    ///         SignedDuration::from_mins(2),
    ///     ),
    ///     Ok(RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_mins(12)).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(7) + SignedDuration::from_mins(57))
    ///             .to_end_bound(),
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedIntervalOutput {
        self.precise_different_precisions_with_base_offset(precision, base, precision, base)
    }
}

impl PreciseRelInterval for RelBoundPair {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        precise_rel_bound_pair(self, precision_start, precision_end)
    }

    fn precise_different_precisions_with_base_offset(
        &self,
        precision_start: Precision,
        base_start: SignedDuration,
        precision_end: Precision,
        base_end: SignedDuration,
    ) -> Self::PrecisedIntervalOutput {
        precise_rel_bound_pair_with_base_offset(self, precision_start, base_start, precision_end, base_end)
    }
}

impl PreciseRelInterval for EmptiableRelBoundPair {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let Self::Bound(rel_bound_pair) = self {
            Ok(precise_rel_bound_pair(rel_bound_pair, precision_start, precision_end)?.to_emptiable())
        } else {
            Ok(Self::Empty)
        }
    }

    fn precise_different_precisions_with_base_offset(
        &self,
        precision_start: Precision,
        base_start: SignedDuration,
        precision_end: Precision,
        base_end: SignedDuration,
    ) -> Self::PrecisedIntervalOutput {
        if let Self::Bound(rel_bound_pair) = self {
            Ok(precise_rel_bound_pair_with_base_offset(
                rel_bound_pair,
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

impl PreciseRelInterval for RelInterval {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        Ok(precise_rel_bound_pair(&self.rel_bound_pair(), precision_start, precision_end)?.to_interval())
    }

    fn precise_different_precisions_with_base_offset(
        &self,
        precision_start: Precision,
        base_start: SignedDuration,
        precision_end: Precision,
        base_end: SignedDuration,
    ) -> Self::PrecisedIntervalOutput {
        Ok(precise_rel_bound_pair_with_base_offset(
            &self.rel_bound_pair(),
            precision_start,
            base_start,
            precision_end,
            base_end,
        )?
        .to_interval())
    }
}

impl PreciseRelInterval for EmptiableRelInterval {
    type PrecisedIntervalOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_different_precisions(
        &self,
        precision_start: Precision,
        precision_end: Precision,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableRelBoundPair::Bound(ref rel_bound_pair) = self.emptiable_rel_bound_pair() {
            Ok(precise_rel_bound_pair(rel_bound_pair, precision_start, precision_end)?.to_emptiable_interval())
        } else {
            Ok(Self::Empty(EmptyInterval))
        }
    }

    fn precise_different_precisions_with_base_offset(
        &self,
        precision_start: Precision,
        base_start: SignedDuration,
        precision_end: Precision,
        base_end: SignedDuration,
    ) -> Self::PrecisedIntervalOutput {
        if let EmptiableRelBoundPair::Bound(ref rel_bound_pair) = self.emptiable_rel_bound_pair() {
            Ok(precise_rel_bound_pair_with_base_offset(
                rel_bound_pair,
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

/// Precises [`RelBoundPair`] with the given [`Precision`]s
///
/// # Errors
///
/// See [`Precision::precise_signed_duration`]
pub fn precise_rel_bound_pair(
    bound_pair: &RelBoundPair,
    precision_start: Precision,
    precision_end: Precision,
) -> Result<RelBoundPair, PrecisionOutOfRangeError> {
    Ok(RelBoundPair::new(
        precise_rel_start_bound(&bound_pair.start(), precision_start)?,
        precise_rel_end_bound(&bound_pair.end(), precision_end)?,
    ))
}

/// Precises [`RelBoundPair`] with the given [`Precision`]s and base offsets
///
/// # Errors
///
/// See [`Precision::precise_signed_duration_with_base_offset`]
pub fn precise_rel_bound_pair_with_base_offset(
    bound_pair: &RelBoundPair,
    precision_start: Precision,
    base_start: SignedDuration,
    precision_end: Precision,
    base_end: SignedDuration,
) -> Result<RelBoundPair, PrecisionOutOfRangeError> {
    Ok(RelBoundPair::new(
        precise_rel_start_bound_with_base_offset(&bound_pair.start(), precision_start, base_start)?,
        precise_rel_end_bound_with_base_offset(&bound_pair.end(), precision_end, base_end)?,
    ))
}

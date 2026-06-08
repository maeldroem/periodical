//! Precision change for relative bounds
//!
//! See [module documentation](crate::intervals::ops::precision) for more info.

use jiff::SignedDuration;

use crate::intervals::relative::{
    RelBound,
    RelEndBound,
    RelFiniteBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelFiniteStartBound,
    RelStartBound,
};
use crate::ops::{Precision, PrecisionOutOfRangeError};
use crate::prelude::HasBoundInclusivity;

/// Ability to precise relative bounds
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
/// # use periodical::intervals::relative::RelFiniteBoundPos;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::PreciseRelBound;
/// let bound = RelFiniteBoundPos::new_with_incl(
///     SignedDuration::from_mins(24),
///     BoundInclusivity::Exclusive,
/// )
/// .to_start_bound();
///
/// assert_eq!(
///     bound.precise(Precision::new(
///         Duration::from_mins(5),
///         PrecisionMode::ToFuture
///     )?),
///     Ok(RelFiniteBoundPos::new_with_incl(
///         SignedDuration::from_mins(25),
///         BoundInclusivity::Exclusive,
///     )
///     .to_start_bound())
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait PreciseRelBound {
    /// Type of the resulting precised bound
    type PrecisedBoundOutput;

    /// Precises the bound with the given precision
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
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseRelBound;
    /// let bound = RelFiniteBoundPos::new_with_incl(
    ///     SignedDuration::from_mins(24),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     bound.precise(Precision::new(
    ///         Duration::from_mins(5),
    ///         PrecisionMode::ToFuture
    ///     )?),
    ///     Ok(RelFiniteBoundPos::new_with_incl(
    ///         SignedDuration::from_mins(25),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_start_bound())
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput;

    /// Precises the bound with the given precision and base offset
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
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseRelBound;
    /// let bound = RelFiniteBoundPos::new_with_incl(
    ///     SignedDuration::from_mins(24),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     bound.precise_with_base_offset(
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
    ///         SignedDuration::from_mins(2)
    ///     ),
    ///     Ok(RelFiniteBoundPos::new_with_incl(
    ///         SignedDuration::from_mins(27),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_start_bound())
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput;
}

impl PreciseRelBound for RelFiniteBoundPos {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_finite_bound_pos(self, precision)
    }

    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_finite_bound_pos_with_base_offset(self, precision, base)
    }
}

impl PreciseRelBound for RelFiniteStartBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_finite_start_bound(self, precision)
    }

    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_finite_start_bound_with_base_offset(self, precision, base)
    }
}

impl PreciseRelBound for RelFiniteEndBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_finite_end_bound(self, precision)
    }

    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_finite_end_bound_with_base_offset(self, precision, base)
    }
}

impl PreciseRelBound for RelFiniteBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_finite_bound(self, precision)
    }

    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_finite_bound_with_base_offset(self, precision, base)
    }
}

impl PreciseRelBound for RelStartBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_start_bound(self, precision)
    }

    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_start_bound_with_base_offset(self, precision, base)
    }
}

impl PreciseRelBound for RelEndBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_end_bound(self, precision)
    }

    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_end_bound_with_base_offset(self, precision, base)
    }
}

impl PreciseRelBound for RelBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_bound(self, precision)
    }

    fn precise_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_bound_with_base_offset(self, precision, base)
    }
}

/// Precises an [`RelFiniteBoundPos`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_signed_duration`]
pub fn precise_rel_finite_bound_pos(
    bound: &RelFiniteBoundPos,
    precision: Precision,
) -> Result<RelFiniteBoundPos, PrecisionOutOfRangeError> {
    Ok(RelFiniteBoundPos::new_with_incl(
        precision.precise_signed_duration(bound.offset())?,
        bound.inclusivity(),
    ))
}

/// Precises an [`RelFiniteBoundPos`] with the given [`Precision`] and base offset
///
/// # Errors
///
/// See [`Precision::precise_signed_duration_with_base_offset`]
pub fn precise_rel_finite_bound_pos_with_base_offset(
    bound: &RelFiniteBoundPos,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelFiniteBoundPos, PrecisionOutOfRangeError> {
    Ok(RelFiniteBoundPos::new_with_incl(
        precision.precise_signed_duration_with_base_offset(bound.offset(), base)?,
        bound.inclusivity(),
    ))
}

/// Precises an [`RelFiniteStartBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`precise_rel_finite_bound_pos`]
pub fn precise_rel_finite_start_bound(
    bound: &RelFiniteStartBound,
    precision: Precision,
) -> Result<RelFiniteStartBound, PrecisionOutOfRangeError> {
    Ok(RelFiniteStartBound::new(precise_rel_finite_bound_pos(
        &bound.pos(),
        precision,
    )?))
}

/// Precises an [`RelFiniteStartBound`] with the given [`Precision`] and base offset
///
/// # Errors
///
/// See [`precise_rel_finite_bound_pos_with_base_offset`]
pub fn precise_rel_finite_start_bound_with_base_offset(
    bound: &RelFiniteStartBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelFiniteStartBound, PrecisionOutOfRangeError> {
    Ok(RelFiniteStartBound::new(precise_rel_finite_bound_pos_with_base_offset(
        &bound.pos(),
        precision,
        base,
    )?))
}

/// Precises an [`RelFiniteEndBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`precise_rel_finite_bound_pos`]
pub fn precise_rel_finite_end_bound(
    bound: &RelFiniteEndBound,
    precision: Precision,
) -> Result<RelFiniteEndBound, PrecisionOutOfRangeError> {
    Ok(RelFiniteEndBound::new(precise_rel_finite_bound_pos(
        &bound.pos(),
        precision,
    )?))
}

/// Precises an [`RelFiniteEndBound`] with the given [`Precision`] and base offset
///
/// # Errors
///
/// See [`precise_rel_finite_bound_pos_with_base_offset`]
pub fn precise_rel_finite_end_bound_with_base_offset(
    bound: &RelFiniteEndBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelFiniteEndBound, PrecisionOutOfRangeError> {
    Ok(RelFiniteEndBound::new(precise_rel_finite_bound_pos_with_base_offset(
        &bound.pos(),
        precision,
        base,
    )?))
}

/// Precises an [`RelFiniteBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`precise_rel_finite_bound_pos`]
pub fn precise_rel_finite_bound(
    bound: &RelFiniteBound,
    precision: Precision,
) -> Result<RelFiniteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelFiniteBound::Start(finite_start) => {
            RelFiniteBound::Start(precise_rel_finite_start_bound(finite_start, precision)?)
        },
        RelFiniteBound::End(finite_end) => RelFiniteBound::End(precise_rel_finite_end_bound(finite_end, precision)?),
    })
}

/// Precises an [`RelFiniteBound`] with the given [`Precision`] and base offset
///
/// # Errors
///
/// See [`precise_rel_finite_bound_pos_with_base_offset`]
pub fn precise_rel_finite_bound_with_base_offset(
    bound: &RelFiniteBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelFiniteBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelFiniteBound::Start(finite_start) => RelFiniteBound::Start(precise_rel_finite_start_bound_with_base_offset(
            finite_start,
            precision,
            base,
        )?),
        RelFiniteBound::End(finite_end) => RelFiniteBound::End(precise_rel_finite_end_bound_with_base_offset(
            finite_end, precision, base,
        )?),
    })
}

/// Precises an [`RelStartBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`precise_rel_finite_start_bound`]
pub fn precise_rel_start_bound(
    bound: &RelStartBound,
    precision: Precision,
) -> Result<RelStartBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelStartBound::Finite(finite_start) => {
            RelStartBound::Finite(precise_rel_finite_start_bound(finite_start, precision)?)
        },
        RelStartBound::InfinitePast => *bound,
    })
}

/// Precises an [`RelStartBound`] with the given [`Precision`] and base offset
///
/// # Errors
///
/// See [`precise_rel_finite_start_bound_with_base_offset`]
pub fn precise_rel_start_bound_with_base_offset(
    bound: &RelStartBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelStartBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelStartBound::Finite(finite_start) => RelStartBound::Finite(precise_rel_finite_start_bound_with_base_offset(
            finite_start,
            precision,
            base,
        )?),
        RelStartBound::InfinitePast => *bound,
    })
}

/// Precises an [`RelEndBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`precise_rel_finite_end_bound`]
pub fn precise_rel_end_bound(
    bound: &RelEndBound,
    precision: Precision,
) -> Result<RelEndBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelEndBound::Finite(finite_end) => RelEndBound::Finite(precise_rel_finite_end_bound(finite_end, precision)?),
        RelEndBound::InfiniteFuture => *bound,
    })
}

/// Precises an [`RelEndBound`] with the given [`Precision`] and base offset
///
/// # Errors
///
/// See [`precise_rel_finite_end_bound_with_base_offset`]
pub fn precise_rel_end_bound_with_base_offset(
    bound: &RelEndBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelEndBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelEndBound::Finite(finite_end) => RelEndBound::Finite(precise_rel_finite_end_bound_with_base_offset(
            finite_end, precision, base,
        )?),
        RelEndBound::InfiniteFuture => *bound,
    })
}

/// Precises an [`RelBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`precise_rel_finite_bound`]
pub fn precise_rel_bound(bound: &RelBound, precision: Precision) -> Result<RelBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelBound::Start(start_bound) => RelBound::Start(precise_rel_start_bound(start_bound, precision)?),
        RelBound::End(end_bound) => RelBound::End(precise_rel_end_bound(end_bound, precision)?),
    })
}

/// Precises an [`RelBound`] with the given [`Precision`] and base offset
///
/// # Errors
///
/// See [`precise_rel_finite_bound_with_base_offset`]
pub fn precise_rel_bound_with_base_offset(
    bound: &RelBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelBound, PrecisionOutOfRangeError> {
    Ok(match bound {
        RelBound::Start(start_bound) => {
            RelBound::Start(precise_rel_start_bound_with_base_offset(start_bound, precision, base)?)
        },
        RelBound::End(end_bound) => RelBound::End(precise_rel_end_bound_with_base_offset(end_bound, precision, base)?),
    })
}

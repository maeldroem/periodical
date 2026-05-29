//! Precision change for relative bounds

use jiff::SignedDuration;

use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBoundPosition, RelativeStartBound};
use crate::ops::{Precision, PrecisionOutOfRangeError};
use crate::prelude::HasBoundInclusivity;

/// Ability to precise relative bounds
///
/// The precision itself is defined by [`Precision`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use std::time::Duration;
/// # use jiff::SignedDuration;
/// # use periodical::ops::{Precision, PrecisionMode};
/// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::PreciseRelativeBound;
/// let bound = RelativeFiniteBoundPosition::new_with_inclusivity(
///     SignedDuration::from_mins(24),
///     BoundInclusivity::Exclusive,
/// )
/// .to_start_bound();
///
/// assert_eq!(
///     bound.precise_bound(Precision::new(
///         Duration::from_mins(5),
///         PrecisionMode::ToFuture
///     )?),
///     Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
///         SignedDuration::from_mins(25),
///         BoundInclusivity::Exclusive,
///     )
///     .to_start_bound())
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait PreciseRelativeBound {
    /// Output of methods precising a bound
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
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseRelativeBound;
    /// let bound = RelativeFiniteBoundPosition::new_with_inclusivity(
    ///     SignedDuration::from_mins(24),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     bound.precise_bound(Precision::new(
    ///         Duration::from_mins(5),
    ///         PrecisionMode::ToFuture
    ///     )?),
    ///     Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
    ///         SignedDuration::from_mins(25),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_start_bound())
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput;

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
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::PreciseRelativeBound;
    /// let bound = RelativeFiniteBoundPosition::new_with_inclusivity(
    ///     SignedDuration::from_mins(24),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     bound.precise_bound_with_base_offset(
    ///         Precision::new(Duration::from_mins(5), PrecisionMode::ToFuture)?,
    ///         SignedDuration::from_mins(2)
    ///     ),
    ///     Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
    ///         SignedDuration::from_mins(27),
    ///         BoundInclusivity::Exclusive,
    ///     )
    ///     .to_start_bound())
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn precise_bound_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput;
}

impl PreciseRelativeBound for RelativeFiniteBoundPosition {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_finite_bound_position(self, precision)
    }

    fn precise_bound_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_finite_bound_with_base_offset(self, precision, base)
    }
}

impl PreciseRelativeBound for RelativeStartBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_start_bound(self, precision)
    }

    fn precise_bound_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_start_bound_with_base_offset(self, precision, base)
    }
}

impl PreciseRelativeBound for RelativeEndBound {
    type PrecisedBoundOutput = Result<Self, PrecisionOutOfRangeError>;

    fn precise_bound(&self, precision: Precision) -> Self::PrecisedBoundOutput {
        precise_rel_end_bound(self, precision)
    }

    fn precise_bound_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput {
        precise_rel_end_bound_with_base_offset(self, precision, base)
    }
}

/// Precises an [`RelativeFiniteBoundPosition`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_signed_duration`]
pub fn precise_rel_finite_bound_position(
    bound: &RelativeFiniteBoundPosition,
    precision: Precision,
) -> Result<RelativeFiniteBoundPosition, PrecisionOutOfRangeError> {
    Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
        precision.precise_signed_duration(bound.offset())?,
        bound.inclusivity(),
    ))
}

/// Precises an [`RelativeStartBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_signed_duration`]
pub fn precise_rel_start_bound(
    bound: &RelativeStartBound,
    precision: Precision,
) -> Result<RelativeStartBound, PrecisionOutOfRangeError> {
    match bound {
        RelativeStartBound::InfinitePast => Ok(*bound),
        RelativeStartBound::Finite(finite_bound_position) => {
            precise_rel_finite_bound_position(finite_bound_position, precision).map(RelativeFiniteBoundPosition::to_start_bound)
        },
    }
}

/// Precises an [`RelativeEndBound`] with the given [`Precision`]
///
/// # Errors
///
/// See [`Precision::precise_signed_duration`]
pub fn precise_rel_end_bound(
    bound: &RelativeEndBound,
    precision: Precision,
) -> Result<RelativeEndBound, PrecisionOutOfRangeError> {
    match bound {
        RelativeEndBound::InfiniteFuture => Ok(*bound),
        RelativeEndBound::Finite(finite_bound_position) => {
            precise_rel_finite_bound_position(finite_bound_position, precision).map(RelativeFiniteBoundPosition::to_end_bound)
        },
    }
}

/// Precises an [`RelativeFiniteBoundPosition`] with the given [`Precision`] and base time
///
/// # Errors
///
/// See [`Precision::precise_signed_duration_with_base_offset`]
pub fn precise_rel_finite_bound_with_base_offset(
    bound: &RelativeFiniteBoundPosition,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelativeFiniteBoundPosition, PrecisionOutOfRangeError> {
    Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
        precision.precise_signed_duration_with_base_offset(bound.offset(), base)?,
        bound.inclusivity(),
    ))
}

/// Precises an [`RelativeStartBound`] with the given [`Precision`] and base time
///
/// # Errors
///
/// See [`Precision::precise_signed_duration_with_base_offset`]
pub fn precise_rel_start_bound_with_base_offset(
    bound: &RelativeStartBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelativeStartBound, PrecisionOutOfRangeError> {
    match bound {
        RelativeStartBound::InfinitePast => Ok(*bound),
        RelativeStartBound::Finite(finite_bound_position) => {
            precise_rel_finite_bound_with_base_offset(finite_bound_position, precision, base)
                .map(RelativeFiniteBoundPosition::to_start_bound)
        },
    }
}

/// Precises an [`RelativeEndBound`] with the given [`Precision`] and base time
///
/// # Errors
///
/// See [`Precision::precise_signed_duration_with_base_offset`]
pub fn precise_rel_end_bound_with_base_offset(
    bound: &RelativeEndBound,
    precision: Precision,
    base: SignedDuration,
) -> Result<RelativeEndBound, PrecisionOutOfRangeError> {
    match bound {
        RelativeEndBound::InfiniteFuture => Ok(*bound),
        RelativeEndBound::Finite(finite_bound_position) => {
            precise_rel_finite_bound_with_base_offset(finite_bound_position, precision, base)
                .map(RelativeFiniteBoundPosition::to_end_bound)
        },
    }
}

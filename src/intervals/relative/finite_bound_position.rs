//! Relative finite bound
//!
//! A relative finite bound has two components: an offset, represented by a
//! [`SignedDuration`], and a [bound inclusivity](BoundInclusivity).
//!
//! Relative finite bounds are usually converted into either an
//! [`RelativeStartBound`] through the [`to_start_bound`](RelativeFiniteBoundPosition::to_start_bound) method,
//! or into an [`RelativeEndBound`] through the [`to_end_bound`](RelativeFiniteBoundPosition::to_end_bound) method.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::{
    RelativeEndBound,
    RelativeFiniteEndBound,
    RelativeFiniteStartBound,
    RelativeStartBound,
};

/// A relative finite bound
///
/// Contains an offset [`SignedDuration`] and an ambiguous [`BoundInclusivity`]:
/// if it is [`Exclusive`](BoundInclusivity::Exclusive), then we additionally
/// need the _extremality_ (whether it acts as the start or end of an interval) in
/// order to know what this position truly encompasses.
///
/// This is why when comparing finite bound positions, only its offset is used.
///
/// # Examples
///
/// ## Basic use
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
/// let finite_bound_position = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(21));
/// ```
///
/// ## Creating an [`RelativeFiniteBoundPosition`] with an explicit [`BoundInclusivity`]
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
/// # use periodical::intervals::meta::BoundInclusivity;
/// let finite_bound_position = RelativeFiniteBoundPosition::new_with_inclusivity(
///     SignedDuration::from_hours(21),
///     BoundInclusivity::Exclusive,
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeFiniteBoundPosition {
    offset: SignedDuration,
    inclusivity: BoundInclusivity,
}

impl RelativeFiniteBoundPosition {
    /// Creates a new [`RelativeFiniteBoundPosition`] using the given offset
    ///
    /// This creates a finite bound using the [default `BoundInclusivity`](BoundInclusivity::default)
    #[must_use]
    pub fn new(offset: SignedDuration) -> Self {
        Self::new_with_inclusivity(offset, BoundInclusivity::default())
    }

    /// Creates a new [`RelativeFiniteBoundPosition`] using the given offset and
    /// [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_inclusivity(offset: SignedDuration, inclusivity: BoundInclusivity) -> Self {
        RelativeFiniteBoundPosition {
            offset,
            inclusivity,
        }
    }

    /// Returns the offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// let finite_bound_position = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(12));
    ///
    /// assert_eq!(
    ///     finite_bound_position.offset(),
    ///     SignedDuration::from_hours(12)
    /// );
    /// ```
    #[must_use]
    pub fn offset(&self) -> SignedDuration {
        self.offset
    }

    /// Sets the offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// let mut finite_bound_position = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1));
    /// finite_bound_position.set_offset(SignedDuration::from_hours(32));
    ///
    /// assert_eq!(
    ///     finite_bound_position.offset(),
    ///     SignedDuration::from_hours(32)
    /// );
    /// ```
    pub fn set_offset(&mut self, offset: SignedDuration) {
        self.offset = offset;
    }

    /// Sets the inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelativeFiniteBoundPosition;
    /// # use periodical::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
    /// let mut finite_bound_position = RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1));
    /// finite_bound_position.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     finite_bound_position.inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    pub fn set_inclusivity(&mut self, inclusivity: BoundInclusivity) {
        self.inclusivity = inclusivity;
    }

    #[must_use]
    pub fn to_finite_start_bound(self) -> RelativeFiniteStartBound {
        RelativeFiniteStartBound::new(self)
    }

    /// Wraps the finite bound in an [`RelativeStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> RelativeStartBound {
        RelativeStartBound::from(self)
    }

    #[must_use]
    pub fn to_finite_end_bound(self) -> RelativeFiniteEndBound {
        RelativeFiniteEndBound::new(self)
    }

    /// Wraps the finite bound in an [`RelativeEndBound`]
    #[must_use]
    pub fn to_end_bound(self) -> RelativeEndBound {
        RelativeEndBound::from(self)
    }
}

impl HasBoundInclusivity for RelativeFiniteBoundPosition {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl PartialOrd for RelativeFiniteBoundPosition {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeFiniteBoundPosition {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl From<SignedDuration> for RelativeFiniteBoundPosition {
    fn from(value: SignedDuration) -> Self {
        RelativeFiniteBoundPosition::new(value)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for RelativeFiniteBoundPosition {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        RelativeFiniteBoundPosition::new_with_inclusivity(offset, inclusivity)
    }
}

/// Error that can occur when trying to convert [`Bound<SignedDuration>`] into [`RelativeFiniteBoundPosition`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelativeFiniteBoundPositionTryFromBoundError;

impl Display for RelativeFiniteBoundPositionTryFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `Bound<SignedDuration>` into `RelativeFiniteBoundPosition`"
        )
    }
}

impl Error for RelativeFiniteBoundPositionTryFromBoundError {}

impl TryFrom<Bound<SignedDuration>> for RelativeFiniteBoundPosition {
    type Error = RelativeFiniteBoundPositionTryFromBoundError;

    fn try_from(value: Bound<SignedDuration>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(offset) => Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
                offset,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(offset) => Ok(RelativeFiniteBoundPosition::new_with_inclusivity(
                offset,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => Err(RelativeFiniteBoundPositionTryFromBoundError),
        }
    }
}

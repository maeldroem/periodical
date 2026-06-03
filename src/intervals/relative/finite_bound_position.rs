//! Relative finite bound
//!
//! A relative finite bound has two components: an offset, represented by a
//! [`SignedDuration`], and a [bound inclusivity](BoundInclusivity).
//!
//! Relative finite bounds are usually converted into either an
//! [`RelStartBound`] through the [`to_start_bound`](RelFiniteBoundPos::to_start_bound) method,
//! or into an [`RelEndBound`] through the [`to_end_bound`](RelFiniteBoundPos::to_end_bound) method.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::{RelEndBound, RelFiniteEndBound, RelFiniteStartBound, RelStartBound};

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
/// # use periodical::intervals::relative::RelFiniteBoundPos;
/// let finite_bound_position = RelFiniteBoundPos::new(SignedDuration::from_hours(21));
/// ```
///
/// ## Creating an [`RelFiniteBoundPos`] with an explicit [`BoundInclusivity`]
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::RelFiniteBoundPos;
/// # use periodical::intervals::meta::BoundInclusivity;
/// let finite_bound_position = RelFiniteBoundPos::new_with_incl(
///     SignedDuration::from_hours(21),
///     BoundInclusivity::Exclusive,
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelFiniteBoundPos {
    offset: SignedDuration,
    inclusivity: BoundInclusivity,
}

impl RelFiniteBoundPos {
    /// Creates a new [`RelFiniteBoundPos`] using the given offset
    ///
    /// This creates a finite bound using the [default `BoundInclusivity`](BoundInclusivity::default)
    #[must_use]
    pub fn new(offset: SignedDuration) -> Self {
        Self::new_with_incl(offset, BoundInclusivity::default())
    }

    /// Creates a new [`RelFiniteBoundPos`] using the given offset and
    /// [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_incl(offset: SignedDuration, inclusivity: BoundInclusivity) -> Self {
        RelFiniteBoundPos {
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
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// let finite_bound_position = RelFiniteBoundPos::new(SignedDuration::from_hours(12));
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
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// let mut finite_bound_position = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
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
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// # use periodical::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
    /// let mut finite_bound_position = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
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
    pub fn to_finite_start_bound(self) -> RelFiniteStartBound {
        RelFiniteStartBound::new(self)
    }

    /// Wraps the finite bound in an [`RelStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> RelStartBound {
        RelStartBound::from(self)
    }

    #[must_use]
    pub fn to_finite_end_bound(self) -> RelFiniteEndBound {
        RelFiniteEndBound::new(self)
    }

    /// Wraps the finite bound in an [`RelEndBound`]
    #[must_use]
    pub fn to_end_bound(self) -> RelEndBound {
        RelEndBound::from(self)
    }
}

impl HasBoundInclusivity for RelFiniteBoundPos {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl PartialOrd for RelFiniteBoundPos {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelFiniteBoundPos {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl From<SignedDuration> for RelFiniteBoundPos {
    fn from(value: SignedDuration) -> Self {
        RelFiniteBoundPos::new(value)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for RelFiniteBoundPos {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        RelFiniteBoundPos::new_with_incl(offset, inclusivity)
    }
}

/// Error that can occur when trying to convert [`Bound<SignedDuration>`] into [`RelFiniteBoundPos`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelFiniteBoundPosTryFromBoundError;

impl Display for RelFiniteBoundPosTryFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `Bound<SignedDuration>` into `RelFiniteBoundPos`"
        )
    }
}

impl Error for RelFiniteBoundPosTryFromBoundError {}

impl TryFrom<Bound<SignedDuration>> for RelFiniteBoundPos {
    type Error = RelFiniteBoundPosTryFromBoundError;

    fn try_from(value: Bound<SignedDuration>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(offset) => Ok(RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Inclusive)),
            Bound::Excluded(offset) => Ok(RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive)),
            Bound::Unbounded => Err(RelFiniteBoundPosTryFromBoundError),
        }
    }
}

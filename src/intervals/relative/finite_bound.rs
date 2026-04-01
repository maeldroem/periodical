//! Relative finite bound
//!
//! A relative finite bound has two components: an offset, represented by a
//! [`SignedDuration`], and a [bound inclusivity](BoundInclusivity).
//!
//! Relative finite bounds are usually converted into either an
//! [`RelativeStartBound`] through the [`to_start_bound`](RelativeFiniteBound::to_start_bound) method,
//! or into an [`RelativeEndBound`] through the [`to_end_bound`](RelativeFiniteBound::to_end_bound) method.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::{RelativeEndBound, RelativeStartBound};

/// A relative finite bound
///
/// Contains an offset [`SignedDuration`] and an ambiguous [`BoundInclusivity`]:
/// if it is [`Exclusive`](BoundInclusivity::Exclusive), then we additionally
/// need the _source_ (whether it acts as the start or end of an interval) in
/// order to know what this bound truly encompasses.
///
/// This is why when comparing finite bounds, only its position (for relative
/// bounds, its offset) is used.
///
/// # Examples
///
/// ## Basic use
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::RelativeFiniteBound;
/// let finite_bound = RelativeFiniteBound::new(SignedDuration::from_hours(21));
/// ```
///
/// ## Creating an [`RelativeFiniteBound`] with an explicit [`BoundInclusivity`]
///
/// ```
/// # use jiff::SignedDuration;
/// # use periodical::intervals::relative::RelativeFiniteBound;
/// # use periodical::intervals::meta::BoundInclusivity;
/// let finite_bound = RelativeFiniteBound::new_with_inclusivity(
///     SignedDuration::from_hours(21),
///     BoundInclusivity::Exclusive,
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeFiniteBound {
    pub(crate) offset: SignedDuration,
    pub(crate) inclusivity: BoundInclusivity,
}

impl RelativeFiniteBound {
    /// Creates a new [`RelativeFiniteBound`] using the given offset
    ///
    /// This creates a finite bound using the [default
    /// `BoundInclusivity`](BoundInclusivity::default)
    #[must_use]
    pub fn new(offset: SignedDuration) -> Self {
        Self::new_with_inclusivity(offset, BoundInclusivity::default())
    }

    /// Creates a new [`RelativeFiniteBound`] using the given offset and
    /// [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_inclusivity(offset: SignedDuration, inclusivity: BoundInclusivity) -> Self {
        RelativeFiniteBound {
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
    /// # use periodical::intervals::relative::RelativeFiniteBound;
    /// let finite_bound = RelativeFiniteBound::new(SignedDuration::from_hours(12));
    ///
    /// assert_eq!(finite_bound.offset(), SignedDuration::from_hours(12));
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
    /// # use periodical::intervals::relative::RelativeFiniteBound;
    /// let mut finite_bound = RelativeFiniteBound::new(SignedDuration::from_hours(1));
    /// finite_bound.set_offset(SignedDuration::from_hours(32));
    ///
    /// assert_eq!(finite_bound.offset(), SignedDuration::from_hours(32));
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
    /// # use periodical::intervals::relative::RelativeFiniteBound;
    /// # use periodical::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
    /// let mut finite_bound = RelativeFiniteBound::new(SignedDuration::from_hours(1));
    /// finite_bound.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(finite_bound.inclusivity(), BoundInclusivity::Exclusive);
    /// ```
    pub fn set_inclusivity(&mut self, inclusivity: BoundInclusivity) {
        self.inclusivity = inclusivity;
    }

    /// Wraps the finite bound in an [`RelativeStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> RelativeStartBound {
        RelativeStartBound::from(self)
    }

    /// Wraps the finite bound in an [`RelativeEndBound`]
    #[must_use]
    pub fn to_end_bound(self) -> RelativeEndBound {
        RelativeEndBound::from(self)
    }
}

impl HasBoundInclusivity for RelativeFiniteBound {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl PartialOrd for RelativeFiniteBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeFiniteBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl From<SignedDuration> for RelativeFiniteBound {
    fn from(value: SignedDuration) -> Self {
        RelativeFiniteBound::new(value)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for RelativeFiniteBound {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        RelativeFiniteBound::new_with_inclusivity(offset, inclusivity)
    }
}

/// Error that can occur when trying to convert [`Bound<SignedDuration>`] into [`RelativeFiniteBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelativeFiniteBoundTryFromBoundError;

impl Display for RelativeFiniteBoundTryFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `Bound<SignedDuration>` into `RelativeFiniteBound`"
        )
    }
}

impl Error for RelativeFiniteBoundTryFromBoundError {}

impl TryFrom<Bound<SignedDuration>> for RelativeFiniteBound {
    type Error = RelativeFiniteBoundTryFromBoundError;

    fn try_from(value: Bound<SignedDuration>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(offset) => Ok(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(offset) => Ok(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => Err(RelativeFiniteBoundTryFromBoundError),
        }
    }
}

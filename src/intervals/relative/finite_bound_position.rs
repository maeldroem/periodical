//! Relative finite bound position
//!
//! A relative finite bound position has two components: an offset, represented
//! by a [`SignedDuration`], and a [bound inclusivity](BoundInclusivity).
//!
//! Relative finite bound positions are essential parts of all interval bounds, as any
//! finite bound, such as [`RelFiniteStartBound`] and [`RelFiniteEndBound`], use it to
//! represent their position.
//!
//! Therefore, since no extremality is indicated, the contained bound inclusivity is ambiguous.
//! If you need to take into account the bound inclusivity, you need the extra extremality information,
//! therefore you need to convert the [`RelFiniteBoundPos`] into a bound that can then be compared
//! using dedicated [bound comparison operations](crate::intervals::ops::bound_cmp).

use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::relative::{RelEndBound, RelFiniteEndBound, RelFiniteStartBound, RelStartBound};

/// Relative finite bound position
///
/// A relative finite bound position has two components: an offset, represented
/// by a [`SignedDuration`], and a [bound inclusivity](BoundInclusivity).
///
/// Relative finite bound positions are essential parts of all interval bounds, as any
/// finite bound, such as [`RelFiniteStartBound`] and [`RelFiniteEndBound`], use it to
/// represent their position.
///
/// Therefore, since no extremality is indicated, the contained bound inclusivity is ambiguous.
/// This is why comparison of two finite bound positions only compare their offsets.
/// If you need to take into account the bound inclusivity, you need the extra extremality information,
/// therefore you need to convert the [`RelFiniteBoundPos`] into a bound that can then be compared
/// using dedicated [bound comparison operations](crate::intervals::ops::bound_cmp).
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

    /// Creates a new [`RelFiniteBoundPos`] using the given offset and [`BoundInclusivity`]
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
    /// let offset = SignedDuration::from_hours(12);
    /// let finite_bound_pos = RelFiniteBoundPos::new(offset);
    ///
    /// assert_eq!(finite_bound_pos.offset(), offset);
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
    /// let new_offset = SignedDuration::from_hours(32);
    /// let mut finite_bound_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
    ///
    /// finite_bound_pos.set_offset(new_offset);
    ///
    /// assert_eq!(finite_bound_pos.offset(), new_offset);
    /// ```
    pub fn set_offset(&mut self, new_offset: SignedDuration) {
        self.offset = new_offset;
    }

    /// Sets the bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// # use periodical::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
    /// let mut finite_bound_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
    /// finite_bound_pos.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(finite_bound_pos.inclusivity(), BoundInclusivity::Exclusive);
    /// ```
    pub fn set_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.inclusivity = new_inclusivity;
    }

    /// Wraps `self` in a [`RelFiniteStartBound`]
    #[must_use]
    pub fn to_finite_start_bound(self) -> RelFiniteStartBound {
        RelFiniteStartBound::new(self)
    }

    /// Converts `self` into [`RelStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> RelStartBound {
        RelStartBound::from(self)
    }

    /// Wraps `self` in a [`RelFiniteEndBound`]
    #[must_use]
    pub fn to_finite_end_bound(self) -> RelFiniteEndBound {
        RelFiniteEndBound::new(self)
    }

    /// Converts `self` into [`RelEndBound`]
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

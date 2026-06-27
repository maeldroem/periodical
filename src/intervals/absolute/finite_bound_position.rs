//! Absolute finite bound position
//!
//! An absolute finite bound position has two components: an absolute time, represented
//! by a [`Timestamp`], and a [bound inclusivity](BoundInclusivity).
//!
//! Absolute finite bound positions are essential parts of all interval bounds, as any
//! finite bound, such as [`AbsFiniteStartBound`] and [`AbsFiniteEndBound`], use it to
//! represent their position.
//!
//! Therefore, since no extremality is indicated, the contained bound inclusivity is ambiguous.
//! If you need to take into account the bound inclusivity, you need the extra extremality information,
//! therefore you need to convert the [`AbsFiniteBoundPos`] into a bound that can then be compared
//! using dedicated [bound comparison operations](crate::intervals::ops::bound_cmp).

use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsEndBound, AbsFiniteEndBound, AbsFiniteStartBound, AbsStartBound};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

/// Absolute finite bound position
///
/// An absolute finite bound position has two components: an absolute time, represented
/// by a [`Timestamp`], and a [bound inclusivity](BoundInclusivity).
///
/// Absolute finite bound positions are essential parts of all interval bounds, as any
/// finite bound, such as [`AbsFiniteStartBound`] and [`AbsFiniteEndBound`], use it to
/// represent their position.
///
/// Therefore, since no extremality is indicated, the contained bound inclusivity is ambiguous.
/// This is why comparison of two finite bound positions only compare their times.
/// If you need to take into account the bound inclusivity, you need the extra extremality information,
/// therefore you need to convert the [`AbsFiniteBoundPos`] into a bound that can then be compared
/// using dedicated [bound comparison operations](crate::intervals::ops::bound_cmp).
///
/// # Examples
///
/// ## Basic use
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::AbsFiniteBoundPos;
/// let finite_bound_position =
///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Creating an [`AbsFiniteBoundPos`] with an explicit [`BoundInclusivity`]
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::AbsFiniteBoundPos;
/// # use periodical::intervals::meta::BoundInclusivity;
/// let finite_bound_position = AbsFiniteBoundPos::new_with_incl(
///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
///     BoundInclusivity::Exclusive,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsFiniteBoundPos {
    time: Timestamp,
    inclusivity: BoundInclusivity,
}

impl AbsFiniteBoundPos {
    /// Creates a new [`AbsFiniteBoundPos`] using the given time
    ///
    /// This creates a finite bound using the [default `BoundInclusivity`](BoundInclusivity::default).
    #[must_use]
    pub fn new(time: Timestamp) -> Self {
        Self::new_with_incl(time, BoundInclusivity::default())
    }

    /// Creates a new [`AbsFiniteBoundPos`] using the given time and [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_incl(time: Timestamp, inclusivity: BoundInclusivity) -> Self {
        AbsFiniteBoundPos {
            time,
            inclusivity,
        }
    }

    /// Returns the time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_bound_pos = AbsFiniteBoundPos::new(time);
    ///
    /// assert_eq!(finite_bound_pos.time(), time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn time(&self) -> Timestamp {
        self.time
    }

    /// Sets the time
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// let new_time = "2025-01-02 16:00:00Z".parse::<Timestamp>()?;
    /// let mut finite_bound_pos = AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
    ///
    /// finite_bound_pos.set_time(new_time);
    ///
    /// assert_eq!(finite_bound_pos.time(), new_time);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_time(&mut self, new_time: Timestamp) {
        self.time = new_time;
    }

    /// Sets the bound inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
    /// let mut finite_bound_pos = AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
    /// finite_bound_pos.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(finite_bound_pos.inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.inclusivity = new_inclusivity;
    }

    /// Wraps `self` in an [`AbsFiniteStartBound`]
    #[must_use]
    pub fn to_finite_start_bound(self) -> AbsFiniteStartBound {
        AbsFiniteStartBound::new(self)
    }

    /// Converts `self` into [`AbsStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> AbsStartBound {
        AbsStartBound::from(self)
    }

    /// Wraps `self` in an [`AbsFiniteEndBound`]
    #[must_use]
    pub fn to_finite_end_bound(self) -> AbsFiniteEndBound {
        AbsFiniteEndBound::new(self)
    }

    /// Converts `self` into [`AbsEndBound`]
    #[must_use]
    pub fn to_end_bound(self) -> AbsEndBound {
        AbsEndBound::from(self)
    }
}

impl HasBoundInclusivity for AbsFiniteBoundPos {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl From<Timestamp> for AbsFiniteBoundPos {
    fn from(value: Timestamp) -> Self {
        AbsFiniteBoundPos::new(value)
    }
}

impl From<(Timestamp, BoundInclusivity)> for AbsFiniteBoundPos {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        AbsFiniteBoundPos::new_with_incl(time, inclusivity)
    }
}

/// Error that can occur when trying to convert [`Bound<Timestamp>`] into [`AbsFiniteBoundPos`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsFiniteBoundPosTryFromBoundError;

impl Display for AbsFiniteBoundPosTryFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `Bound<Timestamp>` into `AbsFiniteBoundPos`"
        )
    }
}

impl Error for AbsFiniteBoundPosTryFromBoundError {}

impl TryFrom<Bound<Timestamp>> for AbsFiniteBoundPos {
    type Error = AbsFiniteBoundPosTryFromBoundError;

    fn try_from(value: Bound<Timestamp>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(time) => Ok(AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Inclusive)),
            Bound::Excluded(time) => Ok(AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive)),
            Bound::Unbounded => Err(AbsFiniteBoundPosTryFromBoundError),
        }
    }
}

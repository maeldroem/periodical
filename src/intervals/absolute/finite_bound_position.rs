//! Absolute finite bound
//!
//! An absolute finite bound has two components: an absolute time, represented
//! by a [`Timestamp`], and a [bound inclusivity](BoundInclusivity).
//!
//! Absolute finite bounds are usually converted into either an [`AbsStartBound`]
//! through the [`to_start_bound`](AbsFiniteBoundPos::to_start_bound) method,
//! or into an [`AbsEndBound`] through the [`to_end_bound`](AbsFiniteBoundPos::to_end_bound) method.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsEndBound, AbsFiniteEndBound, AbsFiniteStartBound, AbsStartBound};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

/// An absolute finite bound position
///
/// Contains a time and an ambiguous [`BoundInclusivity`]: if it is
/// [`Exclusive`](BoundInclusivity::Exclusive), then we additionally need the
/// _extremality_ (whether it acts as the start or end of an interval) in order to
/// know what this position truly encompasses.
///
/// This is why when comparing finite bound positions, only its time is compared.
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
/// let finite_bound_position = AbsFiniteBoundPos::new_with_inclusivity(
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
        Self::new_with_inclusivity(time, BoundInclusivity::default())
    }

    /// Creates a new [`AbsFiniteBoundPos`] using the given time and
    /// [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_inclusivity(time: Timestamp, inclusivity: BoundInclusivity) -> Self {
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
    /// let finite_bound_position = AbsFiniteBoundPos::new(time);
    ///
    /// assert_eq!(finite_bound_position.time(), time);
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
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let new_time = "2025-01-02 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut finite_bound_position = AbsFiniteBoundPos::new(time);
    /// finite_bound_position.set_time(new_time);
    ///
    /// assert_eq!(finite_bound_position.time(), new_time);
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
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut finite_bound_position = AbsFiniteBoundPos::new(time);
    /// finite_bound_position.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     finite_bound_position.inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.inclusivity = new_inclusivity;
    }

    #[must_use]
    pub fn to_finite_start_bound(self) -> AbsFiniteStartBound {
        AbsFiniteStartBound::new(self)
    }

    /// Wraps the finite bound in an [`AbsStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> AbsStartBound {
        AbsStartBound::from(self)
    }

    #[must_use]
    pub fn to_finite_end_bound(self) -> AbsFiniteEndBound {
        AbsFiniteEndBound::new(self)
    }

    /// Wraps the finite bound in an [`AbsEndBound`]
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

impl PartialOrd for AbsFiniteBoundPos {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsFiniteBoundPos {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time.cmp(&other.time)
    }
}

impl From<Timestamp> for AbsFiniteBoundPos {
    fn from(value: Timestamp) -> Self {
        AbsFiniteBoundPos::new(value)
    }
}

impl From<(Timestamp, BoundInclusivity)> for AbsFiniteBoundPos {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        AbsFiniteBoundPos::new_with_inclusivity(time, inclusivity)
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
            Bound::Included(time) => Ok(AbsFiniteBoundPos::new_with_inclusivity(
                time,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(time) => Ok(AbsFiniteBoundPos::new_with_inclusivity(
                time,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => Err(AbsFiniteBoundPosTryFromBoundError),
        }
    }
}

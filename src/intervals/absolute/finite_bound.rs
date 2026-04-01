//! Absolute finite bound
//!
//! An absolute finite bound has two components: an absolute time, represented
//! by a [`Timestamp`], and a [bound inclusivity](BoundInclusivity).
//!
//! Absolute finite bounds are usually converted into either an [`AbsoluteStartBound`]
//! through the [`to_start_bound`](AbsoluteFiniteBound::to_start_bound) method,
//! or into an [`AbsoluteEndBound`] through the [`to_end_bound`](AbsoluteFiniteBound::to_end_bound) method.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

/// An absolute finite bound
///
/// Contains a time and an ambiguous [`BoundInclusivity`]: if it is
/// [`Exclusive`](BoundInclusivity::Exclusive), then we additionally need the
/// _source_ (whether it acts as the start or end of an interval) in order to
/// know what this bound truly encompasses.
///
/// This is why when comparing finite bounds, only its position (for absolute
/// bounds, its time) is used.
///
/// # Examples
///
/// ## Basic use
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::AbsoluteFiniteBound;
/// let finite_bound = AbsoluteFiniteBound::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?);
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Creating an [`AbsoluteFiniteBound`] with an explicit [`BoundInclusivity`]
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::AbsoluteFiniteBound;
/// # use periodical::intervals::meta::BoundInclusivity;
/// let finite_bound = AbsoluteFiniteBound::new_with_inclusivity(
///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
///     BoundInclusivity::Exclusive,
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteFiniteBound {
    pub(crate) time: Timestamp,
    pub(crate) inclusivity: BoundInclusivity,
}

impl AbsoluteFiniteBound {
    /// Creates a new [`AbsoluteFiniteBound`] using the given time
    ///
    /// This creates a finite bound using the [default `BoundInclusivity`](BoundInclusivity::default).
    #[must_use]
    pub fn new(time: Timestamp) -> Self {
        Self::new_with_inclusivity(time, BoundInclusivity::default())
    }

    /// Creates a new [`AbsoluteFiniteBound`] using the given time and
    /// [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_inclusivity(time: Timestamp, inclusivity: BoundInclusivity) -> Self {
        AbsoluteFiniteBound {
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
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_bound = AbsoluteFiniteBound::new(time);
    ///
    /// assert_eq!(finite_bound.time(), time);
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
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let new_time = "2025-01-02 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut finite_bound = AbsoluteFiniteBound::new(time);
    /// finite_bound.set_time(new_time);
    ///
    /// assert_eq!(finite_bound.time(), new_time);
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
    /// # use periodical::intervals::absolute::AbsoluteFiniteBound;
    /// # use periodical::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let mut finite_bound = AbsoluteFiniteBound::new(time);
    /// finite_bound.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(finite_bound.inclusivity(), BoundInclusivity::Exclusive);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn set_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.inclusivity = new_inclusivity;
    }

    /// Wraps the finite bound in an [`AbsoluteStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> AbsoluteStartBound {
        AbsoluteStartBound::from(self)
    }

    /// Wraps the finite bound in an [`AbsoluteEndBound`]
    #[must_use]
    pub fn to_end_bound(self) -> AbsoluteEndBound {
        AbsoluteEndBound::from(self)
    }
}

impl HasBoundInclusivity for AbsoluteFiniteBound {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl PartialOrd for AbsoluteFiniteBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteFiniteBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time.cmp(&other.time)
    }
}

impl From<Timestamp> for AbsoluteFiniteBound {
    fn from(value: Timestamp) -> Self {
        AbsoluteFiniteBound::new(value)
    }
}

impl From<(Timestamp, BoundInclusivity)> for AbsoluteFiniteBound {
    fn from((time, inclusivity): (Timestamp, BoundInclusivity)) -> Self {
        AbsoluteFiniteBound::new_with_inclusivity(time, inclusivity)
    }
}

/// Error that can occur when trying to convert [`Bound<Timestamp>`] into [`AbsoluteFiniteBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsoluteFiniteBoundTryFromBoundError;

impl Display for AbsoluteFiniteBoundTryFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `Bound<Timestamp>` into `AbsoluteFiniteBound`"
        )
    }
}

impl Error for AbsoluteFiniteBoundTryFromBoundError {}

impl TryFrom<Bound<Timestamp>> for AbsoluteFiniteBound {
    type Error = AbsoluteFiniteBoundTryFromBoundError;

    fn try_from(value: Bound<Timestamp>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(time) => Ok(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(time) => Ok(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => Err(AbsoluteFiniteBoundTryFromBoundError),
        }
    }
}

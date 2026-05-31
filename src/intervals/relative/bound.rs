//! Relative bound representation
//!
//! Represents a relative bound regardless of its source (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving its source.

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundPartialEq, BoundPartialOrd};
use crate::intervals::relative::RelativeFiniteBound;
use crate::intervals::relative::RelativeFiniteEndBound;
use crate::intervals::relative::RelativeFiniteStartBound;
use crate::intervals::relative::{RelativeEndBound, RelativeStartBound};

/// Enum for relative start and end bounds
///
/// Represents a relative bound regardless of its source (start/end).
/// This is particularly useful for representing relative bounds of an interval
/// as a single type, while still conserving its source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelativeBound {
    Start(RelativeStartBound),
    End(RelativeEndBound),
}

impl RelativeBound {
    /// Returns whether it is of the [`Start`](RelativeBound::Start) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert!(start.is_start());
    /// assert!(!end.is_start());
    /// ```
    #[must_use]
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    /// Returns whether it is of the [`End`](RelativeBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert!(end.is_end());
    /// assert!(!start.is_end());
    /// ```
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    /// Returns the content of the [`Start`](RelativeBound::Start) variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Start`](RelativeBound::Start) variant in an [`Option`]. If instead
    /// `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     start.start(),
    ///     Some(RelativeFiniteBoundPosition::new(start_offset).to_start_bound()),
    /// );
    /// assert_eq!(end.start(), None,);
    /// ```
    #[must_use]
    pub fn start(self) -> Option<RelativeStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](RelativeBound::End) variant
    ///
    /// Consumes `self` and puts the content of the [`End`](RelativeBound::End)
    /// variant in an [`Option`]. If instead `self` is another variant, the
    /// method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBoundPosition};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBoundPosition::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBoundPosition::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     end.end(),
    ///     Some(RelativeFiniteBoundPosition::new(end_offset).to_end_bound()),
    /// );
    /// assert_eq!(start.end(), None,);
    /// ```
    #[must_use]
    pub fn end(self) -> Option<RelativeEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the opposite bound type with the opposite inclusivity
    ///
    /// Simply use [`RelativeStartBound::opposite`] for start bounds,
    /// and [`RelativeEndBound::opposite`] for end bounds, and then wraps the
    /// result in [`RelativeBound`].
    ///
    /// If the bound is infinite, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelativeBound;
    /// # let bounds: [RelativeBound; 0] = [];
    /// struct BoundChange {
    ///     new_bound: RelativeBound,
    ///     before_new_bound: Option<RelativeBound>,
    /// }
    ///
    /// bounds.into_iter().map(|bound| BoundChange {
    ///     new_bound: bound,
    ///     before_new_bound: bound.opposite(),
    /// });
    /// ```
    ///
    /// A similar process is used in
    /// [`LayeredRelativeBounds`](crate::iter::intervals::layered_bounds::LayeredRelativeBounds).
    #[must_use]
    pub fn opposite(&self) -> Option<Self> {
        match self {
            Self::Start(start) => start.opposite().map(Self::End),
            Self::End(end) => end.opposite().map(Self::Start),
        }
    }
}

impl HasBoundExtremality for RelativeBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundPartialEq for RelativeBound {
    fn bound_eq(&self, other: &Self) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundEq for RelativeBound {}

impl BoundPartialEq<RelativeFiniteStartBound> for RelativeBound {
    fn bound_eq(&self, other: &RelativeFiniteStartBound) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeFiniteEndBound> for RelativeBound {
    fn bound_eq(&self, other: &RelativeFiniteEndBound) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeFiniteBound> for RelativeBound {
    fn bound_eq(&self, other: &RelativeFiniteBound) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeStartBound> for RelativeBound {
    fn bound_eq(&self, other: &RelativeStartBound) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundPartialEq<RelativeEndBound> for RelativeBound {
    fn bound_eq(&self, other: &RelativeEndBound) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other),
            Self::End(end) => end.bound_eq(other),
        }
    }
}

impl BoundPartialOrd for RelativeBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for RelativeBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::Start(lhs_start), Self::Start(rhs_start)) => lhs_start.bound_cmp(rhs_start),
            (Self::Start(start), Self::End(end)) => {
                // Comparison between start and end is not supposed to fail,
                // `BoundOrdering::Equal(None)` is a safe fallback
                start.bound_partial_cmp(end).unwrap_or(BoundOrdering::Equal(None))
            },
            (Self::End(end), Self::Start(start)) => {
                // Comparison between start and end is not supposed to fail,
                // `BoundOrdering::Equal(None)` is a safe fallback
                end.bound_partial_cmp(start).unwrap_or(BoundOrdering::Equal(None))
            },
            (Self::End(lhs_end), Self::End(rhs_end)) => lhs_end.bound_cmp(rhs_end),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteStartBound> for RelativeBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(start) => start.bound_partial_cmp(other),
            Self::End(end) => end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteEndBound> for RelativeBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(start) => start.bound_partial_cmp(other),
            Self::End(end) => end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteBound> for RelativeBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(start) => start.bound_partial_cmp(other),
            Self::End(end) => end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeStartBound> for RelativeBound {
    fn bound_partial_cmp(&self, other: &RelativeStartBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(start) => start.bound_partial_cmp(other),
            Self::End(end) => end.bound_partial_cmp(other),
        }
    }
}

impl BoundPartialOrd<RelativeEndBound> for RelativeBound {
    fn bound_partial_cmp(&self, other: &RelativeEndBound) -> Option<BoundOrdering> {
        match self {
            Self::Start(start) => start.bound_partial_cmp(other),
            Self::End(end) => end.bound_partial_cmp(other),
        }
    }
}

impl From<RelativeFiniteStartBound> for RelativeBound {
    fn from(value: RelativeFiniteStartBound) -> Self {
        Self::Start(RelativeStartBound::from(value))
    }
}

impl From<RelativeFiniteEndBound> for RelativeBound {
    fn from(value: RelativeFiniteEndBound) -> Self {
        Self::End(RelativeEndBound::from(value))
    }
}

impl From<RelativeStartBound> for RelativeBound {
    fn from(value: RelativeStartBound) -> Self {
        RelativeBound::Start(value)
    }
}

impl From<RelativeEndBound> for RelativeBound {
    fn from(value: RelativeEndBound) -> Self {
        RelativeBound::End(value)
    }
}

impl From<RelativeFiniteBound> for RelativeBound {
    fn from(value: RelativeFiniteBound) -> Self {
        match value {
            RelativeFiniteBound::Start(finite_start) => Self::Start(RelativeStartBound::from(finite_start)),
            RelativeFiniteBound::End(finite_end) => Self::End(RelativeEndBound::from(finite_end)),
        }
    }
}

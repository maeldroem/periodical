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
use crate::intervals::relative::finite_bound::RelativeFiniteBound;
use crate::intervals::relative::finite_end_bound::RelativeFiniteEndBound;
use crate::intervals::relative::finite_start_bound::RelativeFiniteStartBound;
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

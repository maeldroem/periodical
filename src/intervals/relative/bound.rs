//! Relative bound representation
//!
//! Represents a relative bound regardless of its source (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving its source.

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};

/// Enum for relative start and end bounds
///
/// Represents a relative bound regardless of its source (start/end).
/// This is particularly useful for representing relative bounds of an interval
/// as a single type, while still conserving its source.
#[derive(Debug, Clone, Copy)]
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
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBound};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBound::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBound::new(end_offset)
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
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBound};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBound::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBound::new(end_offset)
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
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBound};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBound::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBound::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     start.start(),
    ///     Some(RelativeFiniteBound::new(start_offset).to_start_bound()),
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
    /// # use periodical::intervals::relative::{RelativeBound, RelativeFiniteBound};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelativeFiniteBound::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelativeFiniteBound::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     end.end(),
    ///     Some(RelativeFiniteBound::new(end_offset).to_end_bound()),
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

impl PartialEq for RelativeBound {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RelativeBound::Start(og_start), RelativeBound::Start(other_start)) => og_start.eq(other_start),
            (RelativeBound::End(og_end), RelativeBound::End(other_end)) => og_end.eq(other_end),
            (RelativeBound::Start(start), RelativeBound::End(end))
            | (RelativeBound::End(end), RelativeBound::Start(start)) => start.eq(end),
        }
    }
}

impl Eq for RelativeBound {}

impl PartialOrd for RelativeBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (RelativeBound::Start(og_start), RelativeBound::Start(other_start)) => og_start.cmp(other_start),
            (RelativeBound::End(og_end), RelativeBound::End(other_end)) => og_end.cmp(other_end),
            (RelativeBound::Start(og_start), RelativeBound::End(other_end)) => {
                // Partial ordering between two different bounds should not fail, but we provide
                // a default just in case
                og_start.partial_cmp(other_end).unwrap_or(Ordering::Equal)
            },
            (RelativeBound::End(og_end), RelativeBound::Start(other_start)) => {
                // Partial ordering between two different bounds should not fail, but we provide
                // a default just in case
                og_end.partial_cmp(other_start).unwrap_or(Ordering::Equal)
            },
        }
    }
}

impl Hash for RelativeBound {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Start(RelativeStartBound::InfinitePast) => {
                RelativeStartBound::InfinitePast.hash(state);
            },
            Self::Start(RelativeStartBound::Finite(finite)) | Self::End(RelativeEndBound::Finite(finite)) => {
                finite.hash(state);
            },
            Self::End(RelativeEndBound::InfiniteFuture) => {
                RelativeEndBound::InfiniteFuture.hash(state);
            },
        }
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

impl From<(RelativeFiniteBound, BoundExtremality)> for RelativeBound {
    fn from((bound, extremality): (RelativeFiniteBound, BoundExtremality)) -> Self {
        match extremality {
            BoundExtremality::Start => Self::from(bound.to_start_bound()),
            BoundExtremality::End => Self::from(bound.to_end_bound()),
        }
    }
}

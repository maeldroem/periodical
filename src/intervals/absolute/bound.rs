//! Absolute bound representation
//! 
//! Represents an absolute bound regardless of its source (start/end).
//! This is particularly useful for representing absolute bounds of an interval as a single type,
//! while still conserving its source.

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteStartBound};


/// Enum for absolute start and end bounds
///
/// Represents an absolute bound regardless of its source (start/end).
/// This is particularly useful for representing absolute bounds of an interval as a single type,
/// while still conserving its source.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsoluteBound {
    Start(AbsoluteStartBound),
    End(AbsoluteEndBound),
}

impl AbsoluteBound {
    /// Returns whether it is of the [`Start`](AbsoluteBound::Start) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBound};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteFiniteBound::new(start_time).to_start_bound()
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteFiniteBound::new(end_time).to_end_bound()
    /// );
    ///
    /// assert!(start.is_start());
    /// assert!(!end.is_start());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    /// Returns whether it is of the [`End`](AbsoluteBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBound};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteFiniteBound::new(start_time).to_start_bound()
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteFiniteBound::new(end_time).to_end_bound()
    /// );
    ///
    /// assert!(end.is_end());
    /// assert!(!start.is_end());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    /// Returns the content of the [`Start`](AbsoluteBound::Start) variant
    ///
    /// Consumes `self` and puts the content of the [`Start`](AbsoluteBound::Start) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteFiniteBound::new(start_time).to_start_bound()
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteFiniteBound::new(end_time).to_end_bound()
    /// );
    ///
    /// assert_eq!(
    ///     start.start(),
    ///     Some(AbsoluteFiniteBound::new(start_time).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     end.start(),
    ///     None,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start(self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](AbsoluteBound::End) variant
    ///
    /// Consumes `self` and puts the content of the [`End`](AbsoluteBound::End) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteBound::Start(
    ///     AbsoluteFiniteBound::new(start_time).to_start_bound()
    /// );
    /// let end = AbsoluteBound::End(
    ///     AbsoluteFiniteBound::new(end_time).to_end_bound()
    /// );
    ///
    /// assert_eq!(
    ///     end.end(),
    ///     Some(AbsoluteFiniteBound::new(end_time).to_end_bound()),
    /// );
    /// assert_eq!(
    ///     start.end(),
    ///     None,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the opposite bound type with the opposite inclusivity
    ///
    /// Simply use [`AbsoluteStartBound::opposite`] for start bounds,
    /// and [`AbsoluteEndBound::opposite`] for end bounds, and then wraps the result in [`AbsoluteBound`].
    ///
    /// If the bound is infinite, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteBound;
    /// # let bounds: [AbsoluteBound; 0] = [];
    /// struct BoundChange {
    ///     new_bound: AbsoluteBound,
    ///     before_new_bound: Option<AbsoluteBound>,
    /// }
    ///
    /// bounds.into_iter().map(|bound| BoundChange {
    ///     new_bound: bound,
    ///     before_new_bound: bound.opposite(),
    /// });
    /// ```
    ///
    /// A similar process is used in
    /// [`LayeredAbsoluteBounds`](crate::iter::intervals::layered_bounds::LayeredAbsoluteBounds).
    #[must_use]
    pub fn opposite(&self) -> Option<Self> {
        match self {
            Self::Start(start) => start.opposite().map(Self::End),
            Self::End(end) => end.opposite().map(Self::Start),
        }
    }
}

impl PartialEq for AbsoluteBound {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AbsoluteBound::Start(og_start), AbsoluteBound::Start(other_start)) => og_start.eq(other_start),
            (AbsoluteBound::End(og_end), AbsoluteBound::End(other_end)) => og_end.eq(other_end),
            (AbsoluteBound::Start(start), AbsoluteBound::End(end))
            | (AbsoluteBound::End(end), AbsoluteBound::Start(start)) => start.eq(end),
        }
    }
}

impl Eq for AbsoluteBound {}

impl PartialOrd for AbsoluteBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (AbsoluteBound::Start(og_start), AbsoluteBound::Start(other_start)) => og_start.cmp(other_start),
            (AbsoluteBound::End(og_end), AbsoluteBound::End(other_end)) => og_end.cmp(other_end),
            (AbsoluteBound::Start(og_start), AbsoluteBound::End(other_end)) => {
                // Partial ordering between two different bounds should not fail, but we provide a default just in case
                og_start.partial_cmp(other_end).unwrap_or(Ordering::Equal)
            },
            (AbsoluteBound::End(og_end), AbsoluteBound::Start(other_start)) => {
                // Partial ordering between two different bounds should not fail, but we provide a default just in case
                og_end.partial_cmp(other_start).unwrap_or(Ordering::Equal)
            },
        }
    }
}

impl Hash for AbsoluteBound {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Start(AbsoluteStartBound::InfinitePast) => {
                AbsoluteStartBound::InfinitePast.hash(state);
            },
            Self::Start(AbsoluteStartBound::Finite(finite)) | Self::End(AbsoluteEndBound::Finite(finite)) => {
                finite.hash(state);
            },
            Self::End(AbsoluteEndBound::InfiniteFuture) => {
                AbsoluteEndBound::InfiniteFuture.hash(state);
            },
        }
    }
}

impl From<AbsoluteStartBound> for AbsoluteBound {
    fn from(value: AbsoluteStartBound) -> Self {
        AbsoluteBound::Start(value)
    }
}

impl From<AbsoluteEndBound> for AbsoluteBound {
    fn from(value: AbsoluteEndBound) -> Self {
        AbsoluteBound::End(value)
    }
}

//! Absolute bound representation
//!
//! Represents an absolute bound regardless of its extremality (start/end).
//! This is particularly useful for representing absolute bounds of an interval
//! as a single type, while still conserving their extremalities.

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteFiniteEndBound,
    AbsoluteFiniteStartBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};

/// Absolute start/end bound
///
/// Represents an absolute bound regardless of its extremality (start/end).
/// This is particularly useful for representing absolute bounds of an interval
/// as a single type, while still conserving their extremalities.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    /// # use periodical::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time)
    ///     .to_end_bound()
    ///     .to_bound();
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
    /// # use periodical::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBoundPosition};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time)
    ///     .to_end_bound()
    ///     .to_bound();
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
    /// Consumes `self` and puts the content of the
    /// [`Start`](AbsoluteBound::Start) variant in an [`Option`]. If instead
    /// `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     start.start(),
    ///     Some(AbsoluteFiniteBoundPosition::new(start_time).to_start_bound()),
    /// );
    /// assert_eq!(end.start(), None);
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
    /// Consumes `self` and puts the content of the [`End`](AbsoluteBound::End)
    /// variant in an [`Option`]. If instead `self` is another variant, the
    /// method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteFiniteBoundPosition::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsoluteFiniteBoundPosition::new(end_time)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     end.end(),
    ///     Some(AbsoluteFiniteBoundPosition::new(end_time).to_end_bound()),
    /// );
    /// assert_eq!(start.end(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the opposite bound type with opposite inclusivity
    ///
    /// Simply uses [`AbsoluteStartBound::opposite`] for start bounds,
    /// and [`AbsoluteEndBound::opposite`] for end bounds, and then wraps the
    /// result in [`AbsoluteBound`].
    ///
    /// Returns [`None`] if the bound is infinite.
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
    pub fn opposite(self) -> Option<Self> {
        match self {
            Self::Start(start) => start.opposite().map(Self::End),
            Self::End(end) => end.opposite().map(Self::Start),
        }
    }
}

impl HasBoundExtremality for AbsoluteBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for AbsoluteBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteFiniteStartBound> for AbsoluteBound {
    fn bound_eq(&self, other: &AbsoluteFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteFiniteEndBound> for AbsoluteBound {
    fn bound_eq(&self, other: &AbsoluteFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteFiniteBound> for AbsoluteBound {
    fn bound_eq(&self, other: &AbsoluteFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteStartBound> for AbsoluteBound {
    fn bound_eq(&self, other: &AbsoluteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsoluteEndBound> for AbsoluteBound {
    fn bound_eq(&self, other: &AbsoluteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for AbsoluteBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::Start(lhs_start), Self::Start(rhs_start)) => lhs_start.bound_cmp(rhs_start),
            (Self::Start(start), Self::End(end)) => start.bound_cmp(end),
            (Self::End(end), Self::Start(start)) => end.bound_cmp(start),
            (Self::End(lhs_end), Self::End(rhs_end)) => lhs_end.bound_cmp(rhs_end),
        }
    }
}

impl BoundOrdExtremaOps for AbsoluteBound {}

impl BoundOrd<AbsoluteFiniteStartBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteFiniteEndBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteFiniteBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteStartBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsoluteEndBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl From<AbsoluteFiniteStartBound> for AbsoluteBound {
    fn from(value: AbsoluteFiniteStartBound) -> Self {
        Self::Start(AbsoluteStartBound::from(value))
    }
}

impl From<AbsoluteFiniteEndBound> for AbsoluteBound {
    fn from(value: AbsoluteFiniteEndBound) -> Self {
        Self::End(AbsoluteEndBound::from(value))
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

impl From<AbsoluteFiniteBound> for AbsoluteBound {
    fn from(value: AbsoluteFiniteBound) -> Self {
        match value {
            AbsoluteFiniteBound::Start(finite_start) => Self::Start(AbsoluteStartBound::from(finite_start)),
            AbsoluteFiniteBound::End(finite_end) => Self::End(AbsoluteEndBound::from(finite_end)),
        }
    }
}

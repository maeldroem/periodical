//! Absolute bound representation
//!
//! Represents an absolute bound regardless of its extremality (start/end).
//! This is particularly useful for representing absolute bounds of an interval
//! as a single type, while still conserving their extremalities.

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsEndBound, AbsFiniteBound, AbsFiniteEndBound, AbsFiniteStartBound, AbsStartBound};
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
pub enum AbsBound {
    Start(AbsStartBound),
    End(AbsEndBound),
}

impl AbsBound {
    /// Returns whether it is of the [`Start`](AbsBound::Start) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsBound, AbsFiniteBoundPos};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsFiniteBoundPos::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsFiniteBoundPos::new(end_time).to_end_bound().to_bound();
    ///
    /// assert!(start.is_start());
    /// assert!(!end.is_start());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    /// Returns whether it is of the [`End`](AbsBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsBound, AbsFiniteBoundPos};
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsFiniteBoundPos::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsFiniteBoundPos::new(end_time).to_end_bound().to_bound();
    ///
    /// assert!(end.is_end());
    /// assert!(!start.is_end());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    /// Returns the content of the [`Start`](AbsBound::Start) variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Start`](AbsBound::Start) variant in an [`Option`]. If instead
    /// `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsBound, AbsEndBound, AbsFiniteBoundPos, AbsStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsFiniteBoundPos::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsFiniteBoundPos::new(end_time).to_end_bound().to_bound();
    ///
    /// assert_eq!(
    ///     start.start(),
    ///     Some(AbsFiniteBoundPos::new(start_time).to_start_bound()),
    /// );
    /// assert_eq!(end.start(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start(self) -> Option<AbsStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](AbsBound::End) variant
    ///
    /// Consumes `self` and puts the content of the [`End`](AbsBound::End)
    /// variant in an [`Option`]. If instead `self` is another variant, the
    /// method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsBound, AbsEndBound, AbsFiniteBoundPos, AbsStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsFiniteBoundPos::new(start_time)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = AbsFiniteBoundPos::new(end_time).to_end_bound().to_bound();
    ///
    /// assert_eq!(
    ///     end.end(),
    ///     Some(AbsFiniteBoundPos::new(end_time).to_end_bound()),
    /// );
    /// assert_eq!(start.end(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(self) -> Option<AbsEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the opposite bound type with opposite inclusivity
    ///
    /// Simply uses [`AbsStartBound::opposite`] for start bounds,
    /// and [`AbsEndBound::opposite`] for end bounds, and then wraps the
    /// result in [`AbsBound`].
    ///
    /// Returns [`None`] if the bound is infinite.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsBound;
    /// # let bounds: [AbsBound; 0] = [];
    /// struct BoundChange {
    ///     new_bound: AbsBound,
    ///     before_new_bound: Option<AbsBound>,
    /// }
    ///
    /// bounds.into_iter().map(|bound| BoundChange {
    ///     new_bound: bound,
    ///     before_new_bound: bound.opposite(),
    /// });
    /// ```
    ///
    /// A similar process is used in
    /// [`LayeredAbsBounds`](crate::iter::intervals::layered_bounds::LayeredAbsBounds).
    #[must_use]
    pub fn opposite(self) -> Option<Self> {
        match self {
            Self::Start(start) => start.opposite().map(Self::End),
            Self::End(end) => end.opposite().map(Self::Start),
        }
    }
}

impl HasBoundExtremality for AbsBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for AbsBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsFiniteStartBound> for AbsBound {
    fn bound_eq(&self, other: &AbsFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsFiniteEndBound> for AbsBound {
    fn bound_eq(&self, other: &AbsFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsFiniteBound> for AbsBound {
    fn bound_eq(&self, other: &AbsFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsStartBound> for AbsBound {
    fn bound_eq(&self, other: &AbsStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsEndBound> for AbsBound {
    fn bound_eq(&self, other: &AbsEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for AbsBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::Start(lhs_start), Self::Start(rhs_start)) => lhs_start.bound_cmp(rhs_start),
            (Self::Start(start), Self::End(end)) => start.bound_cmp(end),
            (Self::End(end), Self::Start(start)) => end.bound_cmp(start),
            (Self::End(lhs_end), Self::End(rhs_end)) => lhs_end.bound_cmp(rhs_end),
        }
    }
}

impl BoundOrdExtremaOps for AbsBound {}

impl BoundOrd<AbsFiniteStartBound> for AbsBound {
    fn bound_cmp(&self, other: &AbsFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsFiniteEndBound> for AbsBound {
    fn bound_cmp(&self, other: &AbsFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsFiniteBound> for AbsBound {
    fn bound_cmp(&self, other: &AbsFiniteBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsStartBound> for AbsBound {
    fn bound_cmp(&self, other: &AbsStartBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsEndBound> for AbsBound {
    fn bound_cmp(&self, other: &AbsEndBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl From<AbsFiniteStartBound> for AbsBound {
    fn from(value: AbsFiniteStartBound) -> Self {
        Self::Start(AbsStartBound::from(value))
    }
}

impl From<AbsFiniteEndBound> for AbsBound {
    fn from(value: AbsFiniteEndBound) -> Self {
        Self::End(AbsEndBound::from(value))
    }
}

impl From<AbsStartBound> for AbsBound {
    fn from(value: AbsStartBound) -> Self {
        AbsBound::Start(value)
    }
}

impl From<AbsEndBound> for AbsBound {
    fn from(value: AbsEndBound) -> Self {
        AbsBound::End(value)
    }
}

impl From<AbsFiniteBound> for AbsBound {
    fn from(value: AbsFiniteBound) -> Self {
        match value {
            AbsFiniteBound::Start(finite_start) => Self::Start(AbsStartBound::from(finite_start)),
            AbsFiniteBound::End(finite_end) => Self::End(AbsEndBound::from(finite_end)),
        }
    }
}

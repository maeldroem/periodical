//! Relative bound representation
//!
//! Represents a relative bound regardless of its extremality (start/end).
//! This is particularly useful for representing relative bounds of an interval
//! as a single type, while still conserving their extremalities.

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{RelEndBound, RelFiniteBound, RelFiniteEndBound, RelFiniteStartBound, RelStartBound};

/// Relative start/end bound
///
/// Represents a relative bound regardless of its extremality (start/end).
/// This is particularly useful for representing relative bounds of an interval
/// as a single type, while still conserving their extremalities.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelBound {
    Start(RelStartBound),
    End(RelEndBound),
}

impl RelBound {
    /// Returns whether it is of the [`Start`](RelBound::Start) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBound, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelFiniteBoundPos::new(end_offset)
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

    /// Returns whether it is of the [`End`](RelBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBound, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelFiniteBoundPos::new(end_offset)
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

    /// Returns the content of the [`Start`](RelBound::Start) variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Start`](RelBound::Start) variant in an [`Option`]. If instead
    /// `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBound, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelFiniteBoundPos::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     start.start(),
    ///     Some(RelFiniteBoundPos::new(start_offset).to_start_bound()),
    /// );
    /// assert_eq!(end.start(), None);
    /// ```
    #[must_use]
    pub fn start(self) -> Option<RelStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](RelBound::End) variant
    ///
    /// Consumes `self` and puts the content of the [`End`](RelBound::End)
    /// variant in an [`Option`]. If instead `self` is another variant, the
    /// method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelBound, RelFiniteBoundPos};
    /// let start_offset = SignedDuration::from_hours(8);
    /// let end_offset = SignedDuration::from_hours(16);
    ///
    /// let start = RelFiniteBoundPos::new(start_offset)
    ///     .to_start_bound()
    ///     .to_bound();
    /// let end = RelFiniteBoundPos::new(end_offset)
    ///     .to_end_bound()
    ///     .to_bound();
    ///
    /// assert_eq!(
    ///     end.end(),
    ///     Some(RelFiniteBoundPos::new(end_offset).to_end_bound()),
    /// );
    /// assert_eq!(start.end(), None);
    /// ```
    #[must_use]
    pub fn end(self) -> Option<RelEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the opposite bound type with opposite inclusivity
    ///
    /// Simply uses [`RelStartBound::opposite`] for start bounds,
    /// and [`RelEndBound::opposite`] for end bounds, and then wraps the
    /// result in [`RelBound`].
    ///
    /// Returns [`None`] if the bound is infinite.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelBound;
    /// # let bounds: [RelBound; 0] = [];
    /// struct BoundChange {
    ///     new_bound: RelBound,
    ///     before_new_bound: Option<RelBound>,
    /// }
    ///
    /// bounds.into_iter().map(|bound| BoundChange {
    ///     new_bound: bound,
    ///     before_new_bound: bound.opposite(),
    /// });
    /// ```
    ///
    /// A similar process is used in
    /// [`LayeredRelBounds`](crate::iter::intervals::layered_bounds::LayeredRelBounds).
    #[must_use]
    pub fn opposite(&self) -> Option<Self> {
        match self {
            Self::Start(start) => start.opposite().map(Self::End),
            Self::End(end) => end.opposite().map(Self::Start),
        }
    }
}

impl HasBoundExtremality for RelBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for RelBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelFiniteStartBound> for RelBound {
    fn bound_eq(&self, other: &RelFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelFiniteEndBound> for RelBound {
    fn bound_eq(&self, other: &RelFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelFiniteBound> for RelBound {
    fn bound_eq(&self, other: &RelFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelStartBound> for RelBound {
    fn bound_eq(&self, other: &RelStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelEndBound> for RelBound {
    fn bound_eq(&self, other: &RelEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for RelBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::Start(lhs_start), Self::Start(rhs_start)) => lhs_start.bound_cmp(rhs_start),
            (Self::Start(start), Self::End(end)) => start.bound_cmp(end),
            (Self::End(end), Self::Start(start)) => end.bound_cmp(start),
            (Self::End(lhs_end), Self::End(rhs_end)) => lhs_end.bound_cmp(rhs_end),
        }
    }
}

impl BoundOrdExtremaOps for RelBound {}

impl BoundOrd<RelFiniteStartBound> for RelBound {
    fn bound_cmp(&self, other: &RelFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelFiniteEndBound> for RelBound {
    fn bound_cmp(&self, other: &RelFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelFiniteBound> for RelBound {
    fn bound_cmp(&self, other: &RelFiniteBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelStartBound> for RelBound {
    fn bound_cmp(&self, other: &RelStartBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelEndBound> for RelBound {
    fn bound_cmp(&self, other: &RelEndBound) -> BoundOrdering {
        match self {
            Self::Start(start) => start.bound_cmp(other),
            Self::End(end) => end.bound_cmp(other),
        }
    }
}

impl From<RelFiniteStartBound> for RelBound {
    fn from(value: RelFiniteStartBound) -> Self {
        Self::Start(RelStartBound::from(value))
    }
}

impl From<RelFiniteEndBound> for RelBound {
    fn from(value: RelFiniteEndBound) -> Self {
        Self::End(RelEndBound::from(value))
    }
}

impl From<RelStartBound> for RelBound {
    fn from(value: RelStartBound) -> Self {
        RelBound::Start(value)
    }
}

impl From<RelEndBound> for RelBound {
    fn from(value: RelEndBound) -> Self {
        RelBound::End(value)
    }
}

impl From<RelFiniteBound> for RelBound {
    fn from(value: RelFiniteBound) -> Self {
        match value {
            RelFiniteBound::Start(finite_start) => Self::Start(RelStartBound::from(finite_start)),
            RelFiniteBound::End(finite_end) => Self::End(RelEndBound::from(finite_end)),
        }
    }
}

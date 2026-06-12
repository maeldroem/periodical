//! Relative finite bound
//!
//! Represents an relative finite bound regardless of its extremality.
//! This is particularly useful for representing finite relative bounds of an interval
//! as a single type, while still conserving their extremalities.

use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    RelBound,
    RelEndBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelFiniteStartBound,
    RelStartBound,
};

/// Relative finite bound
///
/// Represents an relative finite bound regardless of its extremality.
/// This is particularly useful for representing finite relative bounds of an interval
/// as a single type, while still conserving their extremalities.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelFiniteBound {
    Start(RelFiniteStartBound),
    End(RelFiniteEndBound),
}

impl RelFiniteBound {
    /// Returns whether it is of the [`End`](RelFiniteBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// let finite_bound_start = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    /// let finite_bound_end = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
    ///     .to_finite_end_bound()
    ///     .to_finite_bound();
    ///
    /// assert!(finite_bound_start.is_start());
    /// assert!(!finite_bound_end.is_start());
    /// ```
    #[must_use]
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    /// Returns whether it is of the [`End`](RelFiniteBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// let finite_bound_start = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    /// let finite_bound_end = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
    ///     .to_finite_end_bound()
    ///     .to_finite_bound();
    ///
    /// assert!(!finite_bound_start.is_end());
    /// assert!(finite_bound_end.is_end());
    /// ```
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    /// Returns the content of the [`Start`](RelFiniteBound::Start) variant
    ///
    /// Consumes `self` and puts the content of the [`Start`](RelFiniteBound::Start) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// let finite_start_bound =
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
    /// let finite_bound_start = finite_start_bound.to_finite_bound();
    /// let finite_bound_end = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
    ///     .to_finite_end_bound()
    ///     .to_finite_bound();
    ///
    /// assert_eq!(finite_bound_start.start(), Some(finite_start_bound));
    /// assert_eq!(finite_bound_end.start(), None);
    /// ```
    #[must_use]
    pub fn start(self) -> Option<RelFiniteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](RelFiniteBound::End) variant
    ///
    /// Consumes `self` and puts the content of the [`End`](RelFiniteBound::End) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// let finite_bound_start = RelFiniteBoundPos::new(SignedDuration::from_hours(2))
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    /// let finite_end_bound =
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
    /// let finite_bound_end = finite_end_bound.to_finite_bound();
    ///
    /// assert_eq!(finite_bound_start.end(), None);
    /// assert_eq!(finite_bound_end.end(), Some(finite_end_bound));
    /// ```
    #[must_use]
    pub fn end(self) -> Option<RelFiniteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the finite bound position
    #[must_use]
    pub fn pos(self) -> RelFiniteBoundPos {
        match self {
            Self::Start(start) => start.pos(),
            Self::End(end) => end.pos(),
        }
    }

    /// Returns the opposite finite bound
    ///
    /// Returns a finite bound of opposite extremality and bound inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::RelFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(10);
    /// let start = RelFiniteBoundPos::new(offset)
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    ///
    /// assert_eq!(
    ///     start.opposite(),
    ///     RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive)
    ///         .to_finite_end_bound()
    ///         .to_finite_bound()
    /// );
    /// ```
    #[must_use]
    pub fn opposite(self) -> Self {
        match self {
            Self::Start(start) => Self::End(start.opposite()),
            Self::End(end) => Self::Start(end.opposite()),
        }
    }

    /// Converts `self` into [`RelBound`]
    #[must_use]
    pub fn to_bound(self) -> RelBound {
        RelBound::from(self)
    }
}

impl HasBoundExtremality for RelFiniteBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for RelFiniteBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelFiniteStartBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelFiniteEndBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelStartBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelEndBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<RelBound> for RelFiniteBound {
    fn bound_eq(&self, other: &RelBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for RelFiniteBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::Start(lhs_finite_start), Self::Start(rhs_finite_start)) => {
                lhs_finite_start.bound_cmp(rhs_finite_start)
            },
            (Self::Start(finite_start), Self::End(finite_end)) => finite_start.bound_cmp(finite_end),
            (Self::End(finite_end), Self::Start(finite_start)) => finite_end.bound_cmp(finite_start),
            (Self::End(lhs_finite_end), Self::End(rhs_finite_end)) => lhs_finite_end.bound_cmp(rhs_finite_end),
        }
    }
}

impl BoundOrdExtremaOps for RelFiniteBound {}

impl BoundOrd<RelFiniteStartBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelFiniteEndBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelStartBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelEndBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<RelBound> for RelFiniteBound {
    fn bound_cmp(&self, other: &RelBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl From<RelFiniteStartBound> for RelFiniteBound {
    fn from(value: RelFiniteStartBound) -> Self {
        Self::Start(value)
    }
}

impl From<RelFiniteEndBound> for RelFiniteBound {
    fn from(value: RelFiniteEndBound) -> Self {
        Self::End(value)
    }
}

impl From<(RelFiniteBoundPos, BoundExtremality)> for RelFiniteBound {
    fn from((finite_pos, extremality): (RelFiniteBoundPos, BoundExtremality)) -> Self {
        match extremality {
            BoundExtremality::Start => Self::Start(RelFiniteStartBound::from(finite_pos)),
            BoundExtremality::End => Self::End(RelFiniteEndBound::from(finite_pos)),
        }
    }
}

//! Absolute finite bound
//!
//! Represents an absolute finite bound regardless of its extremality.
//! This is particularly useful for representing finite absolute bounds of an interval
//! as a single type, while still conserving their extremalities.

use crate::intervals::absolute::{
    AbsBound,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
    AbsStartBound,
};
use crate::intervals::meta::{BoundExtremality, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};

/// Absolute finite bound
///
/// Represents an absolute finite bound regardless of its extremality.
/// This is particularly useful for representing finite absolute bounds of an interval
/// as a single type, while still conserving their extremalities.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbsFiniteBound {
    Start(AbsFiniteStartBound),
    End(AbsFiniteEndBound),
}

impl AbsFiniteBound {
    /// Returns whether it is of the [`Start`](AbsFiniteBound::Start) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// let finite_bound_start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    /// let finite_bound_end = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_end_bound()
    ///     .to_finite_bound();
    ///
    /// assert!(finite_bound_start.is_start());
    /// assert!(!finite_bound_end.is_start());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_start(&self) -> bool {
        matches!(self, Self::Start(_))
    }

    /// Returns whether it is of the [`End`](AbsFiniteBound::End) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// let finite_bound_start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    /// let finite_bound_end = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_end_bound()
    ///     .to_finite_bound();
    ///
    /// assert!(!finite_bound_start.is_end());
    /// assert!(finite_bound_end.is_end());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End(_))
    }

    /// Returns the content of the [`Start`](AbsFiniteBound::Start) variant
    ///
    /// Consumes `self` and puts the content of the [`Start`](AbsFiniteBound::Start) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// let finite_start_bound = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let finite_bound_start = finite_start_bound.to_finite_bound();
    /// let finite_bound_end = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_end_bound()
    ///     .to_finite_bound();
    ///
    /// assert_eq!(finite_bound_start.start(), Some(finite_start_bound));
    /// assert_eq!(finite_bound_end.start(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn start(self) -> Option<AbsFiniteStartBound> {
        match self {
            Self::Start(start) => Some(start),
            Self::End(_) => None,
        }
    }

    /// Returns the content of the [`End`](AbsFiniteBound::End) variant
    ///
    /// Consumes `self` and puts the content of the [`End`](AbsFiniteBound::End) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// let finite_bound_start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    /// let finite_end_bound =
    ///     AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
    /// let finite_bound_end = finite_end_bound.to_finite_bound();
    ///
    /// assert_eq!(finite_bound_start.end(), None);
    /// assert_eq!(finite_bound_end.end(), Some(finite_end_bound));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn end(self) -> Option<AbsFiniteEndBound> {
        match self {
            Self::Start(_) => None,
            Self::End(end) => Some(end),
        }
    }

    /// Returns the finite bound position
    #[must_use]
    pub fn pos(self) -> AbsFiniteBoundPos {
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
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    /// let start = AbsFiniteBoundPos::new(time)
    ///     .to_finite_start_bound()
    ///     .to_finite_bound();
    ///
    /// assert_eq!(
    ///     start.opposite(),
    ///     AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive)
    ///         .to_finite_end_bound()
    ///         .to_finite_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(self) -> Self {
        match self {
            Self::Start(start) => Self::End(start.opposite()),
            Self::End(end) => Self::Start(end.opposite()),
        }
    }

    /// Converts `self` into [`AbsBound`]
    #[must_use]
    pub fn to_bound(self) -> AbsBound {
        AbsBound::from(self)
    }
}

impl HasBoundExtremality for AbsFiniteBound {
    fn bound_extremality(&self) -> BoundExtremality {
        match self {
            Self::Start(_) => BoundExtremality::Start,
            Self::End(_) => BoundExtremality::End,
        }
    }
}

impl BoundEq for AbsFiniteBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(start) => start.bound_eq(other, rule_set),
            Self::End(end) => end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsFiniteStartBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsFiniteEndBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsStartBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsEndBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundEq<AbsBound> for AbsFiniteBound {
    fn bound_eq(&self, other: &AbsBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Start(finite_start) => finite_start.bound_eq(other, rule_set),
            Self::End(finite_end) => finite_end.bound_eq(other, rule_set),
        }
    }
}

impl BoundOrd for AbsFiniteBound {
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

impl BoundOrdExtremaOps for AbsFiniteBound {}

impl BoundOrd<AbsFiniteStartBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsFiniteEndBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsStartBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsStartBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsEndBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsEndBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl BoundOrd<AbsBound> for AbsFiniteBound {
    fn bound_cmp(&self, other: &AbsBound) -> BoundOrdering {
        match self {
            Self::Start(finite_start) => finite_start.bound_cmp(other),
            Self::End(finite_end) => finite_end.bound_cmp(other),
        }
    }
}

impl From<AbsFiniteStartBound> for AbsFiniteBound {
    fn from(value: AbsFiniteStartBound) -> Self {
        Self::Start(value)
    }
}

impl From<AbsFiniteEndBound> for AbsFiniteBound {
    fn from(value: AbsFiniteEndBound) -> Self {
        Self::End(value)
    }
}

impl From<(AbsFiniteBoundPos, BoundExtremality)> for AbsFiniteBound {
    fn from((finite_pos, extremality): (AbsFiniteBoundPos, BoundExtremality)) -> Self {
        match extremality {
            BoundExtremality::Start => Self::Start(AbsFiniteStartBound::from(finite_pos)),
            BoundExtremality::End => Self::End(AbsFiniteEndBound::from(finite_pos)),
        }
    }
}

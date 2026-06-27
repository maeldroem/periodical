//! Relative start bound
//!
//! Represents the start bound of a relative interval. It can either be finite,
//! in which case it will contain an [`RelFiniteStartBound`], or represent
//! an open start bound through the [`InfinitePast`](RelStartBound::InfinitePast) variant.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    RelBound,
    RelEndBound,
    RelFiniteBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelFiniteStartBound,
};

/// Relative start bound
///
/// Represents the start bound of a relative interval. It can either be finite,
/// in which case it will contain an [`RelFiniteStartBound`], or represent
/// an open start bound through the [`InfinitePast`](RelStartBound::InfinitePast) variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelStartBound {
    Finite(RelFiniteStartBound),
    InfinitePast,
}

impl RelStartBound {
    /// Returns whether it is of the [`Finite`](RelStartBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelStartBound, RelFiniteBoundPos};
    /// let infinite_start_bound = RelStartBound::InfinitePast;
    /// let finite_start_bound = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    ///
    /// assert!(finite_start_bound.is_finite());
    /// assert!(!infinite_start_bound.is_finite());
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfinitePast`](RelStartBound::InfinitePast) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelStartBound, RelFiniteBoundPos};
    /// let infinite_start_bound = RelStartBound::InfinitePast;
    /// let finite_start_bound = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    ///
    /// assert!(infinite_start_bound.is_infinite_past());
    /// assert!(!finite_start_bound.is_infinite_past());
    /// ```
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfinitePast)
    }

    /// Returns the opposite [`RelEndBound`]
    ///
    /// If the [`RelStartBound`] is of the [`InfinitePast`](RelStartBound::InfinitePast) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`RelStartBound`] is finite, then an [`RelEndBound`] is created with the same offset,
    /// but opposite [`BoundInclusivity`].
    ///
    /// This is used, for example, for determining the last point in time before which this bound starts.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelStartBound, RelFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let offset = SignedDuration::from_hours(1);
    /// let start_second_shift = RelFiniteBoundPos::new(offset).to_start_bound();
    ///
    /// assert_eq!(
    ///     start_second_shift.opposite(),
    ///     Some(RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<RelEndBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_end_bound()),
            Self::InfinitePast => None,
        }
    }

    /// Returns the content of the [`Finite`](RelStartBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](RelStartBound::Finite) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelStartBound, RelFiniteBoundPos};
    /// let infinite_start_bound = RelStartBound::InfinitePast;
    ///
    /// let offset = SignedDuration::from_hours(1);
    /// let finite_start_bound = RelFiniteBoundPos::new(offset).to_start_bound();
    ///
    /// assert_eq!(
    ///     finite_start_bound.finite(),
    ///     Some(RelFiniteBoundPos::new(offset).to_finite_start_bound()),
    /// );
    /// assert_eq!(infinite_start_bound.finite(), None);
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<RelFiniteStartBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfinitePast => None,
        }
    }

    /// Wraps `self` in the corresponding [`RelBound`] variant
    #[must_use]
    pub fn to_bound(self) -> RelBound {
        RelBound::from(self)
    }
}

impl HasBoundExtremality for RelStartBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::Start
    }
}

impl PartialOrd for RelStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::InfinitePast, Self::InfinitePast) => Ordering::Equal,
            (Self::InfinitePast, Self::Finite(_)) => Ordering::Less,
            (Self::Finite(_), Self::InfinitePast) => Ordering::Greater,
            (Self::Finite(lhs_finite_start), Self::Finite(rhs_finite_start)) => lhs_finite_start.cmp(rhs_finite_start),
        }
    }
}

impl BoundEq for RelStartBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self {
            Self::Finite(lhs_finite_start) => lhs_finite_start.bound_eq(other, rule_set),
            Self::InfinitePast => other.is_infinite_past(),
        }
    }
}

impl BoundEq<RelFiniteStartBound> for RelStartBound {
    fn bound_eq(&self, other: &RelFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelFiniteEndBound> for RelStartBound {
    fn bound_eq(&self, other: &RelFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelFiniteBound> for RelStartBound {
    fn bound_eq(&self, other: &RelFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelEndBound> for RelStartBound {
    fn bound_eq(&self, other: &RelEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelBound> for RelStartBound {
    fn bound_eq(&self, other: &RelBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            RelBound::Start(rhs_start) => self.bound_eq(rhs_start, rule_set),
            RelBound::End(rhs_end) => self.bound_eq(rhs_end, rule_set),
        }
    }
}

impl BoundOrd for RelStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (Self::InfinitePast, Self::InfinitePast) => BoundOrdering::Equal(None),
            (Self::InfinitePast, Self::Finite(_)) => BoundOrdering::Less,
            (Self::Finite(_), Self::InfinitePast) => BoundOrdering::Greater,
            (Self::Finite(lhs_finite_start), Self::Finite(rhs_finite_start)) => {
                lhs_finite_start.bound_cmp(rhs_finite_start)
            },
        }
    }
}

impl BoundOrdExtremaOps for RelStartBound {}

impl BoundOrd<RelFiniteStartBound> for RelStartBound {
    fn bound_cmp(&self, other: &RelFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<RelFiniteEndBound> for RelStartBound {
    fn bound_cmp(&self, other: &RelFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<RelFiniteBound> for RelStartBound {
    fn bound_cmp(&self, other: &RelFiniteBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<RelEndBound> for RelStartBound {
    fn bound_cmp(&self, other: &RelEndBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<RelBound> for RelStartBound {
    fn bound_cmp(&self, other: &RelBound) -> BoundOrdering {
        match other {
            RelBound::Start(start) => self.bound_cmp(start),
            RelBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<RelFiniteStartBound> for RelStartBound {
    fn from(value: RelFiniteStartBound) -> Self {
        Self::Finite(value)
    }
}

impl From<RelFiniteBoundPos> for RelStartBound {
    fn from(value: RelFiniteBoundPos) -> Self {
        Self::Finite(RelFiniteStartBound::new(value))
    }
}

impl From<Option<SignedDuration>> for RelStartBound {
    fn from(value: Option<SignedDuration>) -> Self {
        match value {
            Some(offset) => Self::from(RelFiniteBoundPos::from(offset)),
            None => Self::InfinitePast,
        }
    }
}

impl From<Option<(SignedDuration, BoundInclusivity)>> for RelStartBound {
    fn from(value: Option<(SignedDuration, BoundInclusivity)>) -> Self {
        match value {
            Some((offset, inclusivity)) => Self::from(RelFiniteBoundPos::new_with_incl(offset, inclusivity)),
            None => Self::InfinitePast,
        }
    }
}

impl From<Bound<SignedDuration>> for RelStartBound {
    fn from(bound: Bound<SignedDuration>) -> Self {
        match bound {
            Bound::Included(offset) => {
                RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Inclusive).to_start_bound()
            },
            Bound::Excluded(offset) => {
                RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive).to_start_bound()
            },
            Bound::Unbounded => RelStartBound::InfinitePast,
        }
    }
}

/// Error that can occur when trying to convert an [`RelBound`] into an [`RelStartBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelStartBoundTryFromRelBoundError;

impl Display for RelStartBoundTryFromRelBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `RelBound` into an `RelStartBound`"
        )
    }
}

impl Error for RelStartBoundTryFromRelBoundError {}

impl TryFrom<RelBound> for RelStartBound {
    type Error = RelStartBoundTryFromRelBoundError;

    fn try_from(value: RelBound) -> Result<Self, Self::Error> {
        value.start().ok_or(RelStartBoundTryFromRelBoundError)
    }
}

// TODO: impl TryFrom for FiniteBound

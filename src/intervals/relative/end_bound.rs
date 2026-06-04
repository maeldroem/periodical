//! Relative end bound
//!
//! Represents the end bound of a relative interval. It can either be finite,
//! in which case it will contain an [`RelFiniteEndBound`], or represent
//! an open end bound through the [`InfiniteFuture`](RelEndBound::InfiniteFuture) variant.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality, HasBoundInclusivity};
use crate::intervals::ops::{
    BoundEq,
    BoundOrd,
    BoundOrdExtremaOps,
    BoundOrdering,
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
};
use crate::intervals::relative::{
    RelBound,
    RelFiniteBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelFiniteStartBound,
    RelStartBound,
};

/// Relative end bound
///
/// Represents the end bound of a relative interval. It can either be finite,
/// in which case it will contain an [`RelFiniteEndBound`], or represent
/// an open end bound through the [`InfiniteFuture`](RelEndBound::InfiniteFuture) variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelEndBound {
    Finite(RelFiniteEndBound),
    InfiniteFuture,
}

impl RelEndBound {
    /// Returns whether it is of the [`Finite`](RelEndBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelEndBound, RelFiniteBoundPos};
    /// let infinite_end_bound = RelEndBound::InfiniteFuture;
    /// let finite_end_bound = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();
    ///
    /// assert!(finite_end_bound.is_finite());
    /// assert!(!infinite_end_bound.is_finite());
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfiniteFuture`](RelEndBound::InfiniteFuture) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelEndBound, RelFiniteBoundPos};
    /// let infinite_end_bound = RelEndBound::InfiniteFuture;
    /// let finite_end_bound = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();
    ///
    /// assert!(infinite_end_bound.is_infinite_future());
    /// assert!(!finite_end_bound.is_infinite_future());
    /// ```
    #[must_use]
    pub fn is_infinite_future(&self) -> bool {
        matches!(self, Self::InfiniteFuture)
    }

    /// Returns the opposite [`RelStartBound`]
    ///
    /// If the [`RelEndBound`] is of the [`InfiniteFuture`](RelEndBound::InfiniteFuture) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`RelEndBound`] is finite, then a [`RelStartBound`] is created with the same offset,
    /// but opposite [`BoundInclusivity`].
    ///
    /// This is used, for example, for determining the first point in time after this bound ends.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelEndBound, RelFiniteBoundPos};
    /// let offset = SignedDuration::from_hours(1);
    /// let end_first_shift = RelFiniteBoundPos::new(offset).to_end_bound();
    ///
    /// assert_eq!(
    ///     end_first_shift.opposite(),
    ///     Some(
    ///         RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive).to_start_bound()
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<RelStartBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_start_bound()),
            Self::InfiniteFuture => None,
        }
    }

    /// Returns the content of the [`Finite`](RelEndBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](RelEndBound::Finite) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelEndBound, RelFiniteBoundPos};
    /// let infinite_end_bound = RelEndBound::InfiniteFuture;
    ///
    /// let offset = SignedDuration::from_hours(1);
    /// let finite_end_bound = RelFiniteBoundPos::new(offset).to_end_bound();
    ///
    /// assert_eq!(
    ///     finite_end_bound.finite(),
    ///     Some(RelFiniteBoundPos::new(offset).to_finite_end_bound()),
    /// );
    /// assert_eq!(infinite_end_bound.finite(), None);
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<RelFiniteEndBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfiniteFuture => None,
        }
    }

    /// Wraps `self` in the corresponding [`RelBound`] variant
    #[must_use]
    pub fn to_bound(self) -> RelBound {
        RelBound::from(self)
    }
}

impl HasBoundExtremality for RelEndBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::End
    }
}

impl PartialOrd for RelEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelEndBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::InfiniteFuture, Self::InfiniteFuture) => Ordering::Equal,
            (Self::InfiniteFuture, Self::Finite(_)) => Ordering::Greater,
            (Self::Finite(_), Self::InfiniteFuture) => Ordering::Less,
            (Self::Finite(lhs_finite_end), Self::Finite(rhs_finite_end)) => lhs_finite_end.cmp(rhs_finite_end),
        }
    }
}

impl BoundEq for RelEndBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        if let Some(rhs_finite_end) = self.finite()
            && let Some(lhs_finite_end) = other.finite()
        {
            rhs_finite_end.bound_eq(&lhs_finite_end, rule_set)
        } else {
            self.eq(other)
        }
    }
}

impl BoundEq<RelFiniteStartBound> for RelEndBound {
    fn bound_eq(&self, other: &RelFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelFiniteEndBound> for RelEndBound {
    fn bound_eq(&self, other: &RelFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelFiniteBound> for RelEndBound {
    fn bound_eq(&self, other: &RelFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelStartBound> for RelEndBound {
    fn bound_eq(&self, other: &RelStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<RelBound> for RelEndBound {
    fn bound_eq(&self, other: &RelBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundOrd for RelEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match self.cmp(other) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(self.finite().zip(other.finite()).map(
                |(lhs_finite_end, rhs_finite_end)| {
                    BoundOverlapAmbiguity::BothEnds(
                        lhs_finite_end.pos().inclusivity(),
                        rhs_finite_end.pos().inclusivity(),
                    )
                },
            )),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrdExtremaOps for RelEndBound {}

impl BoundOrd<RelFiniteStartBound> for RelEndBound {
    fn bound_cmp(&self, other: &RelFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<RelFiniteEndBound> for RelEndBound {
    fn bound_cmp(&self, other: &RelFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<RelFiniteBound> for RelEndBound {
    fn bound_cmp(&self, other: &RelFiniteBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<RelStartBound> for RelEndBound {
    fn bound_cmp(&self, other: &RelStartBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<RelBound> for RelEndBound {
    fn bound_cmp(&self, other: &RelBound) -> BoundOrdering {
        match other {
            RelBound::Start(start) => self.bound_cmp(start),
            RelBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<RelFiniteEndBound> for RelEndBound {
    fn from(value: RelFiniteEndBound) -> Self {
        Self::Finite(value)
    }
}

impl From<RelFiniteBoundPos> for RelEndBound {
    fn from(value: RelFiniteBoundPos) -> Self {
        Self::Finite(RelFiniteEndBound::new(value))
    }
}

impl From<Option<SignedDuration>> for RelEndBound {
    fn from(value: Option<SignedDuration>) -> Self {
        match value {
            Some(offset) => Self::from(RelFiniteBoundPos::from(offset)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Option<(SignedDuration, BoundInclusivity)>> for RelEndBound {
    fn from(value: Option<(SignedDuration, BoundInclusivity)>) -> Self {
        match value {
            Some((offset, inclusivity)) => Self::from(RelFiniteBoundPos::new_with_incl(offset, inclusivity)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Bound<SignedDuration>> for RelEndBound {
    fn from(bound: Bound<SignedDuration>) -> Self {
        match bound {
            Bound::Included(offset) => {
                RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Inclusive).to_end_bound()
            },
            Bound::Excluded(offset) => {
                RelFiniteBoundPos::new_with_incl(offset, BoundInclusivity::Exclusive).to_end_bound()
            },
            Bound::Unbounded => RelEndBound::InfiniteFuture,
        }
    }
}

/// Error that can occur when trying to convert an [`RelBound`] into an [`RelEndBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelEndBoundTryFromRelBoundError;

impl Display for RelEndBoundTryFromRelBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `RelBound` into an `RelEndBound`"
        )
    }
}

impl Error for RelEndBoundTryFromRelBoundError {}

impl TryFrom<RelBound> for RelEndBound {
    type Error = RelEndBoundTryFromRelBoundError;

    fn try_from(value: RelBound) -> Result<Self, Self::Error> {
        value.end().ok_or(RelEndBoundTryFromRelBoundError)
    }
}

// TODO: impl TryFrom for FiniteBound

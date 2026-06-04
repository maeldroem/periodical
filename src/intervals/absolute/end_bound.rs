//! Absolute end bound
//!
//! Represents the end bound of an absolute interval. It can either be finite,
//! in which case it will contain an [`AbsFiniteEndBound`], or represent
//! an open end bound through the [`InfiniteFuture`](AbsEndBound::InfiniteFuture) variant.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::Bound;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBound,
    AbsFiniteBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
    AbsStartBound,
};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality, HasBoundInclusivity};
use crate::intervals::ops::{
    BoundEq,
    BoundOrd,
    BoundOrdExtremaOps,
    BoundOrdering,
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
};

/// Absolute end bound
///
/// Represents the end bound of an absolute interval. It can either be finite,
/// in which case it will contain an [`AbsFiniteEndBound`], or represent
/// an open end bound through the [`InfiniteFuture`](AbsEndBound::InfiniteFuture) variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsEndBound {
    Finite(AbsFiniteEndBound),
    InfiniteFuture,
}

impl AbsEndBound {
    /// Returns whether it is of the [`Finite`](AbsEndBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos};
    /// let infinite_end_bound = AbsEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound();
    ///
    /// assert!(finite_end_bound.is_finite());
    /// assert!(!infinite_end_bound.is_finite());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfiniteFuture`](AbsEndBound::InfiniteFuture) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos};
    /// let infinite_end_bound = AbsEndBound::InfiniteFuture;
    /// let finite_end_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound();
    ///
    /// assert!(infinite_end_bound.is_infinite_future());
    /// assert!(!finite_end_bound.is_infinite_future());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_infinite_future(&self) -> bool {
        matches!(self, Self::InfiniteFuture)
    }

    /// Returns the opposite [`AbsStartBound`]
    ///
    /// If the [`AbsEndBound`] is of the [`InfiniteFuture`](AbsEndBound::InfiniteFuture) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`AbsEndBound`] is finite, then an [`AbsStartBound`] is created with the same time,
    /// but opposite [`BoundInclusivity`].
    ///
    /// This is used, for example, for determining the first point in time after this bound ends.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_first_shift = AbsFiniteBoundPos::new(time).to_end_bound();
    ///
    /// assert_eq!(
    ///     end_first_shift.opposite(),
    ///     Some(AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_start_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsStartBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_start_bound()),
            Self::InfiniteFuture => None,
        }
    }

    /// Returns the content of the [`Finite`](AbsEndBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](AbsEndBound::Finite) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos};
    /// let infinite_end_bound = AbsEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_end_bound = AbsFiniteBoundPos::new(time).to_end_bound();
    ///
    /// assert_eq!(
    ///     finite_end_bound.finite(),
    ///     Some(AbsFiniteBoundPos::new(time).to_finite_end_bound())
    /// );
    /// assert_eq!(infinite_end_bound.finite(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<AbsFiniteEndBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfiniteFuture => None,
        }
    }

    /// Wraps `self` in the corresponding [`AbsBound`] variant
    #[must_use]
    pub fn to_bound(self) -> AbsBound {
        AbsBound::from(self)
    }
}

impl HasBoundExtremality for AbsEndBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::End
    }
}

impl PartialOrd for AbsEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsEndBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::InfiniteFuture, Self::InfiniteFuture) => Ordering::Equal,
            (Self::InfiniteFuture, Self::Finite(_)) => Ordering::Greater,
            (Self::Finite(_), Self::InfiniteFuture) => Ordering::Less,
            (Self::Finite(lhs_finite_end), Self::Finite(rhs_finite_end)) => lhs_finite_end.cmp(rhs_finite_end),
        }
    }
}

impl BoundEq for AbsEndBound {
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

impl BoundEq<AbsFiniteStartBound> for AbsEndBound {
    fn bound_eq(&self, other: &AbsFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsFiniteEndBound> for AbsEndBound {
    fn bound_eq(&self, other: &AbsFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsFiniteBound> for AbsEndBound {
    fn bound_eq(&self, other: &AbsFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsStartBound> for AbsEndBound {
    fn bound_eq(&self, other: &AbsStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsBound> for AbsEndBound {
    fn bound_eq(&self, other: &AbsBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_end| finite_end.bound_eq(other, rule_set))
    }
}

impl BoundOrd for AbsEndBound {
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

impl BoundOrdExtremaOps for AbsEndBound {}

impl BoundOrd<AbsFiniteStartBound> for AbsEndBound {
    fn bound_cmp(&self, other: &AbsFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<AbsFiniteEndBound> for AbsEndBound {
    fn bound_cmp(&self, other: &AbsFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<AbsFiniteBound> for AbsEndBound {
    fn bound_cmp(&self, other: &AbsFiniteBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<AbsStartBound> for AbsEndBound {
    fn bound_cmp(&self, other: &AbsStartBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_end) => finite_end.bound_cmp(other),
            Self::InfiniteFuture => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<AbsBound> for AbsEndBound {
    fn bound_cmp(&self, other: &AbsBound) -> BoundOrdering {
        match other {
            AbsBound::Start(start) => self.bound_cmp(start),
            AbsBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<AbsFiniteEndBound> for AbsEndBound {
    fn from(value: AbsFiniteEndBound) -> Self {
        Self::Finite(value)
    }
}

impl From<AbsFiniteBoundPos> for AbsEndBound {
    fn from(value: AbsFiniteBoundPos) -> Self {
        Self::Finite(AbsFiniteEndBound::new(value))
    }
}

impl From<Option<Timestamp>> for AbsEndBound {
    fn from(value: Option<Timestamp>) -> Self {
        match value {
            Some(timestamp) => Self::from(AbsFiniteBoundPos::from(timestamp)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Option<(Timestamp, BoundInclusivity)>> for AbsEndBound {
    fn from(value: Option<(Timestamp, BoundInclusivity)>) -> Self {
        match value {
            Some((timestamp, inclusivity)) => Self::from(AbsFiniteBoundPos::new_with_incl(timestamp, inclusivity)),
            None => Self::InfiniteFuture,
        }
    }
}

impl From<Bound<Timestamp>> for AbsEndBound {
    fn from(bound: Bound<Timestamp>) -> Self {
        match bound {
            Bound::Included(time) => AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Inclusive).to_end_bound(),
            Bound::Excluded(time) => AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_end_bound(),
            Bound::Unbounded => AbsEndBound::InfiniteFuture,
        }
    }
}

/// Error that can occur when trying to convert an [`AbsBound`] into an [`AbsEndBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsEndBoundTryFromAbsBoundError;

impl Display for AbsEndBoundTryFromAbsBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `AbsBound` into an `AbsEndBound`"
        )
    }
}

impl Error for AbsEndBoundTryFromAbsBoundError {}

impl TryFrom<AbsBound> for AbsEndBound {
    type Error = AbsEndBoundTryFromAbsBoundError;

    fn try_from(value: AbsBound) -> Result<Self, Self::Error> {
        value.end().ok_or(AbsEndBoundTryFromAbsBoundError)
    }
}

// TODO: impl TryFrom for FiniteBound

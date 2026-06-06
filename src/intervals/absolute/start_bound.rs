//! Absolute start bound
//!
//! Represents the start bound of an absolute interval. It can either be finite,
//! in which case it will contain an [`AbsFiniteStartBound`], or represent
//! an open start bound through the [`InfinitePast`](AbsStartBound::InfinitePast) variant.

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
    AbsEndBound,
    AbsFiniteBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapDisambiguationRuleSet};

/// Absolute start bound
///
/// Represents the start bound of an absolute interval. It can either be finite,
/// in which case it will contain an [`AbsFiniteStartBound`], or represent
/// an open start bound through the [`InfinitePast`](AbsStartBound::InfinitePast) variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsStartBound {
    Finite(AbsFiniteStartBound),
    InfinitePast,
}

impl AbsStartBound {
    /// Returns whether it is of the [`Finite`](AbsStartBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsStartBound, AbsFiniteBoundPos};
    /// let infinite_start_bound = AbsStartBound::InfinitePast;
    /// let finite_start_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// assert!(finite_start_bound.is_finite());
    /// assert!(!infinite_start_bound.is_finite());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfinitePast`](AbsStartBound::InfinitePast) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsStartBound, AbsFiniteBoundPos};
    /// let infinite_start_bound = AbsStartBound::InfinitePast;
    /// let finite_start_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// assert!(infinite_start_bound.is_infinite_past());
    /// assert!(!finite_start_bound.is_infinite_past());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfinitePast)
    }

    /// Returns the opposite [`AbsEndBound`]
    ///
    /// If the [`AbsStartBound`] is of the [`InfinitePast`](AbsStartBound::InfinitePast) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`AbsStartBound`] is finite, then an [`AbsEndBound`] is created with the same time,
    /// but opposite [`BoundInclusivity`].
    ///
    /// This is used, for example, for determining the last point in time before which this bound starts.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsStartBound, AbsFiniteBoundPos};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let start_second_shift = AbsFiniteBoundPos::new(time).to_start_bound();
    ///
    /// assert_eq!(
    ///     start_second_shift.opposite(),
    ///     Some(AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsEndBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_end_bound()),
            Self::InfinitePast => None,
        }
    }

    /// Returns the content of the [`Finite`](AbsStartBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](AbsStartBound::Finite) variant in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsStartBound, AbsFiniteBoundPos};
    /// let infinite_start_bound = AbsStartBound::InfinitePast;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_start_bound = AbsFiniteBoundPos::new(time).to_start_bound();
    ///
    /// assert_eq!(
    ///     finite_start_bound.finite(),
    ///     Some(AbsFiniteBoundPos::new(time).to_finite_start_bound())
    /// );
    /// assert_eq!(infinite_start_bound.finite(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<AbsFiniteStartBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfinitePast => None,
        }
    }

    /// Wraps `self` in the corresponding [`AbsBound`] variant
    #[must_use]
    pub fn to_bound(self) -> AbsBound {
        AbsBound::from(self)
    }
}

impl HasBoundExtremality for AbsStartBound {
    fn bound_extremality(&self) -> BoundExtremality {
        BoundExtremality::Start
    }
}

impl PartialOrd for AbsStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::InfinitePast, Self::InfinitePast) => Ordering::Equal,
            (Self::InfinitePast, Self::Finite(_)) => Ordering::Less,
            (Self::Finite(_), Self::InfinitePast) => Ordering::Greater,
            (Self::Finite(lhs_finite_start), Self::Finite(rhs_finite_start)) => lhs_finite_start.cmp(rhs_finite_start),
        }
    }
}

impl BoundEq for AbsStartBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        if let Some(rhs_finite_start) = self.finite()
            && let Some(lhs_finite_start) = other.finite()
        {
            rhs_finite_start.bound_eq(&lhs_finite_start, rule_set)
        } else {
            self.eq(other)
        }
    }
}

impl BoundEq<AbsFiniteStartBound> for AbsStartBound {
    fn bound_eq(&self, other: &AbsFiniteStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsFiniteEndBound> for AbsStartBound {
    fn bound_eq(&self, other: &AbsFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsFiniteBound> for AbsStartBound {
    fn bound_eq(&self, other: &AbsFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsEndBound> for AbsStartBound {
    fn bound_eq(&self, other: &AbsEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundEq<AbsBound> for AbsStartBound {
    fn bound_eq(&self, other: &AbsBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundOrd for AbsStartBound {
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

impl BoundOrdExtremaOps for AbsStartBound {}

impl BoundOrd<AbsFiniteStartBound> for AbsStartBound {
    fn bound_cmp(&self, other: &AbsFiniteStartBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<AbsFiniteEndBound> for AbsStartBound {
    fn bound_cmp(&self, other: &AbsFiniteEndBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<AbsFiniteBound> for AbsStartBound {
    fn bound_cmp(&self, other: &AbsFiniteBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<AbsEndBound> for AbsStartBound {
    fn bound_cmp(&self, other: &AbsEndBound) -> BoundOrdering {
        match self {
            Self::Finite(finite_start) => finite_start.bound_cmp(other),
            Self::InfinitePast => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<AbsBound> for AbsStartBound {
    fn bound_cmp(&self, other: &AbsBound) -> BoundOrdering {
        match other {
            AbsBound::Start(start) => self.bound_cmp(start),
            AbsBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<AbsFiniteStartBound> for AbsStartBound {
    fn from(value: AbsFiniteStartBound) -> Self {
        Self::Finite(value)
    }
}

impl From<AbsFiniteBoundPos> for AbsStartBound {
    fn from(value: AbsFiniteBoundPos) -> Self {
        Self::Finite(AbsFiniteStartBound::new(value))
    }
}

impl From<Option<Timestamp>> for AbsStartBound {
    fn from(value: Option<Timestamp>) -> Self {
        match value {
            Some(timestamp) => Self::from(AbsFiniteBoundPos::from(timestamp)),
            None => Self::InfinitePast,
        }
    }
}

impl From<Option<(Timestamp, BoundInclusivity)>> for AbsStartBound {
    fn from(value: Option<(Timestamp, BoundInclusivity)>) -> Self {
        match value {
            Some((timestamp, inclusivity)) => Self::from(AbsFiniteBoundPos::new_with_incl(timestamp, inclusivity)),
            None => Self::InfinitePast,
        }
    }
}

impl From<Bound<Timestamp>> for AbsStartBound {
    fn from(bound: Bound<Timestamp>) -> Self {
        match bound {
            Bound::Included(time) => {
                AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Inclusive).to_start_bound()
            },
            Bound::Excluded(time) => {
                AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_start_bound()
            },
            Bound::Unbounded => AbsStartBound::InfinitePast,
        }
    }
}

/// Error that can occur when trying to convert an [`AbsBound`] into an [`AbsStartBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsStartBoundTryFromAbsBoundError;

impl Display for AbsStartBoundTryFromAbsBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert an `AbsBound` into an `AbsStartBound`"
        )
    }
}

impl Error for AbsStartBoundTryFromAbsBoundError {}

impl TryFrom<AbsBound> for AbsStartBound {
    type Error = AbsStartBoundTryFromAbsBoundError;

    fn try_from(value: AbsBound) -> Result<Self, Self::Error> {
        value.start().ok_or(AbsStartBoundTryFromAbsBoundError)
    }
}

// TODO: impl TryFrom for FiniteBound

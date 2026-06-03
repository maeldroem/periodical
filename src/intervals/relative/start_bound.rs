//! Relative start bound
//!
//! Represents the start bound of a relative interval. It can either be finite,
//! in which case it will contain an [`RelFiniteBoundPos`], or represent an
//! open start bound through
//! the [`InfinitePast`](RelStartBound::InfinitePast) variant.

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
    RelEndBound,
    RelFiniteBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelFiniteStartBound,
};

/// A relative start bound
///
/// Represents the start bound of an interval, may it be infinitely in the past
/// or at a precise offset, in which case it contains an
/// [`RelFiniteBoundPos`].
///
/// Contrary to specific relative interval types, both [`RelStartBound`]
/// and [`RelEndBound`] use an offset, and not an offset for the start and
/// a length for the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelStartBound {
    Finite(RelFiniteStartBound),
    InfinitePast,
}

impl RelStartBound {
    /// Wraps the start bound of the corresponding [`RelBound`] variant
    #[must_use]
    pub fn to_bound(self) -> RelBound {
        RelBound::from(self)
    }

    /// Returns whether it is of the [`Finite`](RelStartBound::Finite)
    /// variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, RelStartBound};
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

    /// Returns whether it is of the
    /// [`InfinitePast`](RelStartBound::InfinitePast) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, RelStartBound};
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

    /// Returns the content of the [`Finite`](RelStartBound::Finite)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Finite`](RelStartBound::Finite) variant in an [`Option`]. If
    /// instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, RelStartBound};
    /// let infinite_start_bound = RelStartBound::InfinitePast;
    /// let finite_start_bound = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
    ///
    /// assert_eq!(
    ///     finite_start_bound.finite(),
    ///     Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1))),
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

    /// Returns the opposite [`RelEndBound`]
    ///
    /// If the [`RelStartBound`] is of the
    /// [`InfinitePast`](RelStartBound::InfinitePast) variant, then the
    /// method returns [`None`]. Otherwise, if the [`RelStartBound`] is
    /// finite, then an [`RelEndBound`] is created with the same time,
    /// but the opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the last point in time before
    /// this bound begins.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::{RelFiniteBoundPos, RelStartBound};
    /// #
    /// # #[derive(Debug)]
    /// # struct FiniteBoundPositionExpectedError;
    /// #
    /// # impl std::fmt::Display for FiniteBoundPositionExpectedError {
    /// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    /// #         write!(f, "Finite bound expected")
    /// #     }
    /// # }
    /// #
    /// # impl Error for FiniteBoundPositionExpectedError {}
    /// let start_second_part_my_shift =
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound();
    /// let break_end_before_shift = start_second_part_my_shift
    ///     .opposite()
    ///     .ok_or(FiniteBoundPositionExpectedError)?;
    ///
    /// assert_eq!(
    ///     break_end_before_shift.finite(),
    ///     Some(RelFiniteBoundPos::new_with_incl(
    ///         SignedDuration::from_hours(3),
    ///         BoundInclusivity::Exclusive,
    ///     )),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<RelEndBound> {
        match self {
            Self::Finite(finite) => Some(finite.opposite().to_end_bound()),
            Self::InfinitePast => None,
        }
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
        if let Some(rhs_finite_start) = self.finite()
            && let Some(lhs_finite_start) = other.finite()
        {
            rhs_finite_start.bound_eq(&lhs_finite_start, rule_set)
        } else {
            self.eq(other)
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
        self.finite()
            .is_some_and(|finite_start| finite_start.bound_eq(other, rule_set))
    }
}

impl BoundOrd for RelStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match self.cmp(other) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(self.finite().zip(other.finite()).map(
                |(lhs_finite_start, rhs_finite_start)| {
                    BoundOverlapAmbiguity::BothStarts(
                        lhs_finite_start.pos().inclusivity(),
                        rhs_finite_start.pos().inclusivity(),
                    )
                },
            )),
            Ordering::Greater => BoundOrdering::Greater,
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

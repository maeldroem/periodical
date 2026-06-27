//! Absolute finite start bound
//!
//! Represents the finite start bound of an absolute interval.
//! If you need to represent infinity, see [`AbsStartBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsBound,
    AbsEndBound,
    AbsFiniteBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsStartBound,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{
    BoundEq,
    BoundOrd,
    BoundOrdExtremaOps,
    BoundOrdering,
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
};

/// Absolute finite start bound
///
/// Represents the finite start bound of an absolute interval.
/// If you need to represent infinity, see [`AbsStartBound`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsFiniteStartBound(pub(crate) AbsFiniteBoundPos);

impl AbsFiniteStartBound {
    /// Creates a new absolute finite start bound
    #[must_use]
    pub fn new(finite_bound_pos: AbsFiniteBoundPos) -> Self {
        Self(finite_bound_pos)
    }

    /// Returns the inner absolute finite bound position
    #[must_use]
    pub fn pos(&self) -> AbsFiniteBoundPos {
        self.0
    }

    /// Returns a mutable pointer of the inner absolute finite bound position
    ///
    /// This is used for mutating which position this start bound represents.
    #[must_use]
    pub fn pos_mut(&mut self) -> &mut AbsFiniteBoundPos {
        &mut self.0
    }

    /// Returns the opposite finite end bound
    ///
    /// Returns the opposite absolute finite end bound with the same time
    /// but opposite bound inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let time = "2026-01-01 10:00:00Z".parse::<Timestamp>()?;
    /// let shift_start = AbsFiniteBoundPos::new(time).to_finite_start_bound();
    ///
    /// assert_eq!(
    ///     shift_start.opposite(),
    ///     AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_finite_end_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn opposite(self) -> AbsFiniteEndBound {
        AbsFiniteEndBound::new(AbsFiniteBoundPos::new_with_incl(
            self.pos().time(),
            self.pos().inclusivity().opposite(),
        ))
    }

    /// Wraps `self` in [`AbsStartBound`]
    #[must_use]
    pub fn to_start_bound(self) -> AbsStartBound {
        AbsStartBound::Finite(self)
    }

    /// Wraps `self` in the corresponding [`AbsFiniteBound`] variant
    #[must_use]
    pub fn to_finite_bound(self) -> AbsFiniteBound {
        AbsFiniteBound::from(self)
    }

    /// Converts `self` into [`AbsBound`]
    #[must_use]
    pub fn to_bound(self) -> AbsBound {
        AbsBound::from(self)
    }
}

impl PartialOrd for AbsFiniteStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsFiniteStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.pos().time().cmp(&other.pos().time()).then_with(|| {
            match (self.pos().inclusivity(), other.pos().inclusivity()) {
                (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Less,
                (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Greater,
            }
        })
    }
}

impl BoundEq for AbsFiniteStartBound {
    fn bound_eq(&self, other: &Self, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.pos().time().eq(&other.pos().time())
            && BoundOverlapAmbiguity::BothStarts(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<AbsStartBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsStartBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_start| self.bound_eq(&finite_start, rule_set))
    }
}

impl BoundEq<AbsFiniteEndBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsFiniteEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.pos().time().eq(&other.pos().time())
            && BoundOverlapAmbiguity::StartEnd(self.pos().inclusivity(), other.pos().inclusivity())
                .disambiguate(rule_set)
                .is_equal()
    }
}

impl BoundEq<AbsEndBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsEndBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        other
            .finite()
            .is_some_and(|finite_end| self.bound_eq(&finite_end, rule_set))
    }
}

impl BoundEq<AbsFiniteBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsFiniteBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            AbsFiniteBound::Start(finite_start) => self.bound_eq(finite_start, rule_set),
            AbsFiniteBound::End(finite_end) => self.bound_eq(finite_end, rule_set),
        }
    }
}

impl BoundEq<AbsBound> for AbsFiniteStartBound {
    fn bound_eq(&self, other: &AbsBound, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match other {
            AbsBound::Start(start) => self.bound_eq(start, rule_set),
            AbsBound::End(end) => self.bound_eq(end, rule_set),
        }
    }
}

impl BoundOrd for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match self.pos().time().cmp(&other.pos().time()) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                self.pos().inclusivity(),
                other.pos().inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrdExtremaOps for AbsFiniteStartBound {}

impl BoundOrd<AbsStartBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsStartBound) -> BoundOrdering {
        if let Some(finite_start) = other.finite() {
            self.bound_cmp(&finite_start)
        } else {
            BoundOrdering::Greater
        }
    }
}

impl BoundOrd<AbsFiniteEndBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsFiniteEndBound) -> BoundOrdering {
        match self.pos().time().cmp(&other.pos().time()) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                self.pos().inclusivity(),
                other.pos().inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<AbsEndBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsEndBound) -> BoundOrdering {
        match other {
            AbsEndBound::Finite(finite_end) => self.bound_cmp(finite_end),
            AbsEndBound::InfiniteFuture => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<AbsFiniteBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsFiniteBound) -> BoundOrdering {
        match other {
            AbsFiniteBound::Start(finite_start) => self.bound_cmp(finite_start),
            AbsFiniteBound::End(finite_end) => self.bound_cmp(finite_end),
        }
    }
}

impl BoundOrd<AbsBound> for AbsFiniteStartBound {
    fn bound_cmp(&self, other: &AbsBound) -> BoundOrdering {
        match other {
            AbsBound::Start(start) => self.bound_cmp(start),
            AbsBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<AbsFiniteBoundPos> for AbsFiniteStartBound {
    fn from(value: AbsFiniteBoundPos) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

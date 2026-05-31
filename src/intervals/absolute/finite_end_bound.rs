//! Absolute finite end bound
//!
//! Represents the finite end bound of an absolute interval.
//! If you need to represent infinity, see [`AbsoluteEndBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteFiniteStartBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundOverlapAmbiguity, BoundPartialEq, BoundPartialOrd};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteFiniteEndBound(pub(crate) AbsoluteFiniteBoundPosition);

impl AbsoluteFiniteEndBound {
    pub fn new(finite_bound_pos: AbsoluteFiniteBoundPosition) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> AbsoluteFiniteBoundPosition {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut AbsoluteFiniteBoundPosition {
        &mut self.0
    }

    pub fn to_end_bound(self) -> AbsoluteEndBound {
        AbsoluteEndBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> AbsoluteFiniteBound {
        AbsoluteFiniteBound::from(self)
    }

    pub fn to_bound(self) -> AbsoluteBound {
        AbsoluteBound::from(self)
    }

    pub fn opposite(self) -> AbsoluteFiniteStartBound {
        AbsoluteFiniteStartBound::new(AbsoluteFiniteBoundPosition::new_with_inclusivity(
            self.pos().time(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for AbsoluteFiniteEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteFiniteEndBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.pos()
            .cmp(&other.pos())
            .then_with(|| match (self.pos().inclusivity(), other.pos().inclusivity()) {
                (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Greater,
                (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Less,
            })
    }
}

impl BoundPartialEq for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl BoundEq for AbsoluteFiniteEndBound {}

impl BoundPartialEq<AbsoluteEndBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteEndBound) -> bool {
        other.finite().is_some_and(|finite_end| self.bound_eq(&finite_end))
    }
}

impl BoundPartialEq<AbsoluteFiniteStartBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteFiniteStartBound) -> bool {
        let end_pos = self.pos();
        let start_pos = other.pos();

        end_pos.eq(&start_pos)
            && end_pos.inclusivity() == BoundInclusivity::Inclusive
            && start_pos.inclusivity() == BoundInclusivity::Inclusive
    }
}

impl BoundPartialEq<AbsoluteStartBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteStartBound) -> bool {
        other.finite().is_some_and(|finite_start| self.bound_eq(&finite_start))
    }
}

impl BoundPartialEq<AbsoluteFiniteBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteFiniteBound) -> bool {
        match other {
            AbsoluteFiniteBound::Start(finite_start) => self.bound_eq(finite_start),
            AbsoluteFiniteBound::End(finite_end) => self.bound_eq(finite_end),
        }
    }
}

impl BoundPartialEq<AbsoluteBound> for AbsoluteFiniteEndBound {
    fn bound_eq(&self, other: &AbsoluteBound) -> bool {
        match other {
            AbsoluteBound::Start(start) => self.bound_eq(start),
            AbsoluteBound::End(end) => self.bound_eq(end),
        }
    }
}

impl BoundPartialOrd for AbsoluteFiniteEndBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for AbsoluteFiniteEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        let lhs_pos = self.pos();
        let rhs_pos = other.pos();

        match lhs_pos.cmp(&rhs_pos) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                lhs_pos.inclusivity(),
                rhs_pos.inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundPartialOrd<AbsoluteEndBound> for AbsoluteFiniteEndBound {
    fn bound_partial_cmp(&self, other: &AbsoluteEndBound) -> Option<BoundOrdering> {
        Some(if let Some(finite_end) = other.finite() {
            self.bound_cmp(&finite_end)
        } else {
            BoundOrdering::Less
        })
    }
}

impl BoundPartialOrd<AbsoluteFiniteStartBound> for AbsoluteFiniteEndBound {
    fn bound_partial_cmp(&self, other: &AbsoluteFiniteStartBound) -> Option<BoundOrdering> {
        let lhs_pos = self.pos();
        let rhs_pos = other.pos();

        Some(match lhs_pos.cmp(&rhs_pos) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                lhs_pos.inclusivity(),
                rhs_pos.inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        })
    }
}

impl BoundPartialOrd<AbsoluteStartBound> for AbsoluteFiniteEndBound {
    fn bound_partial_cmp(&self, other: &AbsoluteStartBound) -> Option<BoundOrdering> {
        match other {
            AbsoluteStartBound::Finite(finite_end) => self.bound_partial_cmp(finite_end),
            AbsoluteStartBound::InfinitePast => Some(BoundOrdering::Greater),
        }
    }
}

impl BoundPartialOrd<AbsoluteFiniteBound> for AbsoluteFiniteEndBound {
    fn bound_partial_cmp(&self, other: &AbsoluteFiniteBound) -> Option<BoundOrdering> {
        match other {
            AbsoluteFiniteBound::Start(finite_start) => self.bound_partial_cmp(finite_start),
            AbsoluteFiniteBound::End(finite_end) => self.bound_partial_cmp(finite_end),
        }
    }
}

impl BoundPartialOrd<AbsoluteBound> for AbsoluteFiniteEndBound {
    fn bound_partial_cmp(&self, other: &AbsoluteBound) -> Option<BoundOrdering> {
        match other {
            AbsoluteBound::Start(start) => self.bound_partial_cmp(start),
            AbsoluteBound::End(end) => self.bound_partial_cmp(end),
        }
    }
}

impl From<AbsoluteFiniteBoundPosition> for AbsoluteFiniteEndBound {
    fn from(value: AbsoluteFiniteBoundPosition) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

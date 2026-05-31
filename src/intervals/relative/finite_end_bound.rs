//! Relative finite end bound
//!
//! Represents the finite end bound of an relative interval.
//! If you need to represent infinity, see [`RelativeEndBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdering, BoundOverlapAmbiguity, BoundPartialEq, BoundPartialOrd};
use crate::intervals::relative::{
    RelativeBound,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteStartBound,
    RelativeStartBound,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeFiniteEndBound(pub(crate) RelativeFiniteBoundPosition);

impl RelativeFiniteEndBound {
    pub fn new(finite_bound_pos: RelativeFiniteBoundPosition) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> RelativeFiniteBoundPosition {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut RelativeFiniteBoundPosition {
        &mut self.0
    }

    pub fn to_end_bound(self) -> RelativeEndBound {
        RelativeEndBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> RelativeFiniteBound {
        RelativeFiniteBound::from(self)
    }

    pub fn to_bound(self) -> RelativeBound {
        RelativeBound::from(self)
    }

    pub fn opposite(self) -> RelativeFiniteStartBound {
        RelativeFiniteStartBound::new(RelativeFiniteBoundPosition::new_with_inclusivity(
            self.pos().offset(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for RelativeFiniteEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeFiniteEndBound {
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

impl BoundPartialEq for RelativeFiniteEndBound {
    fn bound_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl BoundEq for RelativeFiniteEndBound {}

impl BoundPartialEq<RelativeEndBound> for RelativeFiniteEndBound {
    fn bound_eq(&self, other: &RelativeEndBound) -> bool {
        other.finite().is_some_and(|finite_end| self.bound_eq(&finite_end))
    }
}

impl BoundPartialEq<RelativeFiniteStartBound> for RelativeFiniteEndBound {
    fn bound_eq(&self, other: &RelativeFiniteStartBound) -> bool {
        let end_pos = self.pos();
        let start_pos = other.pos();

        end_pos.eq(&start_pos)
            && end_pos.inclusivity() == BoundInclusivity::Inclusive
            && start_pos.inclusivity() == BoundInclusivity::Inclusive
    }
}

impl BoundPartialEq<RelativeStartBound> for RelativeFiniteEndBound {
    fn bound_eq(&self, other: &RelativeStartBound) -> bool {
        other.finite().is_some_and(|finite_start| self.bound_eq(&finite_start))
    }
}

impl BoundPartialEq<RelativeFiniteBound> for RelativeFiniteEndBound {
    fn bound_eq(&self, other: &RelativeFiniteBound) -> bool {
        match other {
            RelativeFiniteBound::Start(finite_start) => self.bound_eq(finite_start),
            RelativeFiniteBound::End(finite_end) => self.bound_eq(finite_end),
        }
    }
}

impl BoundPartialEq<RelativeBound> for RelativeFiniteEndBound {
    fn bound_eq(&self, other: &RelativeBound) -> bool {
        match other {
            RelativeBound::Start(start) => self.bound_eq(start),
            RelativeBound::End(end) => self.bound_eq(end),
        }
    }
}

impl BoundPartialOrd for RelativeFiniteEndBound {
    fn bound_partial_cmp(&self, other: &Self) -> Option<BoundOrdering> {
        Some(self.bound_cmp(other))
    }
}

impl BoundOrd for RelativeFiniteEndBound {
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

impl BoundPartialOrd<RelativeEndBound> for RelativeFiniteEndBound {
    fn bound_partial_cmp(&self, other: &RelativeEndBound) -> Option<BoundOrdering> {
        Some(if let Some(finite_end) = other.finite() {
            self.bound_cmp(&finite_end)
        } else {
            BoundOrdering::Less
        })
    }
}

impl BoundPartialOrd<RelativeFiniteStartBound> for RelativeFiniteEndBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteStartBound) -> Option<BoundOrdering> {
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

impl BoundPartialOrd<RelativeStartBound> for RelativeFiniteEndBound {
    fn bound_partial_cmp(&self, other: &RelativeStartBound) -> Option<BoundOrdering> {
        match other {
            RelativeStartBound::Finite(finite_end) => self.bound_partial_cmp(finite_end),
            RelativeStartBound::InfinitePast => Some(BoundOrdering::Greater),
        }
    }
}

impl BoundPartialOrd<RelativeFiniteBound> for RelativeFiniteEndBound {
    fn bound_partial_cmp(&self, other: &RelativeFiniteBound) -> Option<BoundOrdering> {
        match other {
            RelativeFiniteBound::Start(finite_start) => self.bound_partial_cmp(finite_start),
            RelativeFiniteBound::End(finite_end) => self.bound_partial_cmp(finite_end),
        }
    }
}

impl BoundPartialOrd<RelativeBound> for RelativeFiniteEndBound {
    fn bound_partial_cmp(&self, other: &RelativeBound) -> Option<BoundOrdering> {
        match other {
            RelativeBound::Start(start) => self.bound_partial_cmp(start),
            RelativeBound::End(end) => self.bound_partial_cmp(end),
        }
    }
}

impl From<RelativeFiniteBoundPosition> for RelativeFiniteEndBound {
    fn from(value: RelativeFiniteBoundPosition) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

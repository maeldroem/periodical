//! Relative finite start bound
//!
//! Represents the finite start bound of an relative interval.
//! If you need to represent infinity, see [`RelativeStartBound`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapAmbiguity};
use crate::intervals::relative::{
    RelativeBound,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeFiniteBoundPosition,
    RelativeFiniteEndBound,
    RelativeStartBound,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeFiniteStartBound(pub(crate) RelativeFiniteBoundPosition);

impl RelativeFiniteStartBound {
    pub fn new(finite_bound_pos: RelativeFiniteBoundPosition) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> RelativeFiniteBoundPosition {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut RelativeFiniteBoundPosition {
        &mut self.0
    }

    pub fn to_start_bound(self) -> RelativeStartBound {
        RelativeStartBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> RelativeFiniteBound {
        RelativeFiniteBound::from(self)
    }

    pub fn to_bound(self) -> RelativeBound {
        RelativeBound::from(self)
    }

    pub fn opposite(self) -> RelativeFiniteEndBound {
        RelativeFiniteEndBound::new(RelativeFiniteBoundPosition::new_with_inclusivity(
            self.pos().offset(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for RelativeFiniteStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeFiniteStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.pos()
            .cmp(&other.pos())
            .then_with(|| match (self.pos().inclusivity(), other.pos().inclusivity()) {
                (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Less,
                (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Greater,
            })
    }
}

impl BoundEq for RelativeFiniteStartBound {
    fn bound_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl BoundEq<RelativeStartBound> for RelativeFiniteStartBound {
    fn bound_eq(&self, other: &RelativeStartBound) -> bool {
        other.finite().is_some_and(|finite_start| self.bound_eq(&finite_start))
    }
}

impl BoundEq<RelativeFiniteEndBound> for RelativeFiniteStartBound {
    fn bound_eq(&self, other: &RelativeFiniteEndBound) -> bool {
        let start_pos = self.pos();
        let end_pos = other.pos();

        start_pos.eq(&end_pos)
            && start_pos.inclusivity() == BoundInclusivity::Inclusive
            && end_pos.inclusivity() == BoundInclusivity::Inclusive
    }
}

impl BoundEq<RelativeEndBound> for RelativeFiniteStartBound {
    fn bound_eq(&self, other: &RelativeEndBound) -> bool {
        other.finite().is_some_and(|finite_end| self.bound_eq(&finite_end))
    }
}

impl BoundEq<RelativeFiniteBound> for RelativeFiniteStartBound {
    fn bound_eq(&self, other: &RelativeFiniteBound) -> bool {
        match other {
            RelativeFiniteBound::Start(finite_start) => self.bound_eq(finite_start),
            RelativeFiniteBound::End(finite_end) => self.bound_eq(finite_end),
        }
    }
}

impl BoundEq<RelativeBound> for RelativeFiniteStartBound {
    fn bound_eq(&self, other: &RelativeBound) -> bool {
        match other {
            RelativeBound::Start(start) => self.bound_eq(start),
            RelativeBound::End(end) => self.bound_eq(end),
        }
    }
}

impl BoundOrd for RelativeFiniteStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        let lhs_pos = self.pos();
        let rhs_pos = other.pos();

        match lhs_pos.cmp(&rhs_pos) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                lhs_pos.inclusivity(),
                rhs_pos.inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrdExtremaOps for RelativeFiniteStartBound {}

impl BoundOrd<RelativeStartBound> for RelativeFiniteStartBound {
    fn bound_cmp(&self, other: &RelativeStartBound) -> BoundOrdering {
        if let Some(finite_start) = other.finite() {
            self.bound_cmp(&finite_start)
        } else {
            BoundOrdering::Greater
        }
    }
}

impl BoundOrd<RelativeFiniteEndBound> for RelativeFiniteStartBound {
    fn bound_cmp(&self, other: &RelativeFiniteEndBound) -> BoundOrdering {
        let lhs_pos = self.pos();
        let rhs_pos = other.pos();

        match lhs_pos.cmp(&rhs_pos) {
            Ordering::Less => BoundOrdering::Less,
            Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                lhs_pos.inclusivity(),
                rhs_pos.inclusivity(),
            ))),
            Ordering::Greater => BoundOrdering::Greater,
        }
    }
}

impl BoundOrd<RelativeEndBound> for RelativeFiniteStartBound {
    fn bound_cmp(&self, other: &RelativeEndBound) -> BoundOrdering {
        match other {
            RelativeEndBound::Finite(finite_end) => self.bound_cmp(finite_end),
            RelativeEndBound::InfiniteFuture => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<RelativeFiniteBound> for RelativeFiniteStartBound {
    fn bound_cmp(&self, other: &RelativeFiniteBound) -> BoundOrdering {
        match other {
            RelativeFiniteBound::Start(finite_start) => self.bound_cmp(finite_start),
            RelativeFiniteBound::End(finite_end) => self.bound_cmp(finite_end),
        }
    }
}

impl BoundOrd<RelativeBound> for RelativeFiniteStartBound {
    fn bound_cmp(&self, other: &RelativeBound) -> BoundOrdering {
        match other {
            RelativeBound::Start(start) => self.bound_cmp(start),
            RelativeBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<RelativeFiniteBoundPosition> for RelativeFiniteStartBound {
    fn from(value: RelativeFiniteBoundPosition) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

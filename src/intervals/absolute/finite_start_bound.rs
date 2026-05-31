//! Absolute finite start bound
//!
//! Represents the finite start bound of an absolute interval.
//! If you need to represent infinity, see [`AbsoluteStartBound`].

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
    AbsoluteFiniteEndBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{BoundEq, BoundOrd, BoundOrdExtremaOps, BoundOrdering, BoundOverlapAmbiguity};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteFiniteStartBound(pub(crate) AbsoluteFiniteBoundPosition);

impl AbsoluteFiniteStartBound {
    pub fn new(finite_bound_pos: AbsoluteFiniteBoundPosition) -> Self {
        Self(finite_bound_pos)
    }

    pub fn pos(&self) -> AbsoluteFiniteBoundPosition {
        self.0
    }

    pub fn pos_mut(&mut self) -> &mut AbsoluteFiniteBoundPosition {
        &mut self.0
    }

    pub fn to_start_bound(self) -> AbsoluteStartBound {
        AbsoluteStartBound::Finite(self)
    }

    pub fn to_finite_bound(self) -> AbsoluteFiniteBound {
        AbsoluteFiniteBound::from(self)
    }

    pub fn to_bound(self) -> AbsoluteBound {
        AbsoluteBound::from(self)
    }

    pub fn opposite(self) -> AbsoluteFiniteEndBound {
        AbsoluteFiniteEndBound::new(AbsoluteFiniteBoundPosition::new_with_inclusivity(
            self.pos().time(),
            self.pos().inclusivity().opposite(),
        ))
    }
}

impl PartialOrd for AbsoluteFiniteStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteFiniteStartBound {
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

impl BoundEq for AbsoluteFiniteStartBound {
    fn bound_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl BoundEq<AbsoluteStartBound> for AbsoluteFiniteStartBound {
    fn bound_eq(&self, other: &AbsoluteStartBound) -> bool {
        other.finite().is_some_and(|finite_start| self.bound_eq(&finite_start))
    }
}

impl BoundEq<AbsoluteFiniteEndBound> for AbsoluteFiniteStartBound {
    fn bound_eq(&self, other: &AbsoluteFiniteEndBound) -> bool {
        let start_pos = self.pos();
        let end_pos = other.pos();

        start_pos.eq(&end_pos)
            && start_pos.inclusivity() == BoundInclusivity::Inclusive
            && end_pos.inclusivity() == BoundInclusivity::Inclusive
    }
}

impl BoundEq<AbsoluteEndBound> for AbsoluteFiniteStartBound {
    fn bound_eq(&self, other: &AbsoluteEndBound) -> bool {
        other.finite().is_some_and(|finite_end| self.bound_eq(&finite_end))
    }
}

impl BoundEq<AbsoluteFiniteBound> for AbsoluteFiniteStartBound {
    fn bound_eq(&self, other: &AbsoluteFiniteBound) -> bool {
        match other {
            AbsoluteFiniteBound::Start(finite_start) => self.bound_eq(finite_start),
            AbsoluteFiniteBound::End(finite_end) => self.bound_eq(finite_end),
        }
    }
}

impl BoundEq<AbsoluteBound> for AbsoluteFiniteStartBound {
    fn bound_eq(&self, other: &AbsoluteBound) -> bool {
        match other {
            AbsoluteBound::Start(start) => self.bound_eq(start),
            AbsoluteBound::End(end) => self.bound_eq(end),
        }
    }
}

impl BoundOrd for AbsoluteFiniteStartBound {
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

impl BoundOrdExtremaOps for AbsoluteFiniteStartBound {}

impl BoundOrd<AbsoluteStartBound> for AbsoluteFiniteStartBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        if let Some(finite_start) = other.finite() {
            self.bound_cmp(&finite_start)
        } else {
            BoundOrdering::Greater
        }
    }
}

impl BoundOrd<AbsoluteFiniteEndBound> for AbsoluteFiniteStartBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteEndBound) -> BoundOrdering {
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

impl BoundOrd<AbsoluteEndBound> for AbsoluteFiniteStartBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        match other {
            AbsoluteEndBound::Finite(finite_end) => self.bound_cmp(finite_end),
            AbsoluteEndBound::InfiniteFuture => BoundOrdering::Less,
        }
    }
}

impl BoundOrd<AbsoluteFiniteBound> for AbsoluteFiniteStartBound {
    fn bound_cmp(&self, other: &AbsoluteFiniteBound) -> BoundOrdering {
        match other {
            AbsoluteFiniteBound::Start(finite_start) => self.bound_cmp(finite_start),
            AbsoluteFiniteBound::End(finite_end) => self.bound_cmp(finite_end),
        }
    }
}

impl BoundOrd<AbsoluteBound> for AbsoluteFiniteStartBound {
    fn bound_cmp(&self, other: &AbsoluteBound) -> BoundOrdering {
        match other {
            AbsoluteBound::Start(start) => self.bound_cmp(start),
            AbsoluteBound::End(end) => self.bound_cmp(end),
        }
    }
}

impl From<AbsoluteFiniteBoundPosition> for AbsoluteFiniteStartBound {
    fn from(value: AbsoluteFiniteBoundPosition) -> Self {
        Self::new(value)
    }
}

// TODO: impl TryFrom for FiniteBound and Bound

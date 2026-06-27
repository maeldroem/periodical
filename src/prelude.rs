//! Global prelude
//!
//! Import it with a wildcard, i.e. `use periodical::prelude::*;`, in order to
//! bring common traits into scope and import common structures.

pub use crate::intervals::absolute::{
    AbsBound,
    AbsBoundPair,
    AbsInterval,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
pub use crate::intervals::meta::{
    HasBoundExtremality,
    HasBoundInclusivity,
    HasDuration,
    HasIntervalType,
    HasIntervalTypeWithRel,
    HasOpeningDirection,
    HasOpenness,
    HasRelativity,
    IsEmpty,
};
pub use crate::intervals::ops::abridge::Abridgable;
pub use crate::intervals::ops::bound_cmp::{BoundEq, BoundOrd, BoundOrdExtremaOps};
pub use crate::intervals::ops::bound_containment::CanPositionBoundContainment;
pub use crate::intervals::ops::complement::Complementable;
pub use crate::intervals::ops::cut::{CutResult, CutType, Cuttable};
pub use crate::intervals::ops::extend::Extensible;
pub use crate::intervals::ops::fill_gap::GapFillable;
pub use crate::intervals::ops::grow::{GrowableEndBound, GrowableStartBound};
pub use crate::intervals::ops::overlap::{
    CanPositionOverlap,
    DEFAULT_OVERLAP_RULES,
    DisambiguatedOverlapPosition,
    OverlapPosition,
    OverlapRule,
    OverlapRuleSet,
};
pub use crate::intervals::ops::point_containment::{
    CanPositionPointContainment,
    DEFAULT_POINT_CONTAINMENT_RULES,
    DisambiguatedPointContainmentPosition,
    PointContainmentPosition,
    PointContainmentRule,
    PointContainmentRuleSet,
};
pub use crate::intervals::ops::precision::PreciseAbsInterval;
pub use crate::intervals::ops::relativity_conversion::{ToAbsolute, ToRelative};
pub use crate::intervals::ops::remove_overlap::{OverlapRemovable, OverlapRemovalResult};
pub use crate::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
pub use crate::intervals::ops::set_ops::{Differentiable, Intersectable, SymmetricallyDifferentiable, Unitable};
pub use crate::intervals::ops::shrink::{ShrinkableEndBound, ShrinkableStartBound};
pub use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBound,
    RelBoundPair,
    RelInterval,
};
pub use crate::intervals::special::{EmptyInterval, UnboundedInterval};
pub use crate::iter::intervals::bounds::{AbsBoundsIteratorDispatcher, RelBoundsIteratorDispatcher};
pub use crate::iter::intervals::complement::ComplementIteratorDispatcher;
pub use crate::iter::intervals::layered_bounds::{
    LayeredAbsBounds,
    LayeredBoundsState,
    LayeredBoundsStateChangeAtAbsBound,
    LayeredBoundsStateChangeAtRelBound,
    LayeredRelBounds,
};
pub use crate::iter::intervals::layered_bounds_set_ops::{
    LayeredAbsBoundsDifferenceIteratorDispatcher,
    LayeredAbsBoundsIntersectionIteratorDispatcher,
    LayeredAbsBoundsSymmetricDifferenceIteratorDispatcher,
    LayeredAbsBoundsUnionIteratorDispatcher,
    LayeredRelBoundsDifferenceIteratorDispatcher,
    LayeredRelBoundsIntersectionIteratorDispatcher,
    LayeredRelBoundsSymmetricDifferenceIteratorDispatcher,
    LayeredRelBoundsUnionIteratorDispatcher,
};
pub use crate::iter::intervals::remove_empty::RemoveEmptyIntervalsIteratorDispatcher;
pub use crate::iter::intervals::set_ops::{
    AccumulativeUnionIteratorDispatcher,
    AccumulativeUnionWithIteratorDispatcher,
    PeerDifferenceIteratorDispatcher,
    PeerDifferenceWithIteratorDispatcher,
    PeerIntersectionIteratorDispatcher,
    PeerIntersectionWithIteratorDispatcher,
    PeerSymmetricDifferenceIteratorDispatcher,
    PeerSymmetricDifferenceWithIteratorDispatcher,
    PeerUnionIteratorDispatcher,
    PeerUnionWithIteratorDispatcher,
};
pub use crate::iter::intervals::united_bounds::{AbsUnitedBoundsIter, RelUnitedBoundsIter};

//! Global prelude
//!
//! Import it with a wildcard, i.e. `use periodical::prelude::*;`, in order to bring common traits into scope
//! and import common structures.

pub use crate::intervals::absolute::{
    AbsoluteBound, AbsoluteBounds, AbsoluteInterval, BoundedAbsoluteInterval, EmptiableAbsoluteBounds,
    HalfBoundedAbsoluteInterval, HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
pub use crate::intervals::meta::{Emptiable, HasBoundInclusivity, HasDuration, HasOpenness, HasRelativity};
pub use crate::intervals::ops::abridge::Abridgable;
pub use crate::intervals::ops::bound_containment::CanPositionBoundContainment;
pub use crate::intervals::ops::bound_ord::PartialBoundOrd;
pub use crate::intervals::ops::complement::Complementable;
pub use crate::intervals::ops::cut::{CutResult, CutType, Cuttable};
pub use crate::intervals::ops::extend::Extensible;
pub use crate::intervals::ops::fill_gap::GapFillable;
pub use crate::intervals::ops::grow::{GrowableEndBound, GrowableStartBound};
pub use crate::intervals::ops::overlap::{
    CanPositionOverlap, DEFAULT_OVERLAP_RULES, DisambiguatedOverlapPosition, OverlapPosition, OverlapRule,
    OverlapRuleSet,
};
pub use crate::intervals::ops::point_containment::{
    CanPositionPointContainment, DEFAULT_POINT_CONTAINMENT_RULES, DisambiguatedPointContainmentPosition,
    PointContainmentPosition, PointContainmentRule, PointContainmentRuleSet,
};
pub use crate::intervals::ops::precision::PreciseAbsoluteInterval;
pub use crate::intervals::ops::relativity_conversion::{ToAbsolute, ToRelative};
pub use crate::intervals::ops::remove_overlap::{OverlapRemovable, OverlapRemovalResult};
pub use crate::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
pub use crate::intervals::ops::set_ops::{Differentiable, Intersectable, SymmetricallyDifferentiable, Unitable};
pub use crate::intervals::ops::shrink::{ShrinkableEndBound, ShrinkableStartBound};
pub use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBounds, HalfBoundedRelativeInterval, HasEmptiableRelativeBounds,
    HasRelativeBounds, RelativeBound, RelativeBounds, RelativeInterval,
};
pub use crate::intervals::special::{EmptyInterval, UnboundedInterval};
pub use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};
pub use crate::iter::intervals::complement::ComplementIteratorDispatcher;
pub use crate::iter::intervals::layered_bounds::{
    LayeredAbsoluteBounds, LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound,
    LayeredBoundsStateChangeAtRelativeBound, LayeredRelativeBounds,
};
pub use crate::iter::intervals::layered_bounds_set_ops::{
    LayeredAbsoluteBoundsDifferenceIteratorDispatcher, LayeredAbsoluteBoundsIntersectionIteratorDispatcher,
    LayeredAbsoluteBoundsSymmetricDifferenceIteratorDispatcher, LayeredAbsoluteBoundsUnionIteratorDispatcher,
    LayeredRelativeBoundsDifferenceIteratorDispatcher, LayeredRelativeBoundsIntersectionIteratorDispatcher,
    LayeredRelativeBoundsSymmetricDifferenceIteratorDispatcher, LayeredRelativeBoundsUnionIteratorDispatcher,
};
pub use crate::iter::intervals::remove_empty::RemoveEmptyIntervalsIteratorDispatcher;
pub use crate::iter::intervals::set_ops::{
    AccumulativeUnionIteratorDispatcher, AccumulativeUnionWithIteratorDispatcher, PeerDifferenceIteratorDispatcher,
    PeerDifferenceWithIteratorDispatcher, PeerIntersectionIteratorDispatcher, PeerIntersectionWithIteratorDispatcher,
    PeerSymmetricDifferenceIteratorDispatcher, PeerSymmetricDifferenceWithIteratorDispatcher,
    PeerUnionIteratorDispatcher, PeerUnionWithIteratorDispatcher,
};
pub use crate::iter::intervals::united_bounds::{AbsoluteUnitedBoundsIter, RelativeUnitedBoundsIter};

//! Interval extension up to another interval
//!
//! Extends an interval up to another. The process takes the lowest start bound
//! of the two intervals and the highest end bound of the two intervals, then
//! creates a new interval spanning those two points.
//!
//! Regarding bound inclusivity, for each point we will get the bound
//! inclusivity of the interval from which the point was taken. If they were
//! equal, we choose the most inclusive bound.
//!
//! # Examples

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

macro_rules! extensible_impl {
    (implementor => $implementor:ty, rhs => [$($rhs:ty),*$(,)?], output => clone rhs $(,)?) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $rhs;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    rhs.clone()
                }
            }
        )*
    };
    (implementor => $implementor:ty, rhs => [$($rhs:ty),*$(,)?], output => clone lhs $(,)?) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = Self;

                fn extend(&self, _rhs: &$rhs) -> Self::Output {
                    self.clone()
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        absolute,
        (non_emptiable, non_emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(extend_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()))
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        absolute,
        (non_emptiable, emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(extend_abs_bound_pair_with_emptiable_abs_bound_pair(
                        &self.abs_bound_pair(),
                        &rhs.emptiable_abs_bound_pair()
                    ))
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        absolute,
        (emptiable, non_emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    // Commutative operation, so OK to use RHS as LHS
                    Self::Output::from(extend_abs_bound_pair_with_emptiable_abs_bound_pair(
                        &rhs.abs_bound_pair(),
                        &self.emptiable_abs_bound_pair()
                    ))
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        absolute,
        (emptiable, emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(extend_emptiable_abs_bound_pair(
                        &self.emptiable_abs_bound_pair(),
                        &rhs.emptiable_abs_bound_pair()
                    ))
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        relative,
        (non_emptiable, non_emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(extend_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()))
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        relative,
        (non_emptiable, emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(extend_rel_bound_pair_with_emptiable_rel_bound_pair(
                        &self.rel_bound_pair(),
                        &rhs.emptiable_rel_bound_pair()
                    ))
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        relative,
        (emptiable, non_emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    // Commutative operation, so OK to use RHS as LHS
                    Self::Output::from(extend_rel_bound_pair_with_emptiable_rel_bound_pair(
                        &rhs.rel_bound_pair(),
                        &self.emptiable_rel_bound_pair()
                    ))
                }
            }
        )*
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        relative,
        (emptiable, emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(extend_emptiable_rel_bound_pair(
                        &self.emptiable_rel_bound_pair(),
                        &rhs.emptiable_rel_bound_pair()
                    ))
                }
            }
        )*
    };
}

/// Capacity to extend an interval up to another
///
/// Extends an interval up to another. The process takes the lowest start bound
/// of the two intervals and the highest end bound of the two intervals, then
/// creates a new interval spanning those two points.
///
/// Regarding bound inclusivity, for each point we will get the bound
/// inclusivity of the interval from which the point was taken. If they were
/// equal, we choose the most inclusive bound.
pub trait Extensible<Rhs = Self> {
    /// Output type
    type Output;

    /// Creates an extended interval from the current one and given one
    ///
    /// Extends an interval up to another. The process takes the lowest start
    /// bound of the two intervals and the highest end bound of the two
    /// intervals, then creates a new interval spanning those two points.
    ///
    /// Regarding bound inclusivity, for each point we will get the bound
    /// inclusivity of the interval from which the point was taken. If they
    /// were equal, we choose the most inclusive bound.
    ///
    /// If both intervals are empty, the method just returns an empty interval.
    ///
    /// If one of the intervals is empty, the method just return a clone of the
    /// other non-empty interval.
    ///
    /// # Examples
    #[must_use]
    fn extend(&self, rhs: &Rhs) -> Self::Output;
}

// extensible_impl!(
//     implementor => AbsBoundPair,
//     rhs => [AbsBoundPair],
//     output => AbsBoundPair,
//     absolute,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => AbsBoundPair,
//     rhs => [EmptiableAbsBoundPair],
//     output => AbsBoundPair,
//     absolute,
//     (non_emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableAbsBoundPair,
//     rhs => [AbsBoundPair],
//     output => AbsBoundPair,
//     absolute,
//     (emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableAbsBoundPair,
//     rhs => [EmptiableAbsBoundPair],
//     output => EmptiableAbsBoundPair,
//     absolute,
//     (emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => AbsInterval,
//     rhs => [AbsInterval],
//     output => AbsInterval,
//     absolute,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => AbsInterval,
//     rhs => [EmptiableAbsInterval],
//     output => AbsInterval,
//     absolute,
//     (non_emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableAbsInterval,
//     rhs => [AbsInterval],
//     output => AbsInterval,
//     absolute,
//     (emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableAbsInterval,
//     rhs => [EmptiableAbsInterval],
//     output => EmptiableAbsInterval,
//     absolute,
//     (emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => BoundedAbsInterval,
//     rhs => [BoundedAbsInterval],
//     output => BoundedAbsInterval,
//     absolute,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => BoundedAbsInterval,
//     rhs => [HalfBoundedAbsInterval],
//     output => HalfBoundedAbsInterval,
//     absolute,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => BoundedAbsInterval,
//     rhs => [UnboundedInterval],
//     output => clone rhs,
// );
// extensible_impl!(
//     implementor => BoundedAbsInterval,
//     rhs => [EmptyInterval],
//     output => clone lhs,
// );
// extensible_impl!(
//     implementor => HalfBoundedAbsInterval,
//     rhs => [BoundedAbsInterval],
//     output => HalfBoundedAbsInterval,
//     absolute,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => HalfBoundedAbsInterval,
//     rhs => [HalfBoundedAbsInterval],
//     output => AbsInterval,
//     absolute,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => HalfBoundedAbsInterval,
//     rhs => [UnboundedInterval],
//     output => clone rhs,
// );
// extensible_impl!(
//     implementor => HalfBoundedAbsInterval,
//     rhs => [EmptyInterval],
//     output => clone lhs,
// );

// extensible_impl!(
//     implementor => RelBoundPair,
//     rhs => [RelBoundPair],
//     output => RelBoundPair,
//     relative,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => RelBoundPair,
//     rhs => [EmptiableRelBoundPair],
//     output => RelBoundPair,
//     relative,
//     (non_emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableRelBoundPair,
//     rhs => [RelBoundPair],
//     output => RelBoundPair,
//     relative,
//     (emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableRelBoundPair,
//     rhs => [EmptiableRelBoundPair],
//     output => EmptiableRelBoundPair,
//     relative,
//     (emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => RelInterval,
//     rhs => [RelInterval],
//     output => RelInterval,
//     relative,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => RelInterval,
//     rhs => [EmptiableRelInterval],
//     output => RelInterval,
//     relative,
//     (non_emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableRelInterval,
//     rhs => [RelInterval],
//     output => RelInterval,
//     relative,
//     (emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => EmptiableRelInterval,
//     rhs => [EmptiableRelInterval],
//     output => EmptiableRelInterval,
//     relative,
//     (emptiable, emptiable),
// );
// extensible_impl!(
//     implementor => BoundedRelInterval,
//     rhs => [BoundedRelInterval],
//     output => BoundedRelInterval,
//     relative,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => BoundedRelInterval,
//     rhs => [HalfBoundedRelInterval],
//     output => HalfBoundedRelInterval,
//     relative,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => BoundedRelInterval,
//     rhs => [UnboundedInterval],
//     output => clone rhs,
// );
// extensible_impl!(
//     implementor => BoundedRelInterval,
//     rhs => [EmptyInterval],
//     output => clone lhs,
// );
// extensible_impl!(
//     implementor => HalfBoundedRelInterval,
//     rhs => [BoundedRelInterval],
//     output => HalfBoundedRelInterval,
//     relative,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => HalfBoundedRelInterval,
//     rhs => [HalfBoundedRelInterval],
//     output => RelInterval,
//     relative,
//     (non_emptiable, non_emptiable),
// );
// extensible_impl!(
//     implementor => HalfBoundedRelInterval,
//     rhs => [UnboundedInterval],
//     output => clone rhs,
// );
// extensible_impl!(
//     implementor => HalfBoundedRelInterval,
//     rhs => [EmptyInterval],
//     output => clone lhs,
// );

// extensible_impl!(
//     implementor => UnboundedInterval,
//     rhs => [
//         BoundedAbsInterval,
//         HalfBoundedAbsInterval,
//         BoundedRelInterval,
//         HalfBoundedRelInterval,
//         UnboundedInterval,
//         EmptyInterval,
//     ],
//     output => clone lhs,
// );
// extensible_impl!(
//     implementor => EmptyInterval,
//     rhs => [
//         BoundedAbsInterval,
//         HalfBoundedAbsInterval,
//         BoundedRelInterval,
//         HalfBoundedRelInterval,
//         UnboundedInterval,
//         EmptyInterval,
//     ],
//     output => clone rhs,
// );

/// Extends two [`AbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bound_pair(lhs_bound_pair: &AbsBoundPair, rhs_bound_pair: &AbsBoundPair) -> AbsBoundPair {
    let new_start_bound =
        match (lhs_bound_pair.abs_start(), rhs_bound_pair.abs_start()) {
            (bound @ AbsStartBound::InfinitePast, _) | (_, bound @ AbsStartBound::InfinitePast) => bound,
            (lhs_bound @ AbsStartBound::Finite(..), rhs_bound @ AbsStartBound::Finite(..)) => {
                if lhs_bound <= rhs_bound { lhs_bound } else { rhs_bound }
            },
        };

    let new_end_bound = match (lhs_bound_pair.abs_end(), rhs_bound_pair.abs_end()) {
        (bound @ AbsEndBound::InfiniteFuture, _) | (_, bound @ AbsEndBound::InfiniteFuture) => bound,
        (lhs_bound @ AbsEndBound::Finite(..), rhs_bound @ AbsEndBound::Finite(..)) => {
            if lhs_bound >= rhs_bound {
                lhs_bound
            } else {
                rhs_bound
            }
        },
    };

    AbsBoundPair::new(new_start_bound, new_end_bound)
}

/// Extends an [`AbsBoundPair`] with an [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bound_pair_with_emptiable_abs_bound_pair(
    lhs_bound_pair: &AbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> AbsBoundPair {
    let EmptiableAbsBoundPair::Bound(rhs_non_empty_bound_pair) = rhs_bound_pair else {
        return lhs_bound_pair.clone();
    };

    extend_abs_bound_pair(lhs_bound_pair, rhs_non_empty_bound_pair)
}

/// Extends two [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_emptiable_abs_bound_pair(
    lhs_bound_pair: &EmptiableAbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> EmptiableAbsBoundPair {
    todo!("fix");
    // match (lhs_bound_pair, rhs_bound_pair) {
    //     (EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Empty) => EmptiableAbsBoundPair::Empty,
    //     (EmptiableAbsBoundPair::Empty, bound @ EmptiableAbsBoundPair::Bound(..))
    //     | (bound @ EmptiableAbsBoundPair::Bound(..), EmptiableAbsBoundPair::Empty) => bound.clone(),
    //     (EmptiableAbsBoundPair::Bound(lhs_bound_pair), EmptiableAbsBoundPair::Bound(rhs_bound_pair)) => {
    //         EmptiableAbsBoundPair::Bound(lhs_bound_pair.extend(rhs_bound_pair))
    //     },
    // }
}

/// Extends two [`BoundedAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bounded_interval_pair(
    lhs_bounded: &BoundedAbsInterval,
    rhs_bounded: &BoundedAbsInterval,
) -> BoundedAbsInterval {
    let Some(lowest_start) = lhs_bounded.abs_start().min(rhs_bounded.abs_start()).finite() else {
        unreachable!("A bounded interval's start bound is always finite.");
    };
    let Some(highest_end) = rhs_bounded.abs_end().max(rhs_bounded.abs_end()).finite() else {
        unreachable!("A bounded interval's end bound is always finite.");
    };

    BoundedAbsInterval::from((lowest_start, highest_end))
}

// TODO: Same than extend_abs_bounded_interval_pair but for (bounded, half_bounded) and (half_bounded, half_bounded)

/// Extends two [`RelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bound_pair(lhs_bound_pair: &RelBoundPair, rhs_bound_pair: &RelBoundPair) -> RelBoundPair {
    let new_start_bound =
        match (lhs_bound_pair.rel_start(), rhs_bound_pair.rel_start()) {
            (bound @ RelStartBound::InfinitePast, _) | (_, bound @ RelStartBound::InfinitePast) => bound,
            (lhs_bound @ RelStartBound::Finite(..), rhs_bound @ RelStartBound::Finite(..)) => {
                if lhs_bound <= rhs_bound { lhs_bound } else { rhs_bound }
            },
        };

    let new_end_bound = match (lhs_bound_pair.rel_end(), rhs_bound_pair.rel_end()) {
        (bound @ RelEndBound::InfiniteFuture, _) | (_, bound @ RelEndBound::InfiniteFuture) => bound,
        (lhs_bound @ RelEndBound::Finite(..), rhs_bound @ RelEndBound::Finite(..)) => {
            if lhs_bound >= rhs_bound {
                lhs_bound
            } else {
                rhs_bound
            }
        },
    };

    RelBoundPair::new(new_start_bound, new_end_bound)
}

/// Extends an [`RelBoundPair`] with an [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bound_pair_with_emptiable_rel_bound_pair(
    lhs_bound_pair: &RelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> RelBoundPair {
    let EmptiableRelBoundPair::Bound(rhs_non_empty_bound_pair) = rhs_bound_pair else {
        return lhs_bound_pair.clone();
    };

    extend_rel_bound_pair(lhs_bound_pair, rhs_non_empty_bound_pair)
}

/// Extends two [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_emptiable_rel_bound_pair(
    lhs_bound_pair: &EmptiableRelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> EmptiableRelBoundPair {
    todo!("fix");
    // match (lhs_bound_pair, rhs_bound_pair) {
    //     (EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Empty) => EmptiableRelBoundPair::Empty,
    //     (EmptiableRelBoundPair::Empty, bound @ EmptiableRelBoundPair::Bound(..))
    //     | (bound @ EmptiableRelBoundPair::Bound(..), EmptiableRelBoundPair::Empty) => bound.clone(),
    //     (EmptiableRelBoundPair::Bound(lhs_bound_pair), EmptiableRelBoundPair::Bound(rhs_bound_pair)) => {
    //         EmptiableRelBoundPair::Bound(lhs_bound_pair.extend(rhs_bound_pair))
    //     },
    // }
}

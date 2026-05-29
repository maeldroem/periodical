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
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
//! # use periodical::intervals::ops::Extensible;
//! let first_interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 12:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let second_interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 14:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBoundPosition::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! assert_eq!(
//!     first_interval.extend(&second_interval),
//!     AbsoluteBoundPair::new(
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 08:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_start_bound(),
//!         AbsoluteFiniteBoundPosition::new(
//!             "2025-01-01 16:00:00[Europe/Oslo]"
//!                 .parse::<Zoned>()?
//!                 .timestamp(),
//!         )
//!         .to_end_bound(),
//!     ),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
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
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::ops::Extensible;
    /// let first_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 12:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// let second_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 14:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     first_interval.extend(&second_interval),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn extend(&self, rhs: &Rhs) -> Self::Output;
}

extensible_impl!(
    implementor => AbsoluteBoundPair,
    rhs => [AbsoluteBoundPair],
    output => AbsoluteBoundPair,
    absolute,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => AbsoluteBoundPair,
    rhs => [EmptiableAbsoluteBoundPair],
    output => AbsoluteBoundPair,
    absolute,
    (non_emptiable, emptiable),
);
extensible_impl!(
    implementor => EmptiableAbsoluteBoundPair,
    rhs => [AbsoluteBoundPair],
    output => AbsoluteBoundPair,
    absolute,
    (emptiable, non_emptiable),
);
extensible_impl!(
    implementor => EmptiableAbsoluteBoundPair,
    rhs => [EmptiableAbsoluteBoundPair],
    output => EmptiableAbsoluteBoundPair,
    absolute,
    (emptiable, emptiable),
);
extensible_impl!(
    implementor => AbsoluteInterval,
    rhs => [AbsoluteInterval],
    output => AbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => AbsoluteInterval,
    rhs => [EmptiableAbsoluteInterval],
    output => AbsoluteInterval,
    absolute,
    (non_emptiable, emptiable),
);
extensible_impl!(
    implementor => EmptiableAbsoluteInterval,
    rhs => [AbsoluteInterval],
    output => AbsoluteInterval,
    absolute,
    (emptiable, non_emptiable),
);
extensible_impl!(
    implementor => EmptiableAbsoluteInterval,
    rhs => [EmptiableAbsoluteInterval],
    output => EmptiableAbsoluteInterval,
    absolute,
    (emptiable, emptiable),
);
extensible_impl!(
    implementor => BoundedAbsoluteInterval,
    rhs => [BoundedAbsoluteInterval],
    output => BoundedAbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => BoundedAbsoluteInterval,
    rhs => [HalfBoundedAbsoluteInterval],
    output => HalfBoundedAbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => BoundedAbsoluteInterval,
    rhs => [UnboundedInterval],
    output => clone rhs,
);
extensible_impl!(
    implementor => BoundedAbsoluteInterval,
    rhs => [EmptyInterval],
    output => clone lhs,
);
extensible_impl!(
    implementor => HalfBoundedAbsoluteInterval,
    rhs => [BoundedAbsoluteInterval],
    output => HalfBoundedAbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => HalfBoundedAbsoluteInterval,
    rhs => [HalfBoundedAbsoluteInterval],
    output => AbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => HalfBoundedAbsoluteInterval,
    rhs => [UnboundedInterval],
    output => clone rhs,
);
extensible_impl!(
    implementor => HalfBoundedAbsoluteInterval,
    rhs => [EmptyInterval],
    output => clone lhs,
);

extensible_impl!(
    implementor => RelativeBoundPair,
    rhs => [RelativeBoundPair],
    output => RelativeBoundPair,
    relative,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => RelativeBoundPair,
    rhs => [EmptiableRelativeBoundPair],
    output => RelativeBoundPair,
    relative,
    (non_emptiable, emptiable),
);
extensible_impl!(
    implementor => EmptiableRelativeBoundPair,
    rhs => [RelativeBoundPair],
    output => RelativeBoundPair,
    relative,
    (emptiable, non_emptiable),
);
extensible_impl!(
    implementor => EmptiableRelativeBoundPair,
    rhs => [EmptiableRelativeBoundPair],
    output => EmptiableRelativeBoundPair,
    relative,
    (emptiable, emptiable),
);
extensible_impl!(
    implementor => RelativeInterval,
    rhs => [RelativeInterval],
    output => RelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => RelativeInterval,
    rhs => [EmptiableRelativeInterval],
    output => RelativeInterval,
    relative,
    (non_emptiable, emptiable),
);
extensible_impl!(
    implementor => EmptiableRelativeInterval,
    rhs => [RelativeInterval],
    output => RelativeInterval,
    relative,
    (emptiable, non_emptiable),
);
extensible_impl!(
    implementor => EmptiableRelativeInterval,
    rhs => [EmptiableRelativeInterval],
    output => EmptiableRelativeInterval,
    relative,
    (emptiable, emptiable),
);
extensible_impl!(
    implementor => BoundedRelativeInterval,
    rhs => [BoundedRelativeInterval],
    output => BoundedRelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => BoundedRelativeInterval,
    rhs => [HalfBoundedRelativeInterval],
    output => HalfBoundedRelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => BoundedRelativeInterval,
    rhs => [UnboundedInterval],
    output => clone rhs,
);
extensible_impl!(
    implementor => BoundedRelativeInterval,
    rhs => [EmptyInterval],
    output => clone lhs,
);
extensible_impl!(
    implementor => HalfBoundedRelativeInterval,
    rhs => [BoundedRelativeInterval],
    output => HalfBoundedRelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => HalfBoundedRelativeInterval,
    rhs => [HalfBoundedRelativeInterval],
    output => RelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
extensible_impl!(
    implementor => HalfBoundedRelativeInterval,
    rhs => [UnboundedInterval],
    output => clone rhs,
);
extensible_impl!(
    implementor => HalfBoundedRelativeInterval,
    rhs => [EmptyInterval],
    output => clone lhs,
);

extensible_impl!(
    implementor => UnboundedInterval,
    rhs => [
        BoundedAbsoluteInterval,
        HalfBoundedAbsoluteInterval,
        BoundedRelativeInterval,
        HalfBoundedRelativeInterval,
        UnboundedInterval,
        EmptyInterval,
    ],
    output => clone lhs,
);
extensible_impl!(
    implementor => EmptyInterval,
    rhs => [
        BoundedAbsoluteInterval,
        HalfBoundedAbsoluteInterval,
        BoundedRelativeInterval,
        HalfBoundedRelativeInterval,
        UnboundedInterval,
        EmptyInterval,
    ],
    output => clone rhs,
);

/// Extends two [`AbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bound_pair(
    lhs_bound_pair: &AbsoluteBoundPair,
    rhs_bound_pair: &AbsoluteBoundPair,
) -> AbsoluteBoundPair {
    let new_start_bound = match (lhs_bound_pair.abs_start(), rhs_bound_pair.abs_start()) {
        (bound @ AbsoluteStartBound::InfinitePast, _) | (_, bound @ AbsoluteStartBound::InfinitePast) => bound,
        (lhs_bound @ AbsoluteStartBound::Finite(..), rhs_bound @ AbsoluteStartBound::Finite(..)) => {
            if lhs_bound <= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    let new_end_bound = match (lhs_bound_pair.abs_end(), rhs_bound_pair.abs_end()) {
        (bound @ AbsoluteEndBound::InfiniteFuture, _) | (_, bound @ AbsoluteEndBound::InfiniteFuture) => bound,
        (lhs_bound @ AbsoluteEndBound::Finite(..), rhs_bound @ AbsoluteEndBound::Finite(..)) => {
            if lhs_bound >= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    AbsoluteBoundPair::new(new_start_bound, new_end_bound)
}

/// Extends an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bound_pair_with_emptiable_abs_bound_pair(
    lhs_bound_pair: &AbsoluteBoundPair,
    rhs_bound_pair: &EmptiableAbsoluteBoundPair,
) -> AbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(rhs_non_empty_bound_pair) = rhs_bound_pair else {
        return lhs_bound_pair.clone();
    };

    extend_abs_bound_pair(lhs_bound_pair, rhs_non_empty_bound_pair)
}

/// Extends two [`EmptiableAbsoluteBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_emptiable_abs_bound_pair(
    lhs_bound_pair: &EmptiableAbsoluteBoundPair,
    rhs_bound_pair: &EmptiableAbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableAbsoluteBoundPair::Empty, EmptiableAbsoluteBoundPair::Empty) => EmptiableAbsoluteBoundPair::Empty,
        (EmptiableAbsoluteBoundPair::Empty, bound @ EmptiableAbsoluteBoundPair::Bound(..))
        | (bound @ EmptiableAbsoluteBoundPair::Bound(..), EmptiableAbsoluteBoundPair::Empty) => bound.clone(),
        (EmptiableAbsoluteBoundPair::Bound(lhs_bound_pair), EmptiableAbsoluteBoundPair::Bound(rhs_bound_pair)) => {
            EmptiableAbsoluteBoundPair::Bound(lhs_bound_pair.extend(rhs_bound_pair))
        },
    }
}

/// Extends two [`BoundedAbsoluteInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bounded_interval_pair(
    lhs_bounded: &BoundedAbsoluteInterval,
    rhs_bounded: &BoundedAbsoluteInterval,
) -> BoundedAbsoluteInterval {
    let Some(lowest_start) = lhs_bounded.abs_start().min(rhs_bounded.abs_start()).finite() else {
        unreachable!("A bounded interval's start bound is always finite.");
    };
    let Some(highest_end) = rhs_bounded.abs_end().max(rhs_bounded.abs_end()).finite() else {
        unreachable!("A bounded interval's end bound is always finite.");
    };

    BoundedAbsoluteInterval::from((lowest_start, highest_end))
}

// TODO: Same than extend_abs_bounded_interval_pair but for (bounded, half_bounded) and (half_bounded, half_bounded)

/// Extends two [`RelativeBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bound_pair(
    lhs_bound_pair: &RelativeBoundPair,
    rhs_bound_pair: &RelativeBoundPair,
) -> RelativeBoundPair {
    let new_start_bound = match (lhs_bound_pair.rel_start(), rhs_bound_pair.rel_start()) {
        (bound @ RelativeStartBound::InfinitePast, _) | (_, bound @ RelativeStartBound::InfinitePast) => bound,
        (lhs_bound @ RelativeStartBound::Finite(..), rhs_bound @ RelativeStartBound::Finite(..)) => {
            if lhs_bound <= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    let new_end_bound = match (lhs_bound_pair.rel_end(), rhs_bound_pair.rel_end()) {
        (bound @ RelativeEndBound::InfiniteFuture, _) | (_, bound @ RelativeEndBound::InfiniteFuture) => bound,
        (lhs_bound @ RelativeEndBound::Finite(..), rhs_bound @ RelativeEndBound::Finite(..)) => {
            if lhs_bound >= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    RelativeBoundPair::new(new_start_bound, new_end_bound)
}

/// Extends an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bound_pair_with_emptiable_rel_bound_pair(
    lhs_bound_pair: &RelativeBoundPair,
    rhs_bound_pair: &EmptiableRelativeBoundPair,
) -> RelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(rhs_non_empty_bound_pair) = rhs_bound_pair else {
        return lhs_bound_pair.clone();
    };

    extend_rel_bound_pair(lhs_bound_pair, rhs_non_empty_bound_pair)
}

/// Extends two [`EmptiableRelativeBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_emptiable_rel_bound_pair(
    lhs_bound_pair: &EmptiableRelativeBoundPair,
    rhs_bound_pair: &EmptiableRelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableRelativeBoundPair::Empty, EmptiableRelativeBoundPair::Empty) => EmptiableRelativeBoundPair::Empty,
        (EmptiableRelativeBoundPair::Empty, bound @ EmptiableRelativeBoundPair::Bound(..))
        | (bound @ EmptiableRelativeBoundPair::Bound(..), EmptiableRelativeBoundPair::Empty) => bound.clone(),
        (EmptiableRelativeBoundPair::Bound(lhs_bound_pair), EmptiableRelativeBoundPair::Bound(rhs_bound_pair)) => {
            EmptiableRelativeBoundPair::Bound(lhs_bound_pair.extend(rhs_bound_pair))
        },
    }
}

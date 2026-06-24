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
//! # use jiff::Timestamp;
//! # use periodical::intervals::ops::Extensible;
//! # use periodical::intervals::absolute::BoundedAbsInterval;
//! let x = BoundedAbsInterval::from_times(
//!     "2026-01-01 04:00:00Z".parse::<Timestamp>()?,
//!     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
//! );
//! let y = BoundedAbsInterval::from_times(
//!     "2026-01-01 12:00:00Z".parse::<Timestamp>()?,
//!     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
//! );
//!
//! assert_eq!(
//!     x.extend(&y),
//!     BoundedAbsInterval::from_times(
//!         "2026-01-01 04:00:00Z".parse::<Timestamp>()?,
//!         "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
//!     )
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsInterval,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::ops::{BoundOrdExtremaOps, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HalfBoundedToFutureRelInterval,
    HalfBoundedToPastRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelInterval,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

macro_rules! extensible_impl {
    () => {};

    (@select_method; $lhs:ident; $rhs:ident; abs; non_emptiable; non_emptiable) => {
        extend_abs_bound_pair(&$lhs.abs_bound_pair(), &$rhs.abs_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; non_emptiable; emptiable) => {
        extend_abs_bound_pair_with_emptiable_abs_bound_pair(&$lhs.abs_bound_pair(), &$rhs.emptiable_abs_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; emptiable; non_emptiable) => {
        extensible_impl!(@select_method; $rhs; $lhs; abs; non_emptiable; emptiable)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; emptiable; emptiable) => {
        extend_emptiable_abs_bound_pair(&$lhs.emptiable_abs_bound_pair(), &$rhs.emptiable_abs_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; bounded; bounded) => {
        extend_abs_bounded(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; bounded; hb_to_future) => {
        extend_abs_bounded_half_bounded_to_future(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; bounded; hb_to_past) => {
        extend_abs_bounded_half_bounded_to_past(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; bounded; half_bounded) => {
        extend_abs_bounded_half_bounded(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; hb_to_future; bounded) => {
        extensible_impl!(@select_method; $rhs; $lhs; abs; bounded; hb_to_future)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; hb_to_future; hb_to_future) => {
        extend_abs_half_bounded_to_future(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; hb_to_future; half_bounded) => {
        extend_abs_half_bounded(&$lhs.clone().to_half_bounded_interval(), &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; hb_to_past; bounded) => {
        extensible_impl!(@select_method; $rhs; $lhs; abs; bounded; hb_to_past)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; hb_to_past; hb_to_past) => {
        extend_abs_half_bounded_to_past(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; hb_to_past; half_bounded) => {
        extend_abs_half_bounded(&$lhs.clone().to_half_bounded_interval(), &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; half_bounded; bounded) => {
        extensible_impl!(@select_method; $rhs; $lhs; abs; bounded; half_bounded)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; half_bounded; hb_to_future) => {
        extend_abs_half_bounded(&$lhs, &$rhs.clone().to_half_bounded_interval())
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; half_bounded; hb_to_past) => {
        extend_abs_half_bounded(&$lhs, &$rhs.clone().to_half_bounded_interval())
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; half_bounded; half_bounded) => {
        extend_abs_half_bounded(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; non_emptiable; non_emptiable) => {
        extend_rel_bound_pair(&$lhs.rel_bound_pair(), &$rhs.rel_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; non_emptiable; emptiable) => {
        extend_rel_bound_pair_with_emptiable_rel_bound_pair(&$lhs.rel_bound_pair(), &$rhs.emptiable_rel_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; emptiable; non_emptiable) => {
        extensible_impl!(@select_method; $rhs; $lhs; rel; non_emptiable; emptiable)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; emptiable; emptiable) => {
        extend_emptiable_rel_bound_pair(&$lhs.emptiable_rel_bound_pair(), &$rhs.emptiable_rel_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; bounded; bounded) => {
        extend_rel_bounded(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; bounded; hb_to_future) => {
        extend_rel_bounded_half_bounded_to_future(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; bounded; hb_to_past) => {
        extend_rel_bounded_half_bounded_to_past(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; bounded; half_bounded) => {
        extend_rel_bounded_half_bounded(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; hb_to_future; bounded) => {
        extensible_impl!(@select_method; $rhs; $lhs; rel; bounded; hb_to_future)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; hb_to_future; hb_to_future) => {
        extend_rel_half_bounded_to_future(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; hb_to_future; half_bounded) => {
        extend_rel_half_bounded(&$lhs.clone().to_half_bounded_interval(), &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; hb_to_past; bounded) => {
        extensible_impl!(@select_method; $rhs; $lhs; rel; bounded; hb_to_past)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; hb_to_past; hb_to_past) => {
        extend_rel_half_bounded_to_past(&$lhs, &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; hb_to_past; half_bounded) => {
        extend_rel_half_bounded(&$lhs.clone().to_half_bounded_interval(), &$rhs)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; half_bounded; bounded) => {
        extensible_impl!(@select_method; $rhs; $lhs; rel; bounded; half_bounded)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; half_bounded; hb_to_future) => {
        extend_rel_half_bounded(&$lhs, &$rhs.clone().to_half_bounded_interval())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; half_bounded; hb_to_past) => {
        extend_rel_half_bounded(&$lhs, &$rhs.clone().to_half_bounded_interval())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; half_bounded; half_bounded) => {
        extend_rel_half_bounded(&$lhs, &$rhs)
    };

    // Syntax sucks a bit, but doing match arms of different custom syntax is not possible declaratively
    // and annoying to parse in a proc macro.
    (for $implementor:ty [map rhs] $(|)? $($rhs:ty)|+ => lhs.clone(); $($tail:tt)*) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $implementor;

                fn extend(&self, _rhs: &$rhs) -> Self::Output {
                    self.clone()
                }
            }
        )+

        extensible_impl!($($tail)*);
    };
    (for $implementor:ty [map rhs] $(|)? $($rhs:ty)|+ => rhs.clone(); $($tail:tt)*) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $rhs;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    rhs.clone()
                }
            }
        )+

        extensible_impl!($($tail)*);
    };
    (for $implementor:ty [map rhs] $(|)? $($rhs:ty)|+ => $output:ty [via] (
        $relativity:ident, $lhs_type:ident, $rhs_type:ident $(,)?
    ); $($tail:tt)*) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(extensible_impl!(@select_method; self; rhs; $relativity; $lhs_type; $rhs_type))
                }
            }
        )+

        extensible_impl!($($tail)*);
    };
    (for $implementor:ty [map rhs] $(|)? $($rhs:ty)|+ => $output:ty [always] $output_expr:expr; $($tail:tt)*) => {
        $(
            impl Extensible<$rhs> for $implementor {
                type Output = $output;

                fn extend(&self, _rhs: &$rhs) -> Self::Output {
                    $output_expr
                }
            }
        )+

        extensible_impl!($($tail)*);
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
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::ops::Extensible;
    /// # use periodical::intervals::absolute::BoundedAbsInterval;
    /// let x = BoundedAbsInterval::from_times(
    ///     "2026-01-01 04:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
    /// );
    /// let y = BoundedAbsInterval::from_times(
    ///     "2026-01-01 12:00:00Z".parse::<Timestamp>()?,
    ///     "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    /// );
    ///
    /// assert_eq!(
    ///     x.extend(&y),
    ///     BoundedAbsInterval::from_times(
    ///         "2026-01-01 04:00:00Z".parse::<Timestamp>()?,
    ///         "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
    ///     )
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn extend(&self, rhs: &Rhs) -> Self::Output;
}

extensible_impl!(
    // Absolute
    for AbsBoundPair [map rhs]
        AbsBoundPair => AbsBoundPair [via] (abs, non_emptiable, non_emptiable);
    for AbsBoundPair [map rhs]
        EmptiableAbsBoundPair => AbsBoundPair [via] (abs, non_emptiable, emptiable);

    for EmptiableAbsBoundPair [map rhs]
        AbsBoundPair => AbsBoundPair [via] (abs, emptiable, non_emptiable);
    for EmptiableAbsBoundPair [map rhs]
        EmptiableAbsBoundPair => EmptiableAbsBoundPair [via] (abs, emptiable, emptiable);

    for AbsInterval [map rhs]
        AbsInterval => AbsInterval [via] (abs, non_emptiable, non_emptiable);
    for AbsInterval [map rhs]
        EmptiableAbsInterval => AbsInterval [via] (abs, non_emptiable, emptiable);

    for EmptiableAbsInterval [map rhs]
        AbsInterval => AbsInterval [via] (abs, emptiable, non_emptiable);
    for EmptiableAbsInterval [map rhs]
        EmptiableAbsInterval => EmptiableAbsInterval [via] (abs, emptiable, emptiable);

    for BoundedAbsInterval [map rhs]
        BoundedAbsInterval => BoundedAbsInterval [via] (abs, bounded, bounded);
    for BoundedAbsInterval [map rhs]
        HalfBoundedToFutureAbsInterval => HalfBoundedToFutureAbsInterval [via] (abs, bounded, hb_to_future);
    for BoundedAbsInterval [map rhs]
        HalfBoundedToPastAbsInterval => HalfBoundedToPastAbsInterval [via] (abs, bounded, hb_to_past);
    for BoundedAbsInterval [map rhs]
        HalfBoundedAbsInterval => HalfBoundedAbsInterval [via] (abs, bounded, half_bounded);

    for HalfBoundedToFutureAbsInterval [map rhs]
        BoundedAbsInterval => HalfBoundedToFutureAbsInterval [via] (abs, hb_to_future, bounded);
    for HalfBoundedToFutureAbsInterval [map rhs]
        HalfBoundedToFutureAbsInterval => HalfBoundedToFutureAbsInterval [via] (abs, hb_to_future, hb_to_future);
    for HalfBoundedToFutureAbsInterval [map rhs]
        HalfBoundedToPastAbsInterval => UnboundedInterval [always] UnboundedInterval;
    for HalfBoundedToFutureAbsInterval [map rhs]
        HalfBoundedAbsInterval => AbsInterval [via] (abs, hb_to_future, half_bounded);

    for HalfBoundedToPastAbsInterval [map rhs]
        BoundedAbsInterval => HalfBoundedToPastAbsInterval [via] (abs, hb_to_past, bounded);
    for HalfBoundedToPastAbsInterval [map rhs]
        HalfBoundedToFutureAbsInterval => UnboundedInterval [always] UnboundedInterval;
    for HalfBoundedToPastAbsInterval [map rhs]
        HalfBoundedToPastAbsInterval => HalfBoundedToPastAbsInterval [via] (abs, hb_to_past, hb_to_past);
    for HalfBoundedToPastAbsInterval [map rhs]
        HalfBoundedAbsInterval => AbsInterval [via] (abs, hb_to_past, half_bounded);

    for HalfBoundedAbsInterval [map rhs]
        BoundedAbsInterval => HalfBoundedAbsInterval [via] (abs, half_bounded, bounded);
    for HalfBoundedAbsInterval [map rhs]
        HalfBoundedToFutureAbsInterval => AbsInterval [via] (abs, half_bounded, hb_to_future);
    for HalfBoundedAbsInterval [map rhs]
        HalfBoundedToPastAbsInterval => AbsInterval [via] (abs, half_bounded, hb_to_past);
    for HalfBoundedAbsInterval [map rhs]
        HalfBoundedAbsInterval => AbsInterval [via] (abs, half_bounded, half_bounded);

    // Relative
    for RelBoundPair [map rhs]
        RelBoundPair => RelBoundPair [via] (rel, non_emptiable, non_emptiable);
    for RelBoundPair [map rhs]
        EmptiableRelBoundPair => RelBoundPair [via] (rel, non_emptiable, emptiable);

    for EmptiableRelBoundPair [map rhs]
        RelBoundPair => RelBoundPair [via] (rel, emptiable, non_emptiable);
    for EmptiableRelBoundPair [map rhs]
        EmptiableRelBoundPair => EmptiableRelBoundPair [via] (rel, emptiable, emptiable);

    for RelInterval [map rhs]
        RelInterval => RelInterval [via] (rel, non_emptiable, non_emptiable);
    for RelInterval [map rhs]
        EmptiableRelInterval => RelInterval [via] (rel, non_emptiable, emptiable);

    for EmptiableRelInterval [map rhs]
        RelInterval => RelInterval [via] (rel, emptiable, non_emptiable);
    for EmptiableRelInterval [map rhs]
        EmptiableRelInterval => EmptiableRelInterval [via] (rel, emptiable, emptiable);

    for BoundedRelInterval [map rhs]
        BoundedRelInterval => BoundedRelInterval [via] (rel, bounded, bounded);
    for BoundedRelInterval [map rhs]
        HalfBoundedToFutureRelInterval => HalfBoundedToFutureRelInterval [via] (rel, bounded, hb_to_future);
    for BoundedRelInterval [map rhs]
        HalfBoundedToPastRelInterval => HalfBoundedToPastRelInterval [via] (rel, bounded, hb_to_past);
    for BoundedRelInterval [map rhs]
        HalfBoundedRelInterval => HalfBoundedRelInterval [via] (rel, bounded, half_bounded);

    for HalfBoundedToFutureRelInterval [map rhs]
        BoundedRelInterval => HalfBoundedToFutureRelInterval [via] (rel, hb_to_future, bounded);
    for HalfBoundedToFutureRelInterval [map rhs]
        HalfBoundedToFutureRelInterval => HalfBoundedToFutureRelInterval [via] (rel, hb_to_future, hb_to_future);
    for HalfBoundedToFutureRelInterval [map rhs]
        HalfBoundedToPastRelInterval => UnboundedInterval [always] UnboundedInterval;
    for HalfBoundedToFutureRelInterval [map rhs]
        HalfBoundedRelInterval => RelInterval [via] (rel, hb_to_future, half_bounded);

    for HalfBoundedToPastRelInterval [map rhs]
        BoundedRelInterval => HalfBoundedToPastRelInterval [via] (rel, hb_to_past, bounded);
    for HalfBoundedToPastRelInterval [map rhs]
        HalfBoundedToFutureRelInterval => UnboundedInterval [always] UnboundedInterval;
    for HalfBoundedToPastRelInterval [map rhs]
        HalfBoundedToPastRelInterval => HalfBoundedToPastRelInterval [via] (rel, hb_to_past, hb_to_past);
    for HalfBoundedToPastRelInterval [map rhs]
        HalfBoundedRelInterval => RelInterval [via] (rel, hb_to_past, half_bounded);

    for HalfBoundedRelInterval [map rhs]
        BoundedRelInterval => HalfBoundedRelInterval [via] (rel, half_bounded, bounded);
    for HalfBoundedRelInterval [map rhs]
        HalfBoundedToFutureRelInterval => RelInterval [via] (rel, half_bounded, hb_to_future);
    for HalfBoundedRelInterval [map rhs]
        HalfBoundedToPastRelInterval => RelInterval [via] (rel, half_bounded, hb_to_past);
    for HalfBoundedRelInterval [map rhs]
        HalfBoundedRelInterval => RelInterval [via] (rel, half_bounded, half_bounded);

    // Special
    for UnboundedInterval [map rhs]
        BoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval | HalfBoundedAbsInterval
        | BoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval | HalfBoundedRelInterval
        | UnboundedInterval | EmptyInterval => lhs.clone();
    for EmptyInterval [map rhs]
        BoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval | HalfBoundedAbsInterval
        | BoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval | HalfBoundedRelInterval
        | UnboundedInterval => rhs.clone();
    for EmptyInterval [map rhs] EmptyInterval => lhs.clone();
);

/// Extends two [`AbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bound_pair(lhs_bound_pair: &AbsBoundPair, rhs_bound_pair: &AbsBoundPair) -> AbsBoundPair {
    let min_start = lhs_bound_pair
        .start()
        .bound_min(rhs_bound_pair.start(), BoundOverlapDisambiguationRuleSet::Strict);
    let max_end = lhs_bound_pair
        .end()
        .bound_max(rhs_bound_pair.end(), BoundOverlapDisambiguationRuleSet::Strict);

    AbsBoundPair::unchecked_new(min_start, max_end)
}

/// Extends an [`AbsBoundPair`] with an [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bound_pair_with_emptiable_abs_bound_pair(
    lhs_bound_pair: &AbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> AbsBoundPair {
    if let EmptiableAbsBoundPair::Bound(rhs_bound_pair) = rhs_bound_pair {
        extend_abs_bound_pair(lhs_bound_pair, rhs_bound_pair)
    } else {
        lhs_bound_pair.clone()
    }
}

/// Extends an [`EmptiableAbsBoundPair`] with an [`EmptiableAbsBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_emptiable_abs_bound_pair(
    lhs_bound_pair: &EmptiableAbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> EmptiableAbsBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableAbsBoundPair::Bound(lhs_bound_pair), EmptiableAbsBoundPair::Bound(rhs_bound_pair)) => {
            extend_abs_bound_pair(lhs_bound_pair, rhs_bound_pair).to_emptiable()
        },
        (EmptiableAbsBoundPair::Bound(lhs_bound_pair), EmptiableAbsBoundPair::Empty) => {
            extend_abs_bound_pair_with_emptiable_abs_bound_pair(lhs_bound_pair, rhs_bound_pair).to_emptiable()
        },
        (EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Bound(rhs_bound_pair)) => {
            extend_abs_bound_pair_with_emptiable_abs_bound_pair(rhs_bound_pair, lhs_bound_pair).to_emptiable()
        },
        (EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Empty) => EmptiableAbsBoundPair::Empty,
    }
}

/// Extends two [`BoundedAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bounded(lhs_bounded: &BoundedAbsInterval, rhs_bounded: &BoundedAbsInterval) -> BoundedAbsInterval {
    let min_start = lhs_bounded
        .start()
        .bound_min(rhs_bounded.start(), BoundOverlapDisambiguationRuleSet::Strict);
    let max_end = lhs_bounded
        .end()
        .bound_max(rhs_bounded.end(), BoundOverlapDisambiguationRuleSet::Strict);

    BoundedAbsInterval::unchecked_new(min_start, max_end)
}

/// Extends a [`BoundedAbsInterval`] with a [`HalfBoundedToFutureAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bounded_half_bounded_to_future(
    bounded: &BoundedAbsInterval,
    half_bounded_to_future: &HalfBoundedToFutureAbsInterval,
) -> HalfBoundedToFutureAbsInterval {
    let min_start = bounded.start().bound_min(
        half_bounded_to_future.start(),
        BoundOverlapDisambiguationRuleSet::Strict,
    );

    HalfBoundedToFutureAbsInterval::new(min_start)
}

/// Extends a [`BoundedAbsInterval`] with a [`HalfBoundedToPastAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bounded_half_bounded_to_past(
    bounded: &BoundedAbsInterval,
    half_bounded_to_past: &HalfBoundedToPastAbsInterval,
) -> HalfBoundedToPastAbsInterval {
    let max_end = bounded
        .end()
        .bound_max(half_bounded_to_past.end(), BoundOverlapDisambiguationRuleSet::Strict);

    HalfBoundedToPastAbsInterval::new(max_end)
}

/// Extends a [`BoundedAbsInterval`] with a [`HalfBoundedAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_bounded_half_bounded(
    bounded: &BoundedAbsInterval,
    half_bounded: &HalfBoundedAbsInterval,
) -> HalfBoundedAbsInterval {
    match half_bounded {
        HalfBoundedAbsInterval::ToFuture(hb_to_future) => {
            extend_abs_bounded_half_bounded_to_future(bounded, hb_to_future).to_half_bounded_interval()
        },
        HalfBoundedAbsInterval::ToPast(hb_to_past) => {
            extend_abs_bounded_half_bounded_to_past(bounded, hb_to_past).to_half_bounded_interval()
        },
    }
}

/// Extends two [`HalfBoundedToFutureAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_half_bounded_to_future(
    lhs_half_bounded: &HalfBoundedToFutureAbsInterval,
    rhs_half_bounded: &HalfBoundedToFutureAbsInterval,
) -> HalfBoundedToFutureAbsInterval {
    let min_start = lhs_half_bounded
        .start()
        .bound_min(rhs_half_bounded.start(), BoundOverlapDisambiguationRuleSet::Strict);

    HalfBoundedToFutureAbsInterval::new(min_start)
}

/// Extends two [`HalfBoundedToPastAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_half_bounded_to_past(
    lhs_half_bounded: &HalfBoundedToPastAbsInterval,
    rhs_half_bounded: &HalfBoundedToPastAbsInterval,
) -> HalfBoundedToPastAbsInterval {
    let max_end = lhs_half_bounded
        .end()
        .bound_max(rhs_half_bounded.end(), BoundOverlapDisambiguationRuleSet::Strict);

    HalfBoundedToPastAbsInterval::new(max_end)
}

/// Extends two [`HalfBoundedAbsInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_abs_half_bounded(
    lhs_half_bounded: &HalfBoundedAbsInterval,
    rhs_half_bounded: &HalfBoundedAbsInterval,
) -> AbsInterval {
    match (lhs_half_bounded, rhs_half_bounded) {
        (HalfBoundedAbsInterval::ToFuture(lhs_half_bounded), HalfBoundedAbsInterval::ToFuture(rhs_half_bounded)) => {
            extend_abs_half_bounded_to_future(lhs_half_bounded, rhs_half_bounded).to_interval()
        },
        (HalfBoundedAbsInterval::ToPast(lhs_half_bounded), HalfBoundedAbsInterval::ToPast(rhs_half_bounded)) => {
            extend_abs_half_bounded_to_past(lhs_half_bounded, rhs_half_bounded).to_interval()
        },
        (HalfBoundedAbsInterval::ToFuture(_), HalfBoundedAbsInterval::ToPast(_))
        | (HalfBoundedAbsInterval::ToPast(_), HalfBoundedAbsInterval::ToFuture(_)) => {
            UnboundedInterval.to_abs_interval()
        },
    }
}

/// Extends two [`RelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bound_pair(lhs_bound_pair: &RelBoundPair, rhs_bound_pair: &RelBoundPair) -> RelBoundPair {
    let min_start = lhs_bound_pair
        .start()
        .bound_min(rhs_bound_pair.start(), BoundOverlapDisambiguationRuleSet::Strict);
    let max_end = lhs_bound_pair
        .end()
        .bound_max(rhs_bound_pair.end(), BoundOverlapDisambiguationRuleSet::Strict);

    RelBoundPair::unchecked_new(min_start, max_end)
}

/// Extends a [`RelBoundPair`] with an [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bound_pair_with_emptiable_rel_bound_pair(
    lhs_bound_pair: &RelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> RelBoundPair {
    if let EmptiableRelBoundPair::Bound(rhs_bound_pair) = rhs_bound_pair {
        extend_rel_bound_pair(lhs_bound_pair, rhs_bound_pair)
    } else {
        lhs_bound_pair.clone()
    }
}

/// Extends an [`EmptiableRelBoundPair`] with an [`EmptiableRelBoundPair`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_emptiable_rel_bound_pair(
    lhs_bound_pair: &EmptiableRelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> EmptiableRelBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableRelBoundPair::Bound(lhs_bound_pair), EmptiableRelBoundPair::Bound(rhs_bound_pair)) => {
            extend_rel_bound_pair(lhs_bound_pair, rhs_bound_pair).to_emptiable()
        },
        (EmptiableRelBoundPair::Bound(lhs_bound_pair), EmptiableRelBoundPair::Empty) => {
            extend_rel_bound_pair_with_emptiable_rel_bound_pair(lhs_bound_pair, rhs_bound_pair).to_emptiable()
        },
        (EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Bound(rhs_bound_pair)) => {
            extend_rel_bound_pair_with_emptiable_rel_bound_pair(rhs_bound_pair, lhs_bound_pair).to_emptiable()
        },
        (EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Empty) => EmptiableRelBoundPair::Empty,
    }
}

/// Extends two [`BoundedRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bounded(lhs_bounded: &BoundedRelInterval, rhs_bounded: &BoundedRelInterval) -> BoundedRelInterval {
    let min_start = lhs_bounded
        .start()
        .bound_min(rhs_bounded.start(), BoundOverlapDisambiguationRuleSet::Strict);
    let max_end = lhs_bounded
        .end()
        .bound_max(rhs_bounded.end(), BoundOverlapDisambiguationRuleSet::Strict);

    BoundedRelInterval::unchecked_new(min_start, max_end)
}

/// Extends a [`BoundedRelInterval`] with a [`HalfBoundedToFutureRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bounded_half_bounded_to_future(
    bounded: &BoundedRelInterval,
    half_bounded_to_future: &HalfBoundedToFutureRelInterval,
) -> HalfBoundedToFutureRelInterval {
    let min_start = bounded.start().bound_min(
        half_bounded_to_future.start(),
        BoundOverlapDisambiguationRuleSet::Strict,
    );

    HalfBoundedToFutureRelInterval::new(min_start)
}

/// Extends a [`BoundedRelInterval`] with a [`HalfBoundedToPastRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bounded_half_bounded_to_past(
    bounded: &BoundedRelInterval,
    half_bounded_to_past: &HalfBoundedToPastRelInterval,
) -> HalfBoundedToPastRelInterval {
    let max_end = bounded
        .end()
        .bound_max(half_bounded_to_past.end(), BoundOverlapDisambiguationRuleSet::Strict);

    HalfBoundedToPastRelInterval::new(max_end)
}

/// Extends a [`BoundedRelInterval`] with a [`HalfBoundedRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_bounded_half_bounded(
    bounded: &BoundedRelInterval,
    half_bounded: &HalfBoundedRelInterval,
) -> HalfBoundedRelInterval {
    match half_bounded {
        HalfBoundedRelInterval::ToFuture(hb_to_future) => {
            extend_rel_bounded_half_bounded_to_future(bounded, hb_to_future).to_half_bounded_interval()
        },
        HalfBoundedRelInterval::ToPast(hb_to_past) => {
            extend_rel_bounded_half_bounded_to_past(bounded, hb_to_past).to_half_bounded_interval()
        },
    }
}

/// Extends two [`HalfBoundedToFutureRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_half_bounded_to_future(
    lhs_half_bounded: &HalfBoundedToFutureRelInterval,
    rhs_half_bounded: &HalfBoundedToFutureRelInterval,
) -> HalfBoundedToFutureRelInterval {
    let min_start = lhs_half_bounded
        .start()
        .bound_min(rhs_half_bounded.start(), BoundOverlapDisambiguationRuleSet::Strict);

    HalfBoundedToFutureRelInterval::new(min_start)
}

/// Extends two [`HalfBoundedToPastRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_half_bounded_to_past(
    lhs_half_bounded: &HalfBoundedToPastRelInterval,
    rhs_half_bounded: &HalfBoundedToPastRelInterval,
) -> HalfBoundedToPastRelInterval {
    let max_end = lhs_half_bounded
        .end()
        .bound_max(rhs_half_bounded.end(), BoundOverlapDisambiguationRuleSet::Strict);

    HalfBoundedToPastRelInterval::new(max_end)
}

/// Extends two [`HalfBoundedRelInterval`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn extend_rel_half_bounded(
    lhs_half_bounded: &HalfBoundedRelInterval,
    rhs_half_bounded: &HalfBoundedRelInterval,
) -> RelInterval {
    match (lhs_half_bounded, rhs_half_bounded) {
        (HalfBoundedRelInterval::ToFuture(lhs_half_bounded), HalfBoundedRelInterval::ToFuture(rhs_half_bounded)) => {
            extend_rel_half_bounded_to_future(lhs_half_bounded, rhs_half_bounded).to_interval()
        },
        (HalfBoundedRelInterval::ToPast(lhs_half_bounded), HalfBoundedRelInterval::ToPast(rhs_half_bounded)) => {
            extend_rel_half_bounded_to_past(lhs_half_bounded, rhs_half_bounded).to_interval()
        },
        (HalfBoundedRelInterval::ToFuture(_), HalfBoundedRelInterval::ToPast(_))
        | (HalfBoundedRelInterval::ToPast(_), HalfBoundedRelInterval::ToFuture(_)) => {
            UnboundedInterval.to_rel_interval()
        },
    }
}

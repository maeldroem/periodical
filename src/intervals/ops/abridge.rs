//! Interval abridging
//!
//! Abridging is similar to the inverse of [`Extensible`](crate::intervals::ops::extend::Extensible).
//! That is to say it will take the _highest_ start bound and link it to the _lowest_ end bound.
//!
//! If the highest start and the lowest end are equal and both are inclusive or
//! exclusive, it returns a bound of this instant.
//!
//! However, if the highest start and lowest end are adjacent, one being
//! inclusive and the other exclusive, abridging returns an empty interval.
//!
//! The terms _highest_ and _lowest_ are to be interpreted as _highest_ being
//! towards future, _lowest_ being towards past.
//!
//! # Examples
//!
//! See [`Abridgable`].

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
    swap_abs_start_end_bounds,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{
    BoundOrd,
    BoundOrdExtremaOps,
    BoundOrdering,
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
};
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
    RelEndBound,
    RelInterval,
    RelStartBound,
    swap_rel_start_end_bounds,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

macro_rules! abridgable_impl {
    () => {};

    (@select_method; $lhs:ident; $rhs:ident; abs; non_emptiable; non_emptiable) => {
        abridge_abs_bound_pair(&$lhs.abs_bound_pair(), &$rhs.abs_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; non_emptiable; emptiable) => {
        abridge_abs_bound_pair_with_emptiable_abs_bound_pair(&$lhs.abs_bound_pair(), &$rhs.emptiable_abs_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; emptiable; non_emptiable) => {
        abridgable_impl!(@select_method; $lhs; $rhs; abs; emptiable; emptiable)
    };
    (@select_method; $lhs:ident; $rhs:ident; abs; emptiable; emptiable) => {
        abridge_emptiable_abs_bound_pair(&$lhs.emptiable_abs_bound_pair(), &$rhs.emptiable_abs_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; non_emptiable; non_emptiable) => {
        abridge_rel_bound_pair(&$lhs.rel_bound_pair(), &$rhs.rel_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; non_emptiable; emptiable) => {
        abridge_rel_bound_pair_with_emptiable_rel_bound_pair(&$lhs.rel_bound_pair(), &$rhs.emptiable_rel_bound_pair())
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; emptiable; non_emptiable) => {
        abridgable_impl!(@select_method; $lhs; $rhs; rel; emptiable; emptiable)
    };
    (@select_method; $lhs:ident; $rhs:ident; rel; emptiable; emptiable) => {
        abridge_emptiable_rel_bound_pair(&$lhs.emptiable_rel_bound_pair(), &$rhs.emptiable_rel_bound_pair())
    };

    // Syntax sucks a bit, but doing match arms of different custom syntax is not possible declaratively
    // and annoying to parse in a proc macro.
    (for $implementor:ty [map rhs] $(|)? $($rhs:ty)|+ => lhs.clone(); $($tail:tt)*) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = $implementor;

                fn abridge(&self, _rhs: &$rhs) -> Self::Output {
                    self.clone()
                }
            }
        )+

        abridgable_impl!($($tail)*);
    };
    (for $implementor:ty [map rhs] $(|)? $($rhs:ty)|+ => rhs.clone(); $($tail:tt)*) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = $rhs;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    rhs.clone()
                }
            }
        )+

        abridgable_impl!($($tail)*);
    };
    (for $implementor:ty [map rhs] $(|)? $($rhs:ty)|+ => $output:ty [via] (
        $relativity:ident, $lhs_type:ident, $rhs_type:ident $(,)?
    ); $($tail:tt)*) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(abridgable_impl!(@select_method; self; rhs; $relativity; $lhs_type; $rhs_type))
                }
            }
        )+

        abridgable_impl!($($tail)*);
    };
}

/// Capacity to abridge an interval with another
///
/// Abridging is similar to the inverse of [`Extensible`](crate::intervals::ops::extend::Extensible).
/// That is to say it will take the _highest_ start bound and link it to the _lowest_ end bound.
///
/// If the highest start and the lowest end are equal and both are inclusive or
/// exclusive, it returns a bound of this instant.
///
/// However, if the highest start and lowest end are adjacent, one being
/// inclusive and the other exclusive, abridging returns an empty interval.
///
/// The terms _highest_ and _lowest_ are to be interpreted as _highest_ being
/// towards future, _lowest_ being towards past.
///
/// # Examples
///
/// ## Non-overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
/// let first_end_time = "2025-01-01 11:00:00Z".parse::<Timestamp>()?;
///
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(first_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 13:00:00Z".parse::<Timestamp>()?;
/// let second_end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(second_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(second_end_time).to_end_bound(),
/// );
///
/// let abridged_interval = first_interval.abridge(&second_interval);
///
/// // first interval:    [----]
/// // second interval:           [----]
/// // abridged interval:      (--)
///
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .start(),
///     AbsFiniteBoundPos::new_with_incl(first_end_time, BoundInclusivity::Exclusive)
///         .to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .end(),
///     AbsFiniteBoundPos::new_with_incl(second_start_time, BoundInclusivity::Exclusive)
///         .to_end_bound(),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
/// let first_end_time = "2025-01-01 13:00:00Z".parse::<Timestamp>()?;
///
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(first_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 11:00:00Z".parse::<Timestamp>()?;
/// let second_end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(second_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(second_end_time).to_end_bound(),
/// );
///
/// let abridged_interval = first_interval.abridge(&second_interval);
///
/// // first interval:    [----]
/// // second interval:     [----]
/// // abridged interval:   [--]
///
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .start(),
///     AbsFiniteBoundPos::new_with_incl(second_start_time, BoundInclusivity::Inclusive)
///         .to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .end(),
///     AbsFiniteBoundPos::new_with_incl(first_end_time, BoundInclusivity::Inclusive)
///         .to_end_bound(),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Inclusive-Exclusive adjacent intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::{
/// #     AbsBoundPair,
/// #     AbsFiniteBoundPos,
/// #     EmptiableAbsBoundPair,
/// # };
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
/// let first_end_time = "2025-01-01 12:00:00Z".parse::<Timestamp>()?;
///
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(first_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 12:00:00Z".parse::<Timestamp>()?;
/// let second_end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new_with_incl(second_start_time, BoundInclusivity::Exclusive)
///         .to_start_bound(),
///     AbsFiniteBoundPos::new(second_end_time).to_end_bound(),
/// );
///
/// let abridged_interval = first_interval.abridge(&second_interval);
///
/// // first interval:    [----]
/// // second interval:        (----]
/// // abridged interval: empty interval
///
/// assert_eq!(abridged_interval, EmptiableAbsBoundPair::Empty);
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Abridgable<Rhs = Self> {
    /// Output type
    type Output;

    /// Creates an abridged interval
    ///
    /// Instead of intersecting two intervals, this method takes the highest of
    /// both intervals' start and the lowest of both intervals' end, then
    /// create an interval that spans those two points.
    ///
    /// Regarding bound inclusivity, for each bound we will get the bound
    /// inclusivity of the interval from which the bound was taken. If they
    /// were equal, we choose the most exclusive bound.
    ///
    /// If the intervals don't strictly overlap, the method returns the interval
    /// that spans the gap between the two intervals. This sort of gap
    /// interval will have opposite bound inclusivities from the bounds they
    /// were created from.
    ///
    /// If the highest start and lowest end are adjacent, one being inclusive
    /// and the other exclusive, abridging returns an empty interval.
    ///
    /// If both intervals are empty, the method just returns an empty interval.
    ///
    /// If one interval is empty, the method just returns a clone of the other
    /// non-empty interval.
    #[must_use]
    fn abridge(&self, rhs: &Rhs) -> Self::Output;
}

abridgable_impl!(
    // Absolute
    for AbsBoundPair [map rhs]
        AbsBoundPair => EmptiableAbsBoundPair [via] (abs, non_emptiable, non_emptiable);
    for AbsBoundPair [map rhs]
        EmptiableAbsBoundPair => EmptiableAbsBoundPair [via] (abs, non_emptiable, emptiable);

    for EmptiableAbsBoundPair [map rhs]
        EmptiableAbsBoundPair => EmptiableAbsBoundPair [via] (abs, emptiable, emptiable);

    for AbsInterval [map rhs] AbsInterval => EmptiableAbsInterval [via] (abs, non_emptiable, non_emptiable);
    for AbsInterval [map rhs] EmptiableAbsInterval => EmptiableAbsInterval [via] (abs, non_emptiable, emptiable);

    for EmptiableAbsInterval [map rhs] AbsInterval => EmptiableAbsInterval [via] (abs, emptiable, non_emptiable);
    for EmptiableAbsInterval [map rhs] EmptiableAbsInterval => EmptiableAbsInterval [via] (abs, emptiable, emptiable);

    for BoundedAbsInterval [map rhs]
        BoundedAbsInterval | HalfBoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval
        => EmptiableAbsInterval [via] (abs, non_emptiable, non_emptiable);
    for BoundedAbsInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    for HalfBoundedAbsInterval [map rhs]
        BoundedAbsInterval | HalfBoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval
        => EmptiableAbsInterval [via] (abs, non_emptiable, non_emptiable);
    for HalfBoundedAbsInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    for HalfBoundedToFutureAbsInterval [map rhs]
        BoundedAbsInterval | HalfBoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval
        => EmptiableAbsInterval [via] (abs, non_emptiable, non_emptiable);
    for HalfBoundedToFutureAbsInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    for HalfBoundedToPastAbsInterval [map rhs]
        BoundedAbsInterval | HalfBoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval
        => EmptiableAbsInterval [via] (abs, non_emptiable, non_emptiable);
    for HalfBoundedToPastAbsInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    // Relative
    for RelBoundPair [map rhs]
        RelBoundPair => EmptiableRelBoundPair [via] (rel, non_emptiable, non_emptiable);
    for RelBoundPair [map rhs]
        EmptiableRelBoundPair => EmptiableRelBoundPair [via] (rel, non_emptiable, emptiable);

    for EmptiableRelBoundPair [map rhs]
        EmptiableRelBoundPair => EmptiableRelBoundPair [via] (rel, emptiable, emptiable);

    for RelInterval [map rhs] RelInterval => EmptiableRelInterval [via] (rel, non_emptiable, non_emptiable);
    for RelInterval [map rhs] EmptiableRelInterval => EmptiableRelInterval [via] (rel, non_emptiable, emptiable);

    for EmptiableRelInterval [map rhs] RelInterval => EmptiableRelInterval [via] (rel, emptiable, non_emptiable);
    for EmptiableRelInterval [map rhs] EmptiableRelInterval => EmptiableRelInterval [via] (rel, emptiable, emptiable);

    for BoundedRelInterval [map rhs]
        BoundedRelInterval | HalfBoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval
        => EmptiableRelInterval [via] (rel, non_emptiable, non_emptiable);
    for BoundedRelInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    for HalfBoundedRelInterval [map rhs]
        BoundedRelInterval | HalfBoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval
        => EmptiableRelInterval [via] (rel, non_emptiable, non_emptiable);
    for HalfBoundedRelInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    for HalfBoundedToFutureRelInterval [map rhs]
        BoundedRelInterval | HalfBoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval
        => EmptiableRelInterval [via] (rel, non_emptiable, non_emptiable);
    for HalfBoundedToFutureRelInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    for HalfBoundedToPastRelInterval [map rhs]
        BoundedRelInterval | HalfBoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval
        => EmptiableRelInterval [via] (rel, non_emptiable, non_emptiable);
    for HalfBoundedToPastRelInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    // Special
    for UnboundedInterval [map rhs]
        BoundedAbsInterval | HalfBoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval
        | BoundedRelInterval | HalfBoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval
        => rhs.clone();
    for UnboundedInterval [map rhs] UnboundedInterval | EmptyInterval => lhs.clone();

    for EmptyInterval [map rhs]
        BoundedAbsInterval | HalfBoundedAbsInterval | HalfBoundedToFutureAbsInterval | HalfBoundedToPastAbsInterval
        | BoundedRelInterval | HalfBoundedRelInterval | HalfBoundedToFutureRelInterval | HalfBoundedToPastRelInterval
        | UnboundedInterval
        => rhs.clone();
    for EmptyInterval [map rhs] EmptyInterval => lhs.clone();

);

/// Abridges two [`AbsBoundPair`]s
#[must_use]
pub fn abridge_abs_bound_pair(lhs_bound_pair: &AbsBoundPair, rhs_bound_pair: &AbsBoundPair) -> EmptiableAbsBoundPair {
    let mut max_start = lhs_bound_pair
        .start()
        .bound_max(rhs_bound_pair.start(), BoundOverlapDisambiguationRuleSet::Strict);
    let mut min_end = lhs_bound_pair
        .end()
        .bound_min(rhs_bound_pair.end(), BoundOverlapDisambiguationRuleSet::Strict);

    match max_start.bound_cmp(&min_end) {
        BoundOrdering::Less => AbsBoundPair::unchecked_new(max_start, min_end).to_emptiable(),
        BoundOrdering::Equal(None) => {
            unreachable!("Comparing a start bound to an end bound can never result in the ambiguity being `None`");
        },
        BoundOrdering::Equal(Some(ambiguity)) => {
            if let BoundOverlapAmbiguity::StartEnd(start_inclusivity, end_inclusivity) = ambiguity {
                match (start_inclusivity, end_inclusivity) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => {
                        AbsBoundPair::unchecked_new(max_start, min_end).to_emptiable()
                    },
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => EmptiableAbsBoundPair::Empty,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => {
                        if let AbsStartBound::Finite(ref mut finite_highest_start) = max_start {
                            finite_highest_start
                                .pos_mut()
                                .set_inclusivity(BoundInclusivity::Inclusive);
                        }

                        if let AbsEndBound::Finite(ref mut finite_lowest_end) = min_end {
                            finite_lowest_end.pos_mut().set_inclusivity(BoundInclusivity::Inclusive);
                        }

                        AbsBoundPair::unchecked_new(max_start, min_end).to_emptiable()
                    },
                }
            } else {
                unreachable!("Comparing a start bound to an end bound always results in a `StartEnd` ambiguity");
            }
        },
        BoundOrdering::Greater => {
            swap_abs_start_end_bounds(&mut max_start, &mut min_end);

            if let AbsStartBound::Finite(ref mut finite_start) = max_start {
                let new_incl = finite_start.pos().inclusivity().opposite();
                finite_start.pos_mut().set_inclusivity(new_incl);
            }

            if let AbsEndBound::Finite(ref mut finite_end) = min_end {
                let new_incl = finite_end.pos().inclusivity().opposite();
                finite_end.pos_mut().set_inclusivity(new_incl);
            }

            AbsBoundPair::unchecked_new(max_start, min_end).to_emptiable()
        },
    }
}

/// Abridges an [`AbsBoundPair`] with an [`EmptiableAbsBoundPair`]
#[must_use]
pub fn abridge_abs_bound_pair_with_emptiable_abs_bound_pair(
    lhs_bound_pair: &AbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> EmptiableAbsBoundPair {
    if let EmptiableAbsBoundPair::Bound(rhs_bound_pair) = rhs_bound_pair {
        abridge_abs_bound_pair(lhs_bound_pair, rhs_bound_pair)
    } else {
        EmptiableAbsBoundPair::Bound(lhs_bound_pair.clone())
    }
}

/// Abridges two [`EmptiableAbsBoundPair`]s
#[must_use]
pub fn abridge_emptiable_abs_bound_pair(
    lhs_bound_pair: &EmptiableAbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> EmptiableAbsBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Empty) => EmptiableAbsBoundPair::Empty,
        (EmptiableAbsBoundPair::Empty, bound @ EmptiableAbsBoundPair::Bound(_))
        | (bound @ EmptiableAbsBoundPair::Bound(_), EmptiableAbsBoundPair::Empty) => bound.clone(),
        (EmptiableAbsBoundPair::Bound(lhs_bound_pair), EmptiableAbsBoundPair::Bound(rhs_bound_pair)) => {
            abridge_abs_bound_pair(lhs_bound_pair, rhs_bound_pair)
        },
    }
}

/// Abridges two [`RelBoundPair`]s
#[must_use]
pub fn abridge_rel_bound_pair(lhs_bound_pair: &RelBoundPair, rhs_bound_pair: &RelBoundPair) -> EmptiableRelBoundPair {
    let mut max_start = lhs_bound_pair
        .start()
        .bound_max(rhs_bound_pair.start(), BoundOverlapDisambiguationRuleSet::Strict);
    let mut min_end = lhs_bound_pair
        .end()
        .bound_min(rhs_bound_pair.end(), BoundOverlapDisambiguationRuleSet::Strict);

    match max_start.bound_cmp(&min_end) {
        BoundOrdering::Less => RelBoundPair::unchecked_new(max_start, min_end).to_emptiable(),
        BoundOrdering::Equal(None) => {
            unreachable!("Comparing a start bound to an end bound can never result in the ambiguity being `None`");
        },
        BoundOrdering::Equal(Some(ambiguity)) => {
            if let BoundOverlapAmbiguity::StartEnd(start_inclusivity, end_inclusivity) = ambiguity {
                match (start_inclusivity, end_inclusivity) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => {
                        RelBoundPair::unchecked_new(max_start, min_end).to_emptiable()
                    },
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => EmptiableRelBoundPair::Empty,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => {
                        if let RelStartBound::Finite(ref mut finite_highest_start) = max_start {
                            finite_highest_start
                                .pos_mut()
                                .set_inclusivity(BoundInclusivity::Inclusive);
                        }

                        if let RelEndBound::Finite(ref mut finite_lowest_end) = min_end {
                            finite_lowest_end.pos_mut().set_inclusivity(BoundInclusivity::Inclusive);
                        }

                        RelBoundPair::unchecked_new(max_start, min_end).to_emptiable()
                    },
                }
            } else {
                unreachable!("Comparing a start bound to an end bound always results in a `StartEnd` ambiguity");
            }
        },
        BoundOrdering::Greater => {
            swap_rel_start_end_bounds(&mut max_start, &mut min_end);

            if let RelStartBound::Finite(ref mut finite_start) = max_start {
                let new_incl = finite_start.pos().inclusivity().opposite();
                finite_start.pos_mut().set_inclusivity(new_incl);
            }

            if let RelEndBound::Finite(ref mut finite_end) = min_end {
                let new_incl = finite_end.pos().inclusivity().opposite();
                finite_end.pos_mut().set_inclusivity(new_incl);
            }

            RelBoundPair::unchecked_new(max_start, min_end).to_emptiable()
        },
    }
}

/// Abridges an [`RelBoundPair`] with an [`EmptiableRelBoundPair`]
#[must_use]
pub fn abridge_rel_bound_pair_with_emptiable_rel_bound_pair(
    lhs_bound_pair: &RelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> EmptiableRelBoundPair {
    if let EmptiableRelBoundPair::Bound(rhs_bound_pair) = rhs_bound_pair {
        abridge_rel_bound_pair(lhs_bound_pair, rhs_bound_pair)
    } else {
        EmptiableRelBoundPair::Bound(lhs_bound_pair.clone())
    }
}

/// Abridges two [`EmptiableRelBoundPair`]s
#[must_use]
pub fn abridge_emptiable_rel_bound_pair(
    lhs_bound_pair: &EmptiableRelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> EmptiableRelBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Empty) => EmptiableRelBoundPair::Empty,
        (EmptiableRelBoundPair::Empty, bound @ EmptiableRelBoundPair::Bound(_))
        | (bound @ EmptiableRelBoundPair::Bound(_), EmptiableRelBoundPair::Empty) => bound.clone(),
        (EmptiableRelBoundPair::Bound(lhs_bound_pair), EmptiableRelBoundPair::Bound(rhs_bound_pair)) => {
            abridge_rel_bound_pair(lhs_bound_pair, rhs_bound_pair)
        },
    }
}

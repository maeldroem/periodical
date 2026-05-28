//! Interval abridging
//!
//! Abridging is similar to the inverse of
//! [`Extensible`](crate::intervals::ops::extend::Extensible). That is to say it
//! will take the _highest_ start bound and link it to the _lowest_ end bound.
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
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
    swap_absolute_bound_pair,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
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
    swap_relative_bound_pair,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

macro_rules! abridgable_impl {
    (implementor => $implementor:ty, rhs => [$($rhs:ty),*$(,)?], output => clone rhs $(,)?) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = $rhs;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    rhs.clone()
                }
            }
        )*
    };
    (implementor => $implementor:ty, rhs => [$($rhs:ty),*$(,)?], output => clone lhs $(,)?) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = Self;

                fn abridge(&self, _rhs: &$rhs) -> Self::Output {
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
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(abridge_abs_bound_pair(&self.abs_bound_pair(), &rhs.abs_bound_pair()))
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
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(abridge_abs_bound_pair_with_emptiable_abs_bound_pair(
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
        abridgable_impl!(
            implementor => $implementor,
            rhs => [$($rhs),*],
            output => $output,
            absolute,
            (emptiable, emptiable),
        );
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        absolute,
        (emptiable, emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(abridge_emptiable_abs_bound_pair(
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
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(abridge_rel_bound_pair(&self.rel_bound_pair(), &rhs.rel_bound_pair()))
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
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(abridge_rel_bound_pair_with_emptiable_rel_bound_pair(
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
        abridgable_impl!(
            implementor => $implementor,
            rhs => [$($rhs),*],
            output => $output,
            relative,
            (emptiable, emptiable),
        );
    };
    (
        implementor => $implementor:ty,
        rhs => [$($rhs:ty),*$(,)?],
        output => $output:ty,
        relative,
        (emptiable, emptiable $(,)?) $(,)?
    ) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(abridge_emptiable_rel_bound_pair(
                        &self.emptiable_rel_bound_pair(),
                        &rhs.emptiable_rel_bound_pair()
                    ))
                }
            }
        )*
    };
}

/// Capacity to abridge an interval with another
///
/// Abridging is similar to the inverse of
/// [`Extensible`](crate::intervals::ops::extend::Extensible). That is to say it
/// will take the _highest_ start bound and link it to the _lowest_ end bound.
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
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let first_end_time = "2025-01-01 11:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
///
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(first_start_time).to_start_bound(),
///     AbsoluteFiniteBound::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 13:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(second_start_time).to_start_bound(),
///     AbsoluteFiniteBound::new(second_end_time).to_end_bound(),
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
///     AbsoluteFiniteBound::new_with_inclusivity(first_end_time, BoundInclusivity::Exclusive,)
///         .to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .end(),
///     AbsoluteFiniteBound::new_with_inclusivity(second_start_time, BoundInclusivity::Exclusive,)
///         .to_end_bound(),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Overlapping intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let first_end_time = "2025-01-01 13:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
///
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(first_start_time).to_start_bound(),
///     AbsoluteFiniteBound::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 11:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(second_start_time).to_start_bound(),
///     AbsoluteFiniteBound::new(second_end_time).to_end_bound(),
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
///     AbsoluteFiniteBound::new_with_inclusivity(second_start_time, BoundInclusivity::Inclusive,)
///         .to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .end(),
///     AbsoluteFiniteBound::new_with_inclusivity(first_end_time, BoundInclusivity::Inclusive,)
///         .to_end_bound(),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Inclusive-Exclusive adjacent intervals
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let first_end_time = "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
///
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(first_start_time).to_start_bound(),
///     AbsoluteFiniteBound::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
///
/// let second_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new_with_inclusivity(
///         second_start_time,
///         BoundInclusivity::Exclusive,
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(second_end_time).to_end_bound(),
/// );
///
/// let abridged_interval = first_interval.abridge(&second_interval);
///
/// // first interval:    [----]
/// // second interval:        (----]
/// // abridged interval: empty interval
///
/// assert_eq!(abridged_interval, EmptiableAbsoluteBoundPair::Empty);
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
    implementor => AbsoluteBoundPair,
    rhs => [AbsoluteBoundPair],
    output => EmptiableAbsoluteBoundPair,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => AbsoluteBoundPair,
    rhs => [EmptiableAbsoluteBoundPair],
    output => EmptiableAbsoluteBoundPair,
    absolute,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsoluteBoundPair,
    rhs => [AbsoluteBoundPair],
    output => EmptiableAbsoluteBoundPair,
    absolute,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsoluteBoundPair,
    rhs => [EmptiableAbsoluteBoundPair],
    output => EmptiableAbsoluteBoundPair,
    absolute,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => AbsoluteInterval,
    rhs => [AbsoluteInterval],
    output => EmptiableAbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => AbsoluteInterval,
    rhs => [EmptiableAbsoluteInterval],
    output => EmptiableAbsoluteInterval,
    absolute,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsoluteInterval,
    rhs => [AbsoluteInterval],
    output => EmptiableAbsoluteInterval,
    absolute,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsoluteInterval,
    rhs => [EmptiableAbsoluteInterval],
    output => EmptiableAbsoluteInterval,
    absolute,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => BoundedAbsoluteInterval,
    rhs => [BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval],
    output => EmptiableAbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => BoundedAbsoluteInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);
abridgable_impl!(
    implementor => HalfBoundedAbsoluteInterval,
    rhs => [BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval],
    output => EmptiableAbsoluteInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => HalfBoundedAbsoluteInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);

abridgable_impl!(
    implementor => RelativeBoundPair,
    rhs => [RelativeBoundPair],
    output => EmptiableRelativeBoundPair,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => RelativeBoundPair,
    rhs => [EmptiableRelativeBoundPair],
    output => EmptiableRelativeBoundPair,
    relative,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelativeBoundPair,
    rhs => [RelativeBoundPair],
    output => EmptiableRelativeBoundPair,
    relative,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelativeBoundPair,
    rhs => [EmptiableRelativeBoundPair],
    output => EmptiableRelativeBoundPair,
    relative,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => RelativeInterval,
    rhs => [RelativeInterval],
    output => EmptiableRelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => RelativeInterval,
    rhs => [EmptiableRelativeInterval],
    output => EmptiableRelativeInterval,
    relative,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelativeInterval,
    rhs => [RelativeInterval],
    output => EmptiableRelativeInterval,
    relative,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelativeInterval,
    rhs => [EmptiableRelativeInterval],
    output => EmptiableRelativeInterval,
    relative,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => BoundedRelativeInterval,
    rhs => [BoundedRelativeInterval, HalfBoundedRelativeInterval],
    output => EmptiableRelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => BoundedRelativeInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);
abridgable_impl!(
    implementor => HalfBoundedRelativeInterval,
    rhs => [BoundedRelativeInterval, HalfBoundedRelativeInterval],
    output => EmptiableRelativeInterval,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => HalfBoundedRelativeInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);

abridgable_impl!(
    implementor => UnboundedInterval,
    rhs => [
        BoundedAbsoluteInterval,
        HalfBoundedAbsoluteInterval,
        BoundedRelativeInterval,
        HalfBoundedRelativeInterval,
    ],
    output => clone rhs,
);
abridgable_impl!(
    implementor => UnboundedInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);

abridgable_impl!(
    implementor => EmptyInterval,
    rhs => [
        BoundedAbsoluteInterval,
        HalfBoundedAbsoluteInterval,
        BoundedRelativeInterval,
        HalfBoundedRelativeInterval,
        UnboundedInterval,
    ],
    output => clone rhs,
);
abridgable_impl!(
    implementor => EmptyInterval,
    rhs => [EmptyInterval],
    output => clone lhs,
);

/// Abridges two [`AbsoluteBoundPair`]s
#[must_use]
pub fn abridge_abs_bound_pair(
    lhs_bound_pair: &AbsoluteBoundPair,
    rhs_bound_pair: &AbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    let mut highest_start = match (lhs_bound_pair.abs_start(), rhs_bound_pair.abs_start()) {
        (AbsoluteStartBound::InfinitePast, bound @ AbsoluteStartBound::Finite(..))
        | (
            bound @ (AbsoluteStartBound::Finite(..) | AbsoluteStartBound::InfinitePast),
            AbsoluteStartBound::InfinitePast,
        ) => bound,
        (lhs_bound @ AbsoluteStartBound::Finite(..), rhs_bound @ AbsoluteStartBound::Finite(..)) => {
            if lhs_bound >= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    let mut lowest_end = match (lhs_bound_pair.abs_end(), rhs_bound_pair.abs_end()) {
        (AbsoluteEndBound::InfiniteFuture, bound @ AbsoluteEndBound::Finite(..))
        | (
            bound @ (AbsoluteEndBound::Finite(..) | AbsoluteEndBound::InfiniteFuture),
            AbsoluteEndBound::InfiniteFuture,
        ) => bound,
        (lhs_bound @ AbsoluteEndBound::Finite(..), rhs_bound @ AbsoluteEndBound::Finite(..)) => {
            if lhs_bound <= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    match highest_start.bound_cmp(&lowest_end) {
        BoundOrdering::Less => {
            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::unchecked_new(highest_start, lowest_end))
        },
        BoundOrdering::Equal(None) => {
            unreachable!("Comparing a start bound to an end bound can never result in the ambiguity being `None`");
        },
        BoundOrdering::Equal(Some(ambiguity)) => {
            if let BoundOverlapAmbiguity::EndStart(reference_inclusivity, compared_inclusivity) = ambiguity {
                match (reference_inclusivity, compared_inclusivity) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => {
                        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => EmptiableAbsoluteBoundPair::Empty,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => {
                        if let AbsoluteStartBound::Finite(ref mut finite_start) = highest_start {
                            finite_start.set_inclusivity(finite_start.inclusivity().opposite());
                        }

                        if let AbsoluteEndBound::Finite(ref mut finite_end) = lowest_end {
                            finite_end.set_inclusivity(finite_end.inclusivity().opposite());
                        }

                        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                }
            } else {
                unreachable!("Comparing a start bound to an end bound always results in a `EndStart` ambiguity");
            }
        },
        BoundOrdering::Greater => {
            swap_absolute_bound_pair(&mut highest_start, &mut lowest_end);

            if let AbsoluteStartBound::Finite(ref mut finite_start) = highest_start {
                finite_start.set_inclusivity(finite_start.inclusivity().opposite());
            }

            if let AbsoluteEndBound::Finite(ref mut finite_end) = lowest_end {
                finite_end.set_inclusivity(finite_end.inclusivity().opposite());
            }

            EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::unchecked_new(highest_start, lowest_end))
        },
    }
}

/// Abridges an [`AbsoluteBoundPair`] with an [`EmptiableAbsoluteBoundPair`]
#[must_use]
pub fn abridge_abs_bound_pair_with_emptiable_abs_bound_pair(
    lhs_bound_pair: &AbsoluteBoundPair,
    rhs_bound_pair: &EmptiableAbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(rhs_non_empty_bounds) = rhs_bound_pair else {
        return EmptiableAbsoluteBoundPair::Bound(lhs_bound_pair.clone());
    };

    abridge_abs_bound_pair(lhs_bound_pair, rhs_non_empty_bounds)
}

/// Abridges two [`EmptiableAbsoluteBoundPair`]s
#[must_use]
pub fn abridge_emptiable_abs_bound_pair(
    lhs_bound_pair: &EmptiableAbsoluteBoundPair,
    rhs_bound_pair: &EmptiableAbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableAbsoluteBoundPair::Empty, EmptiableAbsoluteBoundPair::Empty) => EmptiableAbsoluteBoundPair::Empty,
        (EmptiableAbsoluteBoundPair::Empty, bound @ EmptiableAbsoluteBoundPair::Bound(..))
        | (bound @ EmptiableAbsoluteBoundPair::Bound(..), EmptiableAbsoluteBoundPair::Empty) => bound.clone(),
        (EmptiableAbsoluteBoundPair::Bound(lhs_bound_pair), EmptiableAbsoluteBoundPair::Bound(rhs_bound_pair)) => {
            abridge_abs_bound_pair(lhs_bound_pair, rhs_bound_pair)
        },
    }
}

/// Abridges two [`RelativeBoundPair`]s
#[must_use]
pub fn abridge_rel_bound_pair(
    lhs_bound_pair: &RelativeBoundPair,
    rhs_bound_pair: &RelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    let mut highest_start = match (lhs_bound_pair.rel_start(), rhs_bound_pair.rel_start()) {
        (RelativeStartBound::InfinitePast, bound @ RelativeStartBound::Finite(..))
        | (
            bound @ (RelativeStartBound::Finite(..) | RelativeStartBound::InfinitePast),
            RelativeStartBound::InfinitePast,
        ) => bound,
        (lhs_bound @ RelativeStartBound::Finite(..), rhs_bound @ RelativeStartBound::Finite(..)) => {
            if lhs_bound >= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    let mut lowest_end = match (lhs_bound_pair.rel_end(), rhs_bound_pair.rel_end()) {
        (RelativeEndBound::InfiniteFuture, bound @ RelativeEndBound::Finite(..))
        | (
            bound @ (RelativeEndBound::Finite(..) | RelativeEndBound::InfiniteFuture),
            RelativeEndBound::InfiniteFuture,
        ) => bound,
        (lhs_bound @ RelativeEndBound::Finite(..), rhs_bound @ RelativeEndBound::Finite(..)) => {
            if lhs_bound <= rhs_bound { lhs_bound } else { rhs_bound }
        },
    };

    match highest_start.bound_cmp(&lowest_end) {
        BoundOrdering::Less => {
            EmptiableRelativeBoundPair::Bound(RelativeBoundPair::unchecked_new(highest_start, lowest_end))
        },
        BoundOrdering::Equal(None) => {
            unreachable!("Comparing a start bound to an end bound can never result in the ambiguity being `None`");
        },
        BoundOrdering::Equal(Some(ambiguity)) => {
            if let BoundOverlapAmbiguity::EndStart(reference_inclusivity, compared_inclusivity) = ambiguity {
                match (reference_inclusivity, compared_inclusivity) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => {
                        EmptiableRelativeBoundPair::Bound(RelativeBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => EmptiableRelativeBoundPair::Empty,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => {
                        if let RelativeStartBound::Finite(ref mut finite_start) = highest_start {
                            finite_start.set_inclusivity(finite_start.inclusivity().opposite());
                        }

                        if let RelativeEndBound::Finite(ref mut finite_end) = lowest_end {
                            finite_end.set_inclusivity(finite_end.inclusivity().opposite());
                        }

                        EmptiableRelativeBoundPair::Bound(RelativeBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                }
            } else {
                unreachable!("Comparing a start bound to an end bound always results in a `EndStart` ambiguity");
            }
        },
        BoundOrdering::Greater => {
            swap_relative_bound_pair(&mut highest_start, &mut lowest_end);

            if let RelativeStartBound::Finite(ref mut finite_start) = highest_start {
                finite_start.set_inclusivity(finite_start.inclusivity().opposite());
            }

            if let RelativeEndBound::Finite(ref mut finite_end) = lowest_end {
                finite_end.set_inclusivity(finite_end.inclusivity().opposite());
            }

            EmptiableRelativeBoundPair::Bound(RelativeBoundPair::unchecked_new(highest_start, lowest_end))
        },
    }
}

/// Abridges an [`RelativeBoundPair`] with an [`EmptiableRelativeBoundPair`]
#[must_use]
pub fn abridge_rel_bound_pair_with_emptiable_rel_bound_pair(
    lhs_bound_pair: &RelativeBoundPair,
    rhs_bound_pair: &EmptiableRelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(rhs_non_empty_bound_pair) = rhs_bound_pair else {
        return EmptiableRelativeBoundPair::Bound(lhs_bound_pair.clone());
    };

    abridge_rel_bound_pair(lhs_bound_pair, rhs_non_empty_bound_pair)
}

/// Abridges two [`EmptiableRelativeBoundPair`]s
#[must_use]
pub fn abridge_emptiable_rel_bound_pair(
    lhs_bound_pair: &EmptiableRelativeBoundPair,
    rhs_bound_pair: &EmptiableRelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableRelativeBoundPair::Empty, EmptiableRelativeBoundPair::Empty) => EmptiableRelativeBoundPair::Empty,
        (EmptiableRelativeBoundPair::Empty, bound @ EmptiableRelativeBoundPair::Bound(..))
        | (bound @ EmptiableRelativeBoundPair::Bound(..), EmptiableRelativeBoundPair::Empty) => bound.clone(),
        (EmptiableRelativeBoundPair::Bound(lhs_bound_pair), EmptiableRelativeBoundPair::Bound(rhs_bound_pair)) => {
            abridge_rel_bound_pair(lhs_bound_pair, rhs_bound_pair)
        },
    }
}

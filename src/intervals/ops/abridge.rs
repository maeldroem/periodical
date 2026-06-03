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
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
    swap_absolute_start_end_bounds,
};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};
use crate::intervals::ops::{BoundOrd, BoundOrdering, BoundOverlapAmbiguity};
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
    swap_relative_start_end_bounds,
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
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let first_end_time = "2025-01-01 11:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
///
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(first_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 13:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
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
///     AbsFiniteBoundPos::new_with_inclusivity(first_end_time, BoundInclusivity::Exclusive,)
///         .to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .end(),
///     AbsFiniteBoundPos::new_with_inclusivity(second_start_time, BoundInclusivity::Exclusive,)
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
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let first_end_time = "2025-01-01 13:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
///
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(first_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 11:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]"
///     .parse::<Zoned>()?
///     .timestamp();
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
///     AbsFiniteBoundPos::new_with_inclusivity(second_start_time, BoundInclusivity::Inclusive,)
///         .to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval
///         .clone()
///         .bound()
///         .ok_or("Empty abridged interval")?
///         .end(),
///     AbsFiniteBoundPos::new_with_inclusivity(first_end_time, BoundInclusivity::Inclusive,)
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
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::abridge::Abridgable;
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let first_end_time = "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
///
/// let first_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(first_start_time).to_start_bound(),
///     AbsFiniteBoundPos::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
///
/// let second_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new_with_inclusivity(
///         second_start_time,
///         BoundInclusivity::Exclusive,
///     ).to_start_bound(),
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
    implementor => AbsBoundPair,
    rhs => [AbsBoundPair],
    output => EmptiableAbsBoundPair,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => AbsBoundPair,
    rhs => [EmptiableAbsBoundPair],
    output => EmptiableAbsBoundPair,
    absolute,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsBoundPair,
    rhs => [AbsBoundPair],
    output => EmptiableAbsBoundPair,
    absolute,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsBoundPair,
    rhs => [EmptiableAbsBoundPair],
    output => EmptiableAbsBoundPair,
    absolute,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => AbsInterval,
    rhs => [AbsInterval],
    output => EmptiableAbsInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => AbsInterval,
    rhs => [EmptiableAbsInterval],
    output => EmptiableAbsInterval,
    absolute,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsInterval,
    rhs => [AbsInterval],
    output => EmptiableAbsInterval,
    absolute,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableAbsInterval,
    rhs => [EmptiableAbsInterval],
    output => EmptiableAbsInterval,
    absolute,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => BoundedAbsInterval,
    rhs => [BoundedAbsInterval, HalfBoundedAbsInterval],
    output => EmptiableAbsInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => BoundedAbsInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);
abridgable_impl!(
    implementor => HalfBoundedAbsInterval,
    rhs => [BoundedAbsInterval, HalfBoundedAbsInterval],
    output => EmptiableAbsInterval,
    absolute,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => HalfBoundedAbsInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);

abridgable_impl!(
    implementor => RelBoundPair,
    rhs => [RelBoundPair],
    output => EmptiableRelBoundPair,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => RelBoundPair,
    rhs => [EmptiableRelBoundPair],
    output => EmptiableRelBoundPair,
    relative,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelBoundPair,
    rhs => [RelBoundPair],
    output => EmptiableRelBoundPair,
    relative,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelBoundPair,
    rhs => [EmptiableRelBoundPair],
    output => EmptiableRelBoundPair,
    relative,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => RelInterval,
    rhs => [RelInterval],
    output => EmptiableRelInterval,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => RelInterval,
    rhs => [EmptiableRelInterval],
    output => EmptiableRelInterval,
    relative,
    (non_emptiable, emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelInterval,
    rhs => [RelInterval],
    output => EmptiableRelInterval,
    relative,
    (emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => EmptiableRelInterval,
    rhs => [EmptiableRelInterval],
    output => EmptiableRelInterval,
    relative,
    (emptiable, emptiable),
);
abridgable_impl!(
    implementor => BoundedRelInterval,
    rhs => [BoundedRelInterval, HalfBoundedRelInterval],
    output => EmptiableRelInterval,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => BoundedRelInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);
abridgable_impl!(
    implementor => HalfBoundedRelInterval,
    rhs => [BoundedRelInterval, HalfBoundedRelInterval],
    output => EmptiableRelInterval,
    relative,
    (non_emptiable, non_emptiable),
);
abridgable_impl!(
    implementor => HalfBoundedRelInterval,
    rhs => [UnboundedInterval, EmptyInterval],
    output => clone lhs,
);

abridgable_impl!(
    implementor => UnboundedInterval,
    rhs => [
        BoundedAbsInterval,
        HalfBoundedAbsInterval,
        BoundedRelInterval,
        HalfBoundedRelInterval,
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
        BoundedAbsInterval,
        HalfBoundedAbsInterval,
        BoundedRelInterval,
        HalfBoundedRelInterval,
        UnboundedInterval,
    ],
    output => clone rhs,
);
abridgable_impl!(
    implementor => EmptyInterval,
    rhs => [EmptyInterval],
    output => clone lhs,
);

/// Abridges two [`AbsBoundPair`]s
#[must_use]
pub fn abridge_abs_bound_pair(lhs_bound_pair: &AbsBoundPair, rhs_bound_pair: &AbsBoundPair) -> EmptiableAbsBoundPair {
    let mut highest_start =
        match (lhs_bound_pair.abs_start(), rhs_bound_pair.abs_start()) {
            (AbsStartBound::InfinitePast, bound @ AbsStartBound::Finite(..))
            | (bound @ (AbsStartBound::Finite(..) | AbsStartBound::InfinitePast), AbsStartBound::InfinitePast) => bound,
            (lhs_bound @ AbsStartBound::Finite(..), rhs_bound @ AbsStartBound::Finite(..)) => {
                if lhs_bound >= rhs_bound { lhs_bound } else { rhs_bound }
            },
        };

    let mut lowest_end = match (lhs_bound_pair.abs_end(), rhs_bound_pair.abs_end()) {
        (AbsEndBound::InfiniteFuture, bound @ AbsEndBound::Finite(..))
        | (bound @ (AbsEndBound::Finite(..) | AbsEndBound::InfiniteFuture), AbsEndBound::InfiniteFuture) => bound,
        (lhs_bound @ AbsEndBound::Finite(..), rhs_bound @ AbsEndBound::Finite(..)) => {
            if lhs_bound <= rhs_bound {
                lhs_bound
            } else {
                rhs_bound
            }
        },
    };

    match highest_start.bound_cmp(&lowest_end) {
        BoundOrdering::Less => EmptiableAbsBoundPair::Bound(AbsBoundPair::unchecked_new(highest_start, lowest_end)),
        BoundOrdering::Equal(None) => {
            unreachable!("Comparing a start bound to an end bound can never result in the ambiguity being `None`");
        },
        BoundOrdering::Equal(Some(ambiguity)) => {
            if let BoundOverlapAmbiguity::EndStart(reference_inclusivity, compared_inclusivity) = ambiguity {
                match (reference_inclusivity, compared_inclusivity) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => {
                        EmptiableAbsBoundPair::Bound(AbsBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => EmptiableAbsBoundPair::Empty,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => {
                        if let AbsStartBound::Finite(ref mut finite_start) = highest_start {
                            let new_incl = finite_start.pos().inclusivity().opposite();
                            finite_start.pos_mut().set_inclusivity(new_incl);
                        }

                        if let AbsEndBound::Finite(ref mut finite_end) = lowest_end {
                            let new_incl = finite_end.pos().inclusivity().opposite();
                            finite_end.pos_mut().set_inclusivity(new_incl);
                        }

                        EmptiableAbsBoundPair::Bound(AbsBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                }
            } else {
                unreachable!("Comparing a start bound to an end bound always results in a `EndStart` ambiguity");
            }
        },
        BoundOrdering::Greater => {
            swap_absolute_start_end_bounds(&mut highest_start, &mut lowest_end);

            if let AbsStartBound::Finite(ref mut finite_start) = highest_start {
                let new_incl = finite_start.pos().inclusivity().opposite();
                finite_start.pos_mut().set_inclusivity(new_incl);
            }

            if let AbsEndBound::Finite(ref mut finite_end) = lowest_end {
                let new_incl = finite_end.pos().inclusivity().opposite();
                finite_end.pos_mut().set_inclusivity(new_incl);
            }

            EmptiableAbsBoundPair::Bound(AbsBoundPair::unchecked_new(highest_start, lowest_end))
        },
    }
}

/// Abridges an [`AbsBoundPair`] with an [`EmptiableAbsBoundPair`]
#[must_use]
pub fn abridge_abs_bound_pair_with_emptiable_abs_bound_pair(
    lhs_bound_pair: &AbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> EmptiableAbsBoundPair {
    let EmptiableAbsBoundPair::Bound(rhs_non_empty_bounds) = rhs_bound_pair else {
        return EmptiableAbsBoundPair::Bound(lhs_bound_pair.clone());
    };

    abridge_abs_bound_pair(lhs_bound_pair, rhs_non_empty_bounds)
}

/// Abridges two [`EmptiableAbsBoundPair`]s
#[must_use]
pub fn abridge_emptiable_abs_bound_pair(
    lhs_bound_pair: &EmptiableAbsBoundPair,
    rhs_bound_pair: &EmptiableAbsBoundPair,
) -> EmptiableAbsBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Empty) => EmptiableAbsBoundPair::Empty,
        (EmptiableAbsBoundPair::Empty, bound @ EmptiableAbsBoundPair::Bound(..))
        | (bound @ EmptiableAbsBoundPair::Bound(..), EmptiableAbsBoundPair::Empty) => bound.clone(),
        (EmptiableAbsBoundPair::Bound(lhs_bound_pair), EmptiableAbsBoundPair::Bound(rhs_bound_pair)) => {
            abridge_abs_bound_pair(lhs_bound_pair, rhs_bound_pair)
        },
    }
}

/// Abridges two [`RelBoundPair`]s
#[must_use]
pub fn abridge_rel_bound_pair(lhs_bound_pair: &RelBoundPair, rhs_bound_pair: &RelBoundPair) -> EmptiableRelBoundPair {
    let mut highest_start =
        match (lhs_bound_pair.rel_start(), rhs_bound_pair.rel_start()) {
            (RelStartBound::InfinitePast, bound @ RelStartBound::Finite(..))
            | (bound @ (RelStartBound::Finite(..) | RelStartBound::InfinitePast), RelStartBound::InfinitePast) => bound,
            (lhs_bound @ RelStartBound::Finite(..), rhs_bound @ RelStartBound::Finite(..)) => {
                if lhs_bound >= rhs_bound { lhs_bound } else { rhs_bound }
            },
        };

    let mut lowest_end = match (lhs_bound_pair.rel_end(), rhs_bound_pair.rel_end()) {
        (RelEndBound::InfiniteFuture, bound @ RelEndBound::Finite(..))
        | (bound @ (RelEndBound::Finite(..) | RelEndBound::InfiniteFuture), RelEndBound::InfiniteFuture) => bound,
        (lhs_bound @ RelEndBound::Finite(..), rhs_bound @ RelEndBound::Finite(..)) => {
            if lhs_bound <= rhs_bound {
                lhs_bound
            } else {
                rhs_bound
            }
        },
    };

    match highest_start.bound_cmp(&lowest_end) {
        BoundOrdering::Less => EmptiableRelBoundPair::Bound(RelBoundPair::unchecked_new(highest_start, lowest_end)),
        BoundOrdering::Equal(None) => {
            unreachable!("Comparing a start bound to an end bound can never result in the ambiguity being `None`");
        },
        BoundOrdering::Equal(Some(ambiguity)) => {
            if let BoundOverlapAmbiguity::EndStart(reference_inclusivity, compared_inclusivity) = ambiguity {
                match (reference_inclusivity, compared_inclusivity) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => {
                        EmptiableRelBoundPair::Bound(RelBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => EmptiableRelBoundPair::Empty,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => {
                        if let RelStartBound::Finite(ref mut finite_start) = highest_start {
                            let new_incl = finite_start.pos().inclusivity().opposite();
                            finite_start.pos_mut().set_inclusivity(new_incl);
                        }

                        if let RelEndBound::Finite(ref mut finite_end) = lowest_end {
                            let new_incl = finite_end.pos().inclusivity().opposite();
                            finite_end.pos_mut().set_inclusivity(new_incl);
                        }

                        EmptiableRelBoundPair::Bound(RelBoundPair::unchecked_new(highest_start, lowest_end))
                    },
                }
            } else {
                unreachable!("Comparing a start bound to an end bound always results in a `EndStart` ambiguity");
            }
        },
        BoundOrdering::Greater => {
            swap_relative_start_end_bounds(&mut highest_start, &mut lowest_end);

            if let RelStartBound::Finite(ref mut finite_start) = highest_start {
                let new_incl = finite_start.pos().inclusivity().opposite();
                finite_start.pos_mut().set_inclusivity(new_incl);
            }

            if let RelEndBound::Finite(ref mut finite_end) = lowest_end {
                let new_incl = finite_end.pos().inclusivity().opposite();
                finite_end.pos_mut().set_inclusivity(new_incl);
            }

            EmptiableRelBoundPair::Bound(RelBoundPair::unchecked_new(highest_start, lowest_end))
        },
    }
}

/// Abridges an [`RelBoundPair`] with an [`EmptiableRelBoundPair`]
#[must_use]
pub fn abridge_rel_bound_pair_with_emptiable_rel_bound_pair(
    lhs_bound_pair: &RelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> EmptiableRelBoundPair {
    let EmptiableRelBoundPair::Bound(rhs_non_empty_bound_pair) = rhs_bound_pair else {
        return EmptiableRelBoundPair::Bound(lhs_bound_pair.clone());
    };

    abridge_rel_bound_pair(lhs_bound_pair, rhs_non_empty_bound_pair)
}

/// Abridges two [`EmptiableRelBoundPair`]s
#[must_use]
pub fn abridge_emptiable_rel_bound_pair(
    lhs_bound_pair: &EmptiableRelBoundPair,
    rhs_bound_pair: &EmptiableRelBoundPair,
) -> EmptiableRelBoundPair {
    match (lhs_bound_pair, rhs_bound_pair) {
        (EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Empty) => EmptiableRelBoundPair::Empty,
        (EmptiableRelBoundPair::Empty, bound @ EmptiableRelBoundPair::Bound(..))
        | (bound @ EmptiableRelBoundPair::Bound(..), EmptiableRelBoundPair::Empty) => bound.clone(),
        (EmptiableRelBoundPair::Bound(lhs_bound_pair), EmptiableRelBoundPair::Bound(rhs_bound_pair)) => {
            abridge_rel_bound_pair(lhs_bound_pair, rhs_bound_pair)
        },
    }
}

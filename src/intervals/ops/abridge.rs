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

macro_rules! abridge_impl_rhs_clone {
    ($implementor:ty, $output:ty, [$($rhs:ty),*$(,)?] $(,)?) => {
        $(
            impl Abridgable<$rhs> for $implementor {
                type Output = $output;

                fn abridge(&self, rhs: &$rhs) -> Self::Output {
                    Self::Output::from(rhs.clone())
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
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let first_end_time = "2025-01-01 11:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
///
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(first_start_time).to_start_bound(),
///     AbsoluteFiniteBound::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 13:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
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
///     abridged_interval.clone().bound().ok_or("Empty abridged interval")?.start(),
///     AbsoluteFiniteBound::new_with_inclusivity(
///         first_end_time,
///         BoundInclusivity::Exclusive,
///     ).to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval.clone().bound().ok_or("Empty abridged interval")?.end(),
///     AbsoluteFiniteBound::new_with_inclusivity(
///         second_start_time,
///         BoundInclusivity::Exclusive,
///     ).to_end_bound(),
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
/// let first_start_time = "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let first_end_time = "2025-01-01 13:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
///
/// let first_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(first_start_time).to_start_bound(),
///     AbsoluteFiniteBound::new(first_end_time).to_end_bound(),
/// );
///
/// let second_start_time = "2025-01-01 11:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
/// let second_end_time = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp();
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
///     abridged_interval.clone().bound().ok_or("Empty abridged interval")?.start(),
///     AbsoluteFiniteBound::new_with_inclusivity(
///         second_start_time,
///         BoundInclusivity::Inclusive,
///     ).to_start_bound(),
/// );
/// assert_eq!(
///     abridged_interval.clone().bound().ok_or("Empty abridged interval")?.end(),
///     AbsoluteFiniteBound::new_with_inclusivity(
///         first_end_time,
///         BoundInclusivity::Inclusive,
///     ).to_end_bound(),
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

impl<Rhs> Abridgable<Rhs> for AbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteBoundPair;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_abs_bound_pair_with_emptiable_abs_bound_pair(&self.abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Abridgable<Rhs> for EmptiableAbsoluteBoundPair
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), &rhs.emptiable_abs_bound_pair())
    }
}

impl<Rhs> Abridgable<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(self.abs_bound_pair().abridge(&rhs.emptiable_abs_bound_pair()))
    }
}

impl<Rhs> Abridgable<Rhs> for EmptiableAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(self.emptiable_abs_bound_pair().abridge(&rhs.emptiable_abs_bound_pair()))
    }
}

impl<Rhs> Abridgable<Rhs> for BoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(self.abs_bound_pair().abridge(&rhs.emptiable_abs_bound_pair()))
    }
}

impl<Rhs> Abridgable<Rhs> for HalfBoundedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBoundPair,
{
    type Output = EmptiableAbsoluteInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(self.abs_bound_pair().abridge(&rhs.emptiable_abs_bound_pair()))
    }
}

impl<Rhs> Abridgable<Rhs> for RelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeBoundPair;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_rel_bound_pair_with_emptiable_rel_bound_pair(&self.rel_bound_pair(), &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Abridgable<Rhs> for EmptiableRelativeBoundPair
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = Self;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        abridge_emptiable_rel_bound_pair(self, &rhs.emptiable_rel_bound_pair())
    }
}

impl<Rhs> Abridgable<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(self.rel_bound_pair().abridge(&rhs.emptiable_rel_bound_pair()))
    }
}

impl<Rhs> Abridgable<Rhs> for BoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(self.rel_bound_pair().abridge(&rhs.emptiable_rel_bound_pair()))
    }
}

impl<Rhs> Abridgable<Rhs> for HalfBoundedRelativeInterval
where
    Rhs: HasEmptiableRelativeBoundPair,
{
    type Output = EmptiableRelativeInterval;

    fn abridge(&self, rhs: &Rhs) -> Self::Output {
        Self::Output::from(self.rel_bound_pair().abridge(&rhs.emptiable_rel_bound_pair()))
    }
}

abridge_impl_rhs_clone!(
    UnboundedInterval,
    AbsoluteInterval,
    [
        AbsoluteBoundPair,
        AbsoluteInterval,
        BoundedAbsoluteInterval,
        HalfBoundedAbsoluteInterval,
    ]
);
abridge_impl_rhs_clone!(
    UnboundedInterval,
    EmptiableAbsoluteInterval,
    [EmptiableAbsoluteBoundPair, EmptiableAbsoluteInterval,]
);
abridge_impl_rhs_clone!(
    UnboundedInterval,
    RelativeInterval,
    [
        RelativeBoundPair,
        RelativeInterval,
        BoundedRelativeInterval,
        HalfBoundedRelativeInterval,
    ]
);
abridge_impl_rhs_clone!(
    UnboundedInterval,
    EmptiableRelativeInterval,
    [EmptiableRelativeBoundPair, EmptiableRelativeInterval,]
);

abridge_impl_rhs_clone!(
    EmptyInterval,
    AbsoluteInterval,
    [
        AbsoluteBoundPair,
        AbsoluteInterval,
        BoundedAbsoluteInterval,
        HalfBoundedAbsoluteInterval,
    ]
);
abridge_impl_rhs_clone!(
    EmptyInterval,
    EmptiableAbsoluteInterval,
    [EmptiableAbsoluteBoundPair, EmptiableAbsoluteInterval,]
);
abridge_impl_rhs_clone!(
    EmptyInterval,
    RelativeInterval,
    [
        RelativeBoundPair,
        RelativeInterval,
        BoundedRelativeInterval,
        HalfBoundedRelativeInterval,
    ]
);
abridge_impl_rhs_clone!(
    EmptyInterval,
    EmptiableRelativeInterval,
    [EmptiableRelativeBoundPair, EmptiableRelativeInterval,]
);

impl Abridgable<UnboundedInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn abridge(&self, _rhs: &UnboundedInterval) -> Self::Output {
        *self
    }
}

impl Abridgable<EmptyInterval> for EmptyInterval {
    type Output = EmptyInterval;

    fn abridge(&self, _rhs: &EmptyInterval) -> Self::Output {
        *self
    }
}

/// Abridges two [`AbsoluteBoundPair`]s
#[must_use]
pub fn abridge_abs_bound_pair(
    og_bounds: &AbsoluteBoundPair,
    other_bounds: &AbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    let mut highest_start = match (og_bounds.abs_start(), other_bounds.abs_start()) {
        (AbsoluteStartBound::InfinitePast, bound @ AbsoluteStartBound::Finite(..))
        | (
            bound @ (AbsoluteStartBound::Finite(..) | AbsoluteStartBound::InfinitePast),
            AbsoluteStartBound::InfinitePast,
        ) => bound,
        (og_bound @ AbsoluteStartBound::Finite(..), other_bound @ AbsoluteStartBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    let mut lowest_end = match (og_bounds.abs_end(), other_bounds.abs_end()) {
        (AbsoluteEndBound::InfiniteFuture, bound @ AbsoluteEndBound::Finite(..))
        | (
            bound @ (AbsoluteEndBound::Finite(..) | AbsoluteEndBound::InfiniteFuture),
            AbsoluteEndBound::InfiniteFuture,
        ) => bound,
        (og_bound @ AbsoluteEndBound::Finite(..), other_bound @ AbsoluteEndBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
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
    og_bounds: &AbsoluteBoundPair,
    other_bounds: &EmptiableAbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    let EmptiableAbsoluteBoundPair::Bound(other_non_empty_bounds) = other_bounds else {
        return EmptiableAbsoluteBoundPair::Bound(og_bounds.clone());
    };

    abridge_abs_bound_pair(og_bounds, other_non_empty_bounds)
}

/// Abridges two [`EmptiableAbsoluteBoundPair`]s
#[must_use]
pub fn abridge_emptiable_abs_bound_pair(
    og_bounds: &EmptiableAbsoluteBoundPair,
    other_bounds: &EmptiableAbsoluteBoundPair,
) -> EmptiableAbsoluteBoundPair {
    match (og_bounds, other_bounds) {
        (EmptiableAbsoluteBoundPair::Empty, EmptiableAbsoluteBoundPair::Empty) => EmptiableAbsoluteBoundPair::Empty,
        (EmptiableAbsoluteBoundPair::Empty, bound @ EmptiableAbsoluteBoundPair::Bound(..))
        | (bound @ EmptiableAbsoluteBoundPair::Bound(..), EmptiableAbsoluteBoundPair::Empty) => bound.clone(),
        (EmptiableAbsoluteBoundPair::Bound(og_bounds), EmptiableAbsoluteBoundPair::Bound(other_bounds)) => {
            abridge_abs_bound_pair(og_bounds, other_bounds)
        },
    }
}

/// Abridges two [`RelativeBoundPair`]s
#[must_use]
pub fn abridge_rel_bound_pair(
    og_bounds: &RelativeBoundPair,
    other_bounds: &RelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    let mut highest_start = match (og_bounds.rel_start(), other_bounds.rel_start()) {
        (RelativeStartBound::InfinitePast, bound @ RelativeStartBound::Finite(..))
        | (
            bound @ (RelativeStartBound::Finite(..) | RelativeStartBound::InfinitePast),
            RelativeStartBound::InfinitePast,
        ) => bound,
        (og_bound @ RelativeStartBound::Finite(..), other_bound @ RelativeStartBound::Finite(..)) => {
            if og_bound >= other_bound { og_bound } else { other_bound }
        },
    };

    let mut lowest_end = match (og_bounds.rel_end(), other_bounds.rel_end()) {
        (RelativeEndBound::InfiniteFuture, bound @ RelativeEndBound::Finite(..))
        | (
            bound @ (RelativeEndBound::Finite(..) | RelativeEndBound::InfiniteFuture),
            RelativeEndBound::InfiniteFuture,
        ) => bound,
        (og_bound @ RelativeEndBound::Finite(..), other_bound @ RelativeEndBound::Finite(..)) => {
            if og_bound <= other_bound { og_bound } else { other_bound }
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
    og_bounds: &RelativeBoundPair,
    other_bounds: &EmptiableRelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    let EmptiableRelativeBoundPair::Bound(other_non_empty_bounds) = other_bounds else {
        return EmptiableRelativeBoundPair::Bound(og_bounds.clone());
    };

    abridge_rel_bound_pair(og_bounds, other_non_empty_bounds)
}

/// Abridges two [`EmptiableRelativeBoundPair`]s
#[must_use]
pub fn abridge_emptiable_rel_bound_pair(
    og_bounds: &EmptiableRelativeBoundPair,
    other_bounds: &EmptiableRelativeBoundPair,
) -> EmptiableRelativeBoundPair {
    match (og_bounds, other_bounds) {
        (EmptiableRelativeBoundPair::Empty, EmptiableRelativeBoundPair::Empty) => EmptiableRelativeBoundPair::Empty,
        (EmptiableRelativeBoundPair::Empty, bound @ EmptiableRelativeBoundPair::Bound(..))
        | (bound @ EmptiableRelativeBoundPair::Bound(..), EmptiableRelativeBoundPair::Empty) => bound.clone(),
        (EmptiableRelativeBoundPair::Bound(og_bounds), EmptiableRelativeBoundPair::Bound(other_bounds)) => {
            abridge_rel_bound_pair(og_bounds, other_bounds)
        },
    }
}

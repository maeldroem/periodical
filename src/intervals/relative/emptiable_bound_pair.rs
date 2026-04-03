//! Emptiable absolute bound pair
//!
//! Similar to [absolute bound pair](crate::intervals::absolute::bound_pair),
//! but has the extra ability of being able to represent an [empty interval](crate::intervals::special::EmptyInterval).

use std::cmp::Ordering;
use std::ops::RangeBounds;
use std::time::Duration;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    IsEmpty,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Possession of possibly empty relative bound pair
pub trait HasEmptiableRelativeBoundPair {
    /// Returns the [`EmptiableRelativeBoundPair`] of the object
    #[must_use]
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelativeBoundPair;

    /// Returns [the relative start bound](RelativeStartBound) of the object, if
    /// applicable
    #[must_use]
    fn partial_rel_start(&self) -> Option<RelativeStartBound>;

    /// Returns [the relative end bound](RelativeEndBound) of the object, if
    /// applicable
    #[must_use]
    fn partial_rel_end(&self) -> Option<RelativeEndBound>;
}

/// All implementors of [`HasRelativeBoundPair`] implement
/// [`HasEmptiableRelativeBoundPair`]. This could change in the future to
/// separate emptiable from non-emptiable bounds.
impl<T> HasEmptiableRelativeBoundPair for T
where
    T: HasRelativeBoundPair,
{
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelativeBoundPair {
        EmptiableRelativeBoundPair::Bound(self.rel_bound_pair())
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        Some(self.rel_start())
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        Some(self.rel_end())
    }
}

/// Enum containing [`RelativeBoundPair`] but with support for
/// [empty intervals](crate::intervals::special::EmptyInterval)
///
/// For more information, check [`RelativeBoundPair`],
/// [`EmptyInterval`], or [`crate::intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableRelativeBoundPair {
    Bound(RelativeBoundPair),
    Empty,
}

impl EmptiableRelativeBoundPair {
    /// Creates an [`EmptiableRelativeBoundPair`] from a [`SignedDuration`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBound, EmptiableRelativeBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = SignedDuration::from_hours(8);
    /// let end = SignedDuration::from_hours(16);
    ///
    /// let emptiable_bounds = EmptiableRelativeBoundPair::from_range(start..end);
    ///
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bounds| bounds.start()),
    ///     Some(RelativeFiniteBound::new(start).to_start_bound()),
    /// );
    /// assert_eq!(
    ///     emptiable_bounds.clone().bound().map(|bounds| bounds.end()),
    ///     Some(RelativeFiniteBound::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound()),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        RelativeBoundPair::from_range(range).to_emptiable()
    }

    /// Compares two [`EmptiableRelativeBoundPair`], but if they have the same
    /// start, order by decreasing length
    ///
    /// Uses [`RelativeBoundPair::ord_by_start_and_inv_length`] under the hood
    /// for the [`Bound`](EmptiableRelativeBoundPair::Bound) variants and
    /// [`EmptiableRelativeBoundPair::cmp`]
    /// for the [`Empty`](EmptiableRelativeBoundPair::Empty) variants (which
    /// will just place all empty bounds before any bound bounds).
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::EmptiableRelativeBoundPair;
    /// # let mut bounds: [EmptiableRelativeBoundPair; 0] = [];
    /// bounds.sort_by(EmptiableRelativeBoundPair::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match (self, other) {
            (
                EmptiableRelativeBoundPair::Bound(og_rel_bound_pair),
                EmptiableRelativeBoundPair::Bound(other_rel_bound_pair),
            ) => og_rel_bound_pair.ord_by_start_and_inv_length(other_rel_bound_pair),
            _ => self.cmp(other),
        }
    }

    /// Returns the content of the [`Bound`](EmptiableRelativeBoundPair::Bound)
    /// variant
    ///
    /// Consumes `self` and puts the content of the
    /// [`Bound`](EmptiableRelativeBoundPair::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method
    /// returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::{
    /// #     EmptiableRelativeBoundPair, RelativeBoundPair, RelativeEndBound, RelativeStartBound,
    /// # };
    /// let bounds = RelativeBoundPair::new(
    ///     RelativeStartBound::InfinitePast,
    ///     RelativeEndBound::InfiniteFuture,
    /// );
    /// // Cloning is only for making the use of `bounds` okay in the following assertions
    /// let bound_emptiable_bounds = EmptiableRelativeBoundPair::Bound(bounds.clone());
    /// let empty_emptiable_bounds = EmptiableRelativeBoundPair::Empty;
    ///
    /// assert_eq!(bound_emptiable_bounds.bound(), Some(bounds));
    /// assert_eq!(empty_emptiable_bounds.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<RelativeBoundPair> {
        match self {
            EmptiableRelativeBoundPair::Empty => None,
            EmptiableRelativeBoundPair::Bound(bound) => Some(bound),
        }
    }

    /// Converts the [`EmptiableRelativeBoundPair`] into [`EmptiableRelativeInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableRelativeInterval {
        EmptiableRelativeInterval::from(self)
    }
}

impl Interval for EmptiableRelativeBoundPair {}

impl HasEmptiableRelativeBoundPair for EmptiableRelativeBoundPair {
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelativeBoundPair {
        self.clone()
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(bounds.start()),
        }
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(bounds.end()),
        }
    }
}

impl IsEmpty for EmptiableRelativeBoundPair {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableRelativeBoundPair {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(Duration::ZERO, Epsilon::None),
        }
    }
}

impl HasOpenness for EmptiableRelativeBoundPair {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableRelativeBoundPair {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl PartialOrd for EmptiableRelativeBoundPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableRelativeBoundPair {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableRelativeBoundPair::Empty, EmptiableRelativeBoundPair::Empty) => Ordering::Equal,
            (EmptiableRelativeBoundPair::Empty, EmptiableRelativeBoundPair::Bound(_)) => Ordering::Less,
            (EmptiableRelativeBoundPair::Bound(_), EmptiableRelativeBoundPair::Empty) => Ordering::Greater,
            (
                EmptiableRelativeBoundPair::Bound(og_rel_bound_pair),
                EmptiableRelativeBoundPair::Bound(other_rel_bound_pair),
            ) => og_rel_bound_pair.cmp(other_rel_bound_pair),
        }
    }
}

/// Converts `(bool, RelativeStartBound, RelativeEndBound)` into [`EmptiableRelativeBoundPair`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an empty interval.
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, RelativeStartBound, RelativeEndBound)> for EmptiableRelativeBoundPair {
    fn from((is_empty, start, end): (bool, RelativeStartBound, RelativeEndBound)) -> Self {
        if is_empty {
            return Self::Empty;
        }

        Self::from(RelativeBoundPair::new(start, end))
    }
}

/// Converts `(bool, Option<SignedDuration>, Option<SignedDuration>)` into
/// [`EmptiableRelativeBoundPair`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an empty interval.
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, Option<SignedDuration>, Option<SignedDuration>)> for EmptiableRelativeBoundPair {
    fn from((is_empty, start_opt, end_opt): (bool, Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        let start = RelativeStartBound::from(start_opt);
        let end = RelativeEndBound::from(end_opt);
        Self::from((is_empty, start, end))
    }
}

/// Converts `(bool, Option<(SignedDuration, BoundInclusivity)>, Option<(SignedDuration, BoundInclusivity)>)`
/// into [`EmptiableRelativeBoundPair`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an empty interval.
/// If it is set to `true`, the next elements are ignored altogether.
impl
    From<(
        bool,
        Option<(SignedDuration, BoundInclusivity)>,
        Option<(SignedDuration, BoundInclusivity)>,
    )> for EmptiableRelativeBoundPair
{
    fn from(
        (is_empty, start_opt, end_opt): (
            bool,
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        let start = RelativeStartBound::from(start_opt);
        let end = RelativeEndBound::from(end_opt);
        Self::from((is_empty, start, end))
    }
}

impl From<RelativeBoundPair> for EmptiableRelativeBoundPair {
    fn from(value: RelativeBoundPair) -> Self {
        EmptiableRelativeBoundPair::Bound(value)
    }
}

impl From<BoundedRelativeInterval> for EmptiableRelativeBoundPair {
    fn from(value: BoundedRelativeInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<HalfBoundedRelativeInterval> for EmptiableRelativeBoundPair {
    fn from(value: HalfBoundedRelativeInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<RelativeInterval> for EmptiableRelativeBoundPair {
    fn from(value: RelativeInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<EmptiableRelativeInterval> for EmptiableRelativeBoundPair {
    fn from(value: EmptiableRelativeInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<UnboundedInterval> for EmptiableRelativeBoundPair {
    fn from(value: UnboundedInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

impl From<EmptyInterval> for EmptiableRelativeBoundPair {
    fn from(value: EmptyInterval) -> Self {
        value.emptiable_rel_bound_pair()
    }
}

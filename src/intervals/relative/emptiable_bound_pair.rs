//! Emptiable absolute bound pair
//! 
//! Similar to [absolute bound pair](crate::intervals::absolute::bound_pair), but has the extra
//! ability of being able to represent an [empty interval](crate::intervals::special::EmptyInterval).

use std::cmp::Ordering;
use std::time::Duration;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::relative::{HasRelativeBoundPair, RelativeBoundPair, RelativeEndBound, RelativeStartBound};
use crate::intervals::meta::{
    Duration as IntervalDuration, Emptiable, Epsilon, HasDuration, HasOpenness, HasRelativity, Interval, Openness,
    Relativity,
};

/// Possession of possibly empty relative bound pair
pub trait HasEmptiableRelativeBoundPair {
    /// Returns the [`EmptiableRelativeBoundPair`] of the object
    #[must_use]
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelativeBoundPair;

    /// Returns [the relative start bound](RelativeStartBound) of the object, if applicable
    #[must_use]
    fn partial_rel_start(&self) -> Option<RelativeStartBound>;

    /// Returns [the relative end bound](RelativeEndBound) of the object, if applicable
    #[must_use]
    fn partial_rel_end(&self) -> Option<RelativeEndBound>;
}

/// All implementors of [`HasRelativeBoundPair`] implement [`HasEmptiableRelativeBoundPair`].
/// This could change in the future to separate emptiable from non-emptiable bounds.
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
/// For more information, check [`RelativeBoundPair`], [`EmptyInterval`](crate::intervals::special::EmptyInterval),
/// or [`crate::intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableRelativeBoundPair {
    Empty,
    Bound(RelativeBoundPair),
}

impl EmptiableRelativeBoundPair {
    /// Returns the content of the [`Bound`](EmptiableRelativeBoundPair::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableRelativeBoundPair::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
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

    /// Compares two [`EmptiableRelativeBoundPair`], but if they have the same start, order by decreasing length
    ///
    /// Uses [`RelativeBoundPair::ord_by_start_and_inv_length`] under the hood for
    /// the [`Bound`](EmptiableRelativeBoundPair::Bound) variants and [`EmptiableRelativeBoundPair::cmp`]
    /// for the [`Empty`](EmptiableRelativeBoundPair::Empty) variants (which will just place all empty bounds before
    /// any bound bounds).
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
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
                EmptiableRelativeBoundPair::Bound(other_rel_bound_pair)
            ) => {
                og_rel_bound_pair.ord_by_start_and_inv_length(other_rel_bound_pair)
            },
            _ => self.cmp(other),
        }
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

impl Emptiable for EmptiableRelativeBoundPair {
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
            (EmptiableRelativeBoundPair::Bound(og_rel_bound_pair), EmptiableRelativeBoundPair::Bound(other_rel_bound_pair)) => {
                og_rel_bound_pair.cmp(other_rel_bound_pair)
            },
        }
    }
}

impl From<RelativeBoundPair> for EmptiableRelativeBoundPair {
    fn from(value: RelativeBoundPair) -> Self {
        EmptiableRelativeBoundPair::Bound(value)
    }
}

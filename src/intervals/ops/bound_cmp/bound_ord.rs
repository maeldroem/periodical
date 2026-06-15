//! Ordering for bounds with support for [bound overlap ambiguity](BoundOverlapAmbiguity)
//!
//! Allows for total ordering of bounds with support for [`BoundOverlapAmbiguity`],
//! which in turn allows for more precise treatment of those ambiguities.
//!
//! When using [`PartialOrd`] on bounds instead of [`BoundOrd`], only their positions (time/offset) can be compared,
//! as explained by the [module documentation](crate::intervals::ops::bound_cmp).
//!
//! # Examples
//!
//! ```
//! # use std::cmp::Ordering;
//! # use std::error::Error;
//! # use jiff::Timestamp;
//! # use periodical::intervals::absolute::AbsFiniteBoundPos;
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
//! let ref_bound =
//!     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
//!
//! let compared_bound = AbsFiniteBoundPos::new_with_incl(
//!     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
//!     BoundInclusivity::Exclusive,
//! )
//! .to_start_bound();
//!
//! // Basic comparison using `Ord`
//! assert_eq!(ref_bound.cmp(&compared_bound), Ordering::Less);
//!
//! // Semantic bound comparison using `BoundOrd`
//! assert_eq!(
//!     ref_bound
//!         .bound_cmp(&compared_bound)
//!         .disambiguate(BoundOverlapDisambiguationRuleSet::Strict),
//!     Ordering::Less,
//! );
//! assert_eq!(
//!     ref_bound
//!         .bound_cmp(&compared_bound)
//!         .disambiguate(BoundOverlapDisambiguationRuleSet::Lenient),
//!     Ordering::Equal,
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::ops::BoundEq;
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity,
    BoundOverlapDisambiguationRuleSet,
    DisambiguatedBoundOverlap,
};

/// [`Ordering`] for bounds with support for [`BoundOverlapAmbiguity`]
///
/// Similar structure to the standard [`Ordering`], but with support for
/// [`BoundOverlapAmbiguity`] when the bounds are equal in position (time/offset).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum BoundOrdering {
    Less,
    Equal(Option<BoundOverlapAmbiguity>),
    Greater,
}

impl BoundOrdering {
    /// Strips the ambiguity info from [`BoundOrdering`]
    ///
    /// Gets rid of the stored [`BoundOverlapAmbiguity`], without resolving it,
    /// just ignoring it, resulting in an [`Ordering`].
    #[must_use]
    pub fn strip(self) -> Ordering {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(_) => Ordering::Equal,
            Self::Greater => Ordering::Greater,
        }
    }

    /// Disambiguates a [`BoundOrdering`] using a
    /// [`BoundOverlapDisambiguationRuleSet`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
    /// let ref_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     compared_bound
    ///         .bound_cmp(&ref_bound)
    ///         .disambiguate(BoundOverlapDisambiguationRuleSet::Lenient),
    ///     Ordering::Equal,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn disambiguate(self, rule_set: BoundOverlapDisambiguationRuleSet) -> Ordering {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(None) => Ordering::Equal,
            Self::Equal(Some(ambiguity)) => match ambiguity.disambiguate(rule_set) {
                DisambiguatedBoundOverlap::Before => Ordering::Less,
                DisambiguatedBoundOverlap::Equal => Ordering::Equal,
                DisambiguatedBoundOverlap::After => Ordering::Greater,
            },
            Self::Greater => Ordering::Greater,
        }
    }

    /// Disambiguates a [`BoundOrdering`] using the given closure
    ///
    /// Uses the given closure in order to resolve any [`BoundOverlapAmbiguity`]
    /// into a [`DisambiguatedBoundOverlap`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrd,
    /// #     BoundOverlapAmbiguity,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// #     DisambiguatedBoundOverlap,
    /// # };
    /// let ref_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let compared_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let mut ref_bound_exclusive = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// let compared_bound_exclusive = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// // Disambiguation closure that only considers exclusive bounds equal
    /// let disambiguation_closure = |ambiguity: BoundOverlapAmbiguity| -> DisambiguatedBoundOverlap {
    ///     match ambiguity {
    ///         BoundOverlapAmbiguity::BothStarts(i1, i2) => {
    ///             if matches!(
    ///                 (i1, i2),
    ///                 (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive),
    ///             ) {
    ///                 DisambiguatedBoundOverlap::Equal
    ///             } else {
    ///                 DisambiguatedBoundOverlap::Before
    ///             }
    ///         },
    ///         _ => unimplemented!(),
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     ref_bound
    ///         .bound_cmp(&compared_bound)
    ///         .disambiguate_using(disambiguation_closure),
    ///     Ordering::Less,
    /// );
    ///
    /// assert_eq!(
    ///     ref_bound_exclusive
    ///         .bound_cmp(&compared_bound_exclusive)
    ///         .disambiguate_using(disambiguation_closure),
    ///     Ordering::Equal,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn disambiguate_using<F>(self, f: F) -> Ordering
    where
        F: FnOnce(BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap,
    {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(None) => Ordering::Equal,
            Self::Equal(Some(ambiguity)) => match ambiguity.disambiguate_using(f) {
                DisambiguatedBoundOverlap::Before => Ordering::Less,
                DisambiguatedBoundOverlap::Equal => Ordering::Equal,
                DisambiguatedBoundOverlap::After => Ordering::Greater,
            },
            Self::Greater => Ordering::Greater,
        }
    }
}

/// Total bound ordering
///
/// This trait allows for ordering bounds, taking into account [`BoundOverlapAmbiguity`]
/// when bounds have the same position (time/offset).
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::AbsFiniteBoundPos;
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::{BoundOrdering, BoundOrd, BoundOverlapAmbiguity};
/// let ref_bound =
///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
///
/// let compared_bound = AbsFiniteBoundPos::new_with_incl(
///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
///     BoundInclusivity::Exclusive,
/// )
/// .to_start_bound();
///
/// assert_eq!(
///     ref_bound.bound_cmp(&compared_bound),
///     BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
///         BoundInclusivity::Inclusive,
///         BoundInclusivity::Exclusive,
///     ))),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait BoundOrd<Rhs = Self>: BoundEq<Rhs>
where
    Rhs: ?Sized,
{
    /// Compares two bounds
    ///
    /// Compares `self` with the given `other` bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::{BoundOrdering, BoundOrd, BoundOverlapAmbiguity};
    /// let ref_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     ref_bound.bound_cmp(&compared_bound),
    ///     BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
    ///         BoundInclusivity::Inclusive,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_cmp(&self, other: &Rhs) -> BoundOrdering;

    /// Returns whether `self` is less than the given other bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrdering,
    /// #     BoundOrd,
    /// #     BoundOverlapAmbiguity,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(ref_bound.bound_lt(&compared_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_lt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.bound_cmp(other).disambiguate(rule_set).is_lt()
    }

    /// Returns whether `self` is less than or equal to the given other bound
    /// using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrdering,
    /// #     BoundOrd,
    /// #     BoundOverlapAmbiguity,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(ref_bound.bound_le(&compared_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_le(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.bound_cmp(other).disambiguate(rule_set).is_le()
    }

    /// Returns whether `self` is greater than the given other bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrdering,
    /// #     BoundOrd,
    /// #     BoundOverlapAmbiguity,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(!ref_bound.bound_gt(&compared_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_gt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.bound_cmp(other).disambiguate(rule_set).is_gt()
    }

    /// Returns whether `self` is greater than or equal to the given other bound
    /// using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrdering,
    /// #     BoundOrd,
    /// #     BoundOverlapAmbiguity,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound =
    ///     AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(!ref_bound.bound_ge(&compared_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_ge(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        self.bound_cmp(other).disambiguate(rule_set).is_ge()
    }
}

/// Extrema operations on bounds
///
/// Extrema operations are all operations relative to extremes, e.g. maximum, minimum, clamp, …
///
/// Since all extrema operations need to have the same input types to have a consistent output type,
/// they can't be stored in [`BoundOrd`].
/// If for example, you want the maximum between an [`AbsStartBound`](crate::intervals::absolute::AbsStartBound)
/// and an [`AbsEndBound`](crate::intervals::absolute::AbsEndBound), that is still possible, although you will
/// have to go through a subtype of both, in this case [`AbsBound`](crate::intervals::absolute::AbsBound).
pub trait BoundOrdExtremaOps: BoundOrd {
    /// Returns the maximum between `self` and another bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrdExtremaOps,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let one = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let two = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    ///
    /// assert_eq!(
    ///     one.bound_max(two, BoundOverlapDisambiguationRuleSet::Strict),
    ///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
    ///         .to_finite_start_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_max(self, other: Self, rule_set: BoundOverlapDisambiguationRuleSet) -> Self
    where
        Self: Sized,
    {
        if other.bound_lt(&self, rule_set) { self } else { other }
    }

    /// Returns the minimum between `self` and another bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrdExtremaOps,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let one = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let two = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    ///
    /// assert_eq!(
    ///     one.bound_min(two, BoundOverlapDisambiguationRuleSet::Strict),
    ///     AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///         .to_finite_start_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_min(self, other: Self, rule_set: BoundOverlapDisambiguationRuleSet) -> Self
    where
        Self: Sized,
    {
        if other.bound_lt(&self, rule_set) { other } else { self }
    }

    /// Clamps a value between a minimum and a maximum bound using the given rule set
    ///
    /// # Panics
    ///
    /// Panics if the given minimum is greater than the maximum.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::AbsFiniteBoundPos;
    /// # use periodical::intervals::ops::{
    /// #     BoundOrdExtremaOps,
    /// #     BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let min = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let max = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    /// let compared = AbsFiniteBoundPos::new("2026-01-01 20:00:00Z".parse::<Timestamp>()?)
    ///     .to_finite_start_bound();
    ///
    /// assert_eq!(
    ///     compared.bound_clamp(min, max, BoundOverlapDisambiguationRuleSet::Strict),
    ///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
    ///         .to_finite_start_bound()
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_clamp(self, min: Self, max: Self, rule_set: BoundOverlapDisambiguationRuleSet) -> Self
    where
        Self: Sized,
    {
        assert!(min.bound_le(&max, rule_set));
        if self.bound_lt(&min, rule_set) {
            min
        } else if self.bound_gt(&max, rule_set) {
            max
        } else {
            self
        }
    }
}

/// Compares and returns the maximum of two bounds using the given rule set
///
/// Internally uses [`BoundOrdExtremaOps::bound_max`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::AbsFiniteBoundPos;
/// # use periodical::intervals::ops::{
/// #     bound_max,
/// #     BoundOverlapDisambiguationRuleSet,
/// # };
/// let one = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
///     .to_finite_start_bound();
/// let two = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
///     .to_finite_start_bound();
///
/// assert_eq!(
///     bound_max(one, two, BoundOverlapDisambiguationRuleSet::Strict),
///     AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
///         .to_finite_start_bound()
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[must_use]
pub fn bound_max<T>(a: T, b: T, rule_set: BoundOverlapDisambiguationRuleSet) -> T
where
    T: BoundOrdExtremaOps,
{
    a.bound_max(b, rule_set)
}

/// Compares and returns the minimum of two bounds using the given rule set
///
/// Internally uses [`BoundOrdExtremaOps::bound_min`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Timestamp;
/// # use periodical::intervals::absolute::AbsFiniteBoundPos;
/// # use periodical::intervals::ops::{
/// #     bound_min,
/// #     BoundOverlapDisambiguationRuleSet,
/// # };
/// let one = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?)
///     .to_finite_start_bound();
/// let two = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
///     .to_finite_start_bound();
///
/// assert_eq!(
///     bound_min(one, two, BoundOverlapDisambiguationRuleSet::Strict),
///     AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?)
///         .to_finite_start_bound()
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[must_use]
pub fn bound_min<T>(a: T, b: T, rule_set: BoundOverlapDisambiguationRuleSet) -> T
where
    T: BoundOrdExtremaOps,
{
    a.bound_min(b, rule_set)
}

//! [Partial ordering](PartialOrd) for bounds with support for [bound overlap ambiguity](BoundOverlapAmbiguity)
//!
//! Allows for partial ordering of bounds with support for
//! [`BoundOverlapAmbiguity`], which in turn allows for more precise treatment
//! of those ambiguities.
//!
//! When using [`PartialOrd`] on bounds instead of [`PartialBoundOrd`], only the
//! result of bound overlap disambiguation using [the strict rule set](BoundOverlapDisambiguationRuleSet::Strict)
//! is returned, whereas [`PartialBoundOrd`] exposes the ambiguity and therefore makes it possible to
//! use other [`BoundOverlapDisambiguationRuleSet`]s or simply treat them in a custom way.
//!
//! Using [`PartialBoundOrd`] will result in a [`BoundOrdering`], that you can
//! then disambiguate into a classical [`Ordering`] using either
//! [stripping](BoundOrdering::strip) (getting rid of the ambiguities without
//! resolving them), [rule sets](BoundOverlapDisambiguationRuleSet),
//! or a [custom closure](BoundOrdering::disambiguate_using).
//!
//! # Examples
//!
//! ```
//! # use std::cmp::Ordering;
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::AbsFiniteBoundPos;
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::bound_ord::PartialBoundOrd;
//! # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
//! let ref_bound = AbsFiniteBoundPos::new(
//!     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//! ).to_start_bound();
//!
//! let compared_bound = AbsFiniteBoundPos::new_with_incl(
//!     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
//!     BoundInclusivity::Exclusive,
//! ).to_start_bound();
//!
//! // Only strict comparison when using Ord
//! assert_eq!(compared_bound.cmp(&ref_bound), Ordering::Greater);
//!
//! // Use the disambiguation rule set you want when using PartialBoundOrd
//! assert_eq!(
//!     compared_bound
//!     .bound_cmp(&ref_bound)
//!     .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
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
/// [`BoundOverlapAmbiguity`] when the bounds are equal in position
/// (time/offset).
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
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::PartialBoundOrd;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
    /// let ref_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// ).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// ).to_start_bound();
    ///
    /// assert_eq!(
    ///     compared_bound
    ///     .bound_cmp(&ref_bound)
    ///     .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
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
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::PartialBoundOrd;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
    /// # };
    /// let ref_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// ).to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// ).to_start_bound();
    ///
    /// let mut ref_bound_exclusive = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// ).to_start_bound();
    ///
    /// let compared_bound_exclusive = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// ).to_start_bound();
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
    ///     compared_bound
    ///     .bound_cmp(&ref_bound)
    ///     .disambiguate_using(disambiguation_closure),
    ///     Ordering::Less,
    /// );
    ///
    /// assert_eq!(
    ///     compared_bound_exclusive
    ///     .bound_cmp(&ref_bound_exclusive)
    ///     .disambiguate_using(disambiguation_closure),
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

/// Partial bound ordering
///
/// This trait allows for partially ordering bounds, taking into account
/// [`BoundOverlapAmbiguity`] when bounds have the same position (time/offset).
///
/// This is a partial order as we want to allow for comparing two different
/// bound types.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
/// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
/// let ref_bound = AbsFiniteBoundPos::new(
///     "2025-01-01 08:00:00[Europe/Oslo]"
///         .parse::<Zoned>()?
///         .timestamp(),
/// )
/// .to_start_bound();
///
/// let compared_bound = AbsFiniteBoundPos::new_with_incl(
///     "2025-01-01 08:00:00[Europe/Oslo]"
///         .parse::<Zoned>()?
///         .timestamp(),
///     BoundInclusivity::Exclusive,
/// )
/// .to_start_bound();
///
/// assert_eq!(
///     compared_bound.bound_cmp(&ref_bound),
///     BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
///         BoundInclusivity::Inclusive,
///         BoundInclusivity::Exclusive,
///     ))),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
// Add note to implementors: only impl on bounds + transitivity, duality etc. must be guaranteed
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
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// let ref_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// )
    /// .to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert_eq!(
    ///     compared_bound.bound_cmp(&ref_bound),
    ///     BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
    ///         BoundInclusivity::Inclusive,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_cmp(&self, other: &Rhs) -> BoundOrdering;

    /// Returns whether `self` is less than the given other bound using the
    /// given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// )
    /// .to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(!compared_bound.bound_lt(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_lt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(ambiguity.disambiguate(rule_set), DisambiguatedBoundOverlap::Before,)
            },
            BoundOrdering::Equal(None) | BoundOrdering::Greater => false,
        }
    }

    /// Returns whether `self` is less than or equal to the given other bound
    /// using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// )
    /// .to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(!compared_bound.bound_le(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_le(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less | BoundOrdering::Equal(None) => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate(rule_set),
                    DisambiguatedBoundOverlap::Before | DisambiguatedBoundOverlap::Equal,
                )
            },
            BoundOrdering::Greater => false,
        }
    }

    /// Returns whether `self` is greater than the given other bound using the
    /// given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// )
    /// .to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(compared_bound.bound_gt(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_gt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(ambiguity.disambiguate(rule_set), DisambiguatedBoundOverlap::After,)
            },
            BoundOrdering::Equal(None) | BoundOrdering::Greater => false,
        }
    }

    /// Returns whether `self` is greater than or equal to the given other bound
    /// using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsFiniteBoundPos, AbsStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsFiniteBoundPos::new(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// )
    /// .to_start_bound();
    ///
    /// let compared_bound = AbsFiniteBoundPos::new_with_incl(
    ///     "2025-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     BoundInclusivity::Exclusive,
    /// )
    /// .to_start_bound();
    ///
    /// assert!(compared_bound.bound_ge(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn bound_ge(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less | BoundOrdering::Equal(None) => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate(rule_set),
                    DisambiguatedBoundOverlap::Equal | DisambiguatedBoundOverlap::After,
                )
            },
            BoundOrdering::Greater => false,
        }
    }
}

pub trait BoundOrdExtremaOps: BoundOrd {
    #[must_use]
    fn bound_max(self, other: Self, rule_set: BoundOverlapDisambiguationRuleSet) -> Self
    where
        Self: Sized,
    {
        if other.bound_lt(&self, rule_set) { self } else { other }
    }

    #[must_use]
    fn bound_min(self, other: Self, rule_set: BoundOverlapDisambiguationRuleSet) -> Self
    where
        Self: Sized,
    {
        if other.bound_lt(&self, rule_set) { other } else { self }
    }

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

#[must_use]
pub fn bound_max<T>(a: T, b: T, rule_set: BoundOverlapDisambiguationRuleSet) -> T
where
    T: BoundOrdExtremaOps,
{
    a.bound_max(b, rule_set)
}

#[must_use]
pub fn bound_min<T>(a: T, b: T, rule_set: BoundOverlapDisambiguationRuleSet) -> T
where
    T: BoundOrdExtremaOps,
{
    a.bound_min(b, rule_set)
}

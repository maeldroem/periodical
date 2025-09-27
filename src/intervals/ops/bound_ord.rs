//! [Partial ordering](PartialOrd) for bounds with support for [bound overlap ambiguity](BoundOverlapAmbiguity)
//!
//! Allows for partial ordering of bounds with support for [`BoundOverlapAmbiguity`],
//! which in turn allows for more precise treatment of those ambiguities.
//!
//! When using [`PartialOrd`] on bounds instead of [`PartialBoundOrd`], only the result
//! of bound overlap disambiguation using [the strict rule set](BoundOverlapDisambiguationRuleSet::Strict)
//! is returned, whereas [`PartialBoundOrd`] exposes the ambiguity and therefore makes it
//! possible to use other [`BoundOverlapDisambiguationRuleSet`]s or simply treat them in a custom way.
//!
//! Using [`PartialBoundOrd`] will result in a [`BoundOrdering`], that you can then disambiguate
//! into a classical [`Ordering`] using either [stripping](BoundOrdering::strip)
//! (getting rid of the ambiguities without resolving them), [rule sets](BoundOverlapDisambiguationRuleSet),
//! or a [custom closure](BoundOrdering::disambiguate_using).
//!
//! # Examples
//!
//! ```
//! # use std::cmp::Ordering;
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::bound_ord::PartialBoundOrd;
//! # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
//! let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//! ));
//!
//! let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
//!     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!     BoundInclusivity::Exclusive,
//! ));
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
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{RelativeBound, RelativeEndBound, RelativeStartBound};

use super::prelude::*;

/// [`Ordering`] for bounds with support for [`BoundOverlapAmbiguity`]
///
/// Similar structure to the standard [`Ordering`], but with support for [`BoundOverlapAmbiguity`]
/// when the bounds are equal in position (time/offset).
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
    /// Gets rid of the stored [`BoundOverlapAmbiguity`], without resolving it, just ignoring it,
    /// resulting in an [`Ordering`].
    #[must_use]
    pub fn strip(self) -> Ordering {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(_) => Ordering::Equal,
            Self::Greater => Ordering::Greater,
        }
    }

    /// Disambiguates a [`BoundOrdering`] using a [`BoundOverlapDisambiguationRuleSet`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::PartialBoundOrd;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapDisambiguationRuleSet;
    /// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert_eq!(
    ///     compared_bound
    ///     .bound_cmp(&ref_bound)
    ///     .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
    ///     Ordering::Equal,
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: BoundOverlapDisambiguationRuleSet) -> Ordering {
        match self {
            Self::Less => Ordering::Less,
            Self::Equal(None) => Ordering::Equal,
            Self::Equal(Some(ambiguity)) => match ambiguity.disambiguate_using_rule_set(rule_set) {
                DisambiguatedBoundOverlap::Before => Ordering::Less,
                DisambiguatedBoundOverlap::Equal => Ordering::Equal,
                DisambiguatedBoundOverlap::After => Ordering::Greater,
            },
            Self::Greater => Ordering::Greater,
        }
    }

    /// Disambiguates a [`BoundOrdering`] using the given closure
    ///
    /// Uses the given closure in order to resolve any [`BoundOverlapAmbiguity`] into a [`DisambiguatedBoundOverlap`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::PartialBoundOrd;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
    /// # };
    /// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let mut ref_bound_exclusive = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// let compared_bound_exclusive = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
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
    /// # Ok::<(), chrono::format::ParseError>(())
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
/// This trait allows for partially ordering bounds, taking into account [`BoundOverlapAmbiguity`]
/// when bounds have the same position (time/offset).
///
/// This is a partial order as we want to allow for comparing two different bound types.
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
/// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
/// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
/// ));
///
/// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     BoundInclusivity::Exclusive,
/// ));
///
/// assert_eq!(
///     compared_bound.bound_cmp(&ref_bound),
///     BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
///         BoundInclusivity::Inclusive,
///         BoundInclusivity::Exclusive,
///     ))),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait PartialBoundOrd<Rhs = Self> {
    /// Compares two bounds
    ///
    /// Compares `self` with the given `other` bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
    /// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert_eq!(
    ///     compared_bound.bound_cmp(&ref_bound),
    ///     BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
    ///         BoundInclusivity::Inclusive,
    ///         BoundInclusivity::Exclusive,
    ///     ))),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn bound_cmp(&self, other: &Rhs) -> BoundOrdering;

    /// Returns whether `self` is less than the given other bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert!(!compared_bound.bound_lt(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn bound_lt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::Before,
                )
            },
            BoundOrdering::Equal(None) | BoundOrdering::Greater => false,
        }
    }

    /// Returns whether `self` is less than or equal to the given other bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert!(!compared_bound.bound_le(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn bound_le(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less | BoundOrdering::Equal(None) => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::Before | DisambiguatedBoundOverlap::Equal,
                )
            },
            BoundOrdering::Greater => false,
        }
    }

    /// Returns whether `self` is greater than the given other bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert!(compared_bound.bound_gt(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn bound_gt(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::After,
                )
            },
            BoundOrdering::Equal(None) | BoundOrdering::Greater => false,
        }
    }

    /// Returns whether `self` is greater than or equal to the given other bound using the given rule set
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_ord::{BoundOrdering, PartialBoundOrd};
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet,
    /// # };
    /// let ref_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    /// ));
    ///
    /// let compared_bound = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///     "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     BoundInclusivity::Exclusive,
    /// ));
    ///
    /// assert!(compared_bound.bound_ge(&ref_bound, BoundOverlapDisambiguationRuleSet::Strict));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn bound_ge(&self, other: &Rhs, rule_set: BoundOverlapDisambiguationRuleSet) -> bool {
        match self.bound_cmp(other) {
            BoundOrdering::Less | BoundOrdering::Equal(None) => true,
            BoundOrdering::Equal(Some(ambiguity)) => {
                matches!(
                    ambiguity.disambiguate_using_rule_set(rule_set),
                    DisambiguatedBoundOverlap::Equal | DisambiguatedBoundOverlap::After,
                )
            },
            BoundOrdering::Greater => false,
        }
    }
}

impl PartialBoundOrd for AbsoluteStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (AbsoluteStartBound::Finite(finite_og), AbsoluteStartBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (AbsoluteStartBound::Finite(_), AbsoluteStartBound::InfinitePast) => BoundOrdering::Greater,
            (AbsoluteStartBound::InfinitePast, AbsoluteStartBound::Finite(_)) => BoundOrdering::Less,
            (AbsoluteStartBound::InfinitePast, AbsoluteStartBound::InfinitePast) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<AbsoluteEndBound> for AbsoluteStartBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        match (self, other) {
            (AbsoluteStartBound::Finite(finite_og), AbsoluteEndBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Less,
        }
    }
}

impl PartialBoundOrd<AbsoluteBound> for AbsoluteStartBound {
    fn bound_cmp(&self, other: &AbsoluteBound) -> BoundOrdering {
        match other {
            AbsoluteBound::Start(other_start) => self.bound_cmp(other_start),
            AbsoluteBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for AbsoluteEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (AbsoluteEndBound::Finite(finite_og), AbsoluteEndBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (AbsoluteEndBound::Finite(_), AbsoluteEndBound::InfiniteFuture) => BoundOrdering::Less,
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::Finite(_)) => BoundOrdering::Greater,
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::InfiniteFuture) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<AbsoluteStartBound> for AbsoluteEndBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        match (self, other) {
            (AbsoluteEndBound::Finite(finite_og), AbsoluteStartBound::Finite(finite_other)) => {
                match finite_og.time().cmp(&finite_other.time()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Greater,
        }
    }
}

impl PartialBoundOrd<AbsoluteBound> for AbsoluteEndBound {
    fn bound_cmp(&self, other: &AbsoluteBound) -> BoundOrdering {
        match other {
            AbsoluteBound::Start(other_start) => self.bound_cmp(other_start),
            AbsoluteBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for AbsoluteBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (AbsoluteBound::Start(og_start), AbsoluteBound::Start(other_start)) => og_start.bound_cmp(other_start),
            (AbsoluteBound::Start(og_start), AbsoluteBound::End(other_end)) => og_start.bound_cmp(other_end),
            (AbsoluteBound::End(og_end), AbsoluteBound::Start(other_start)) => og_end.bound_cmp(other_start),
            (AbsoluteBound::End(og_end), AbsoluteBound::End(other_end)) => og_end.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd<AbsoluteStartBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteStartBound) -> BoundOrdering {
        match self {
            AbsoluteBound::Start(og_start) => og_start.bound_cmp(other),
            AbsoluteBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

impl PartialBoundOrd<AbsoluteEndBound> for AbsoluteBound {
    fn bound_cmp(&self, other: &AbsoluteEndBound) -> BoundOrdering {
        match self {
            AbsoluteBound::Start(og_start) => og_start.bound_cmp(other),
            AbsoluteBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

impl PartialBoundOrd for RelativeStartBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (RelativeStartBound::Finite(finite_og), RelativeStartBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (RelativeStartBound::Finite(_), RelativeStartBound::InfinitePast) => BoundOrdering::Greater,
            (RelativeStartBound::InfinitePast, RelativeStartBound::Finite(_)) => BoundOrdering::Less,
            (RelativeStartBound::InfinitePast, RelativeStartBound::InfinitePast) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<RelativeEndBound> for RelativeStartBound {
    fn bound_cmp(&self, other: &RelativeEndBound) -> BoundOrdering {
        match (self, other) {
            (RelativeStartBound::Finite(finite_og), RelativeEndBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Less,
        }
    }
}

impl PartialBoundOrd<RelativeBound> for RelativeStartBound {
    fn bound_cmp(&self, other: &RelativeBound) -> BoundOrdering {
        match other {
            RelativeBound::Start(other_start) => self.bound_cmp(other_start),
            RelativeBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for RelativeEndBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (RelativeEndBound::Finite(finite_og), RelativeEndBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            (RelativeEndBound::Finite(_), RelativeEndBound::InfiniteFuture) => BoundOrdering::Less,
            (RelativeEndBound::InfiniteFuture, RelativeEndBound::Finite(_)) => BoundOrdering::Greater,
            (RelativeEndBound::InfiniteFuture, RelativeEndBound::InfiniteFuture) => BoundOrdering::Equal(None),
        }
    }
}

impl PartialBoundOrd<RelativeStartBound> for RelativeEndBound {
    fn bound_cmp(&self, other: &RelativeStartBound) -> BoundOrdering {
        match (self, other) {
            (RelativeEndBound::Finite(finite_og), RelativeStartBound::Finite(finite_other)) => {
                match finite_og.offset().cmp(&finite_other.offset()) {
                    Ordering::Less => BoundOrdering::Less,
                    Ordering::Equal => BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                        finite_other.inclusivity(),
                        finite_og.inclusivity(),
                    ))),
                    Ordering::Greater => BoundOrdering::Greater,
                }
            },
            _ => BoundOrdering::Greater,
        }
    }
}

impl PartialBoundOrd<RelativeBound> for RelativeEndBound {
    fn bound_cmp(&self, other: &RelativeBound) -> BoundOrdering {
        match other {
            RelativeBound::Start(other_start) => self.bound_cmp(other_start),
            RelativeBound::End(other_end) => self.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd for RelativeBound {
    fn bound_cmp(&self, other: &Self) -> BoundOrdering {
        match (self, other) {
            (RelativeBound::Start(og_start), RelativeBound::Start(other_start)) => og_start.bound_cmp(other_start),
            (RelativeBound::Start(og_start), RelativeBound::End(other_end)) => og_start.bound_cmp(other_end),
            (RelativeBound::End(og_end), RelativeBound::Start(other_start)) => og_end.bound_cmp(other_start),
            (RelativeBound::End(og_end), RelativeBound::End(other_end)) => og_end.bound_cmp(other_end),
        }
    }
}

impl PartialBoundOrd<RelativeStartBound> for RelativeBound {
    fn bound_cmp(&self, other: &RelativeStartBound) -> BoundOrdering {
        match self {
            RelativeBound::Start(og_start) => og_start.bound_cmp(other),
            RelativeBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

impl PartialBoundOrd<RelativeEndBound> for RelativeBound {
    fn bound_cmp(&self, other: &RelativeEndBound) -> BoundOrdering {
        match self {
            RelativeBound::Start(og_start) => og_start.bound_cmp(other),
            RelativeBound::End(og_end) => og_end.bound_cmp(other),
        }
    }
}

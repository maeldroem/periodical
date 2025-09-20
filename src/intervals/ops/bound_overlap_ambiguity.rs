//! Bound overlap ambiguity
//!
//! This module manages ambiguities that are created when comparing two bounds that have the same position,
//! like time for absolute bounds, or offset for relative bounds.
//!
//! The ambiguity is stored in [`BoundOverlapAmbiguity`]. It stores the source of the bounds (start/end)
//! and their inclusivities.
//! From that structure, you can then choose how to disambiguate it.
//! This is most commonly done using a [`BoundOverlapDisambiguationRuleSet`],
//! but you can also use your own closure for disambiguation.
//!
//! Once disambiguated, you obtain a [`DisambiguatedBoundOverlap`], indicating how the compared bound should be
//! interpreted relative to the reference bound.
//!
//! Most structures using [`BoundOverlapAmbiguity`] wrap it in an [`Option`], as infinite bounds can have
//! the same position (either infinitely in the past or infinitely in the future), but don't carry information
//! about inclusivity, therefore not creating an ambiguity despite them technically having the same position.
//!
//! # Examples
//!
//! ```
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::bound_overlap_ambiguity::{
//! #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
//! # };
//! let ambiguity = BoundOverlapAmbiguity::StartEnd(
//!     BoundInclusivity::Inclusive, // Reference is an inclusive start bound
//!     BoundInclusivity::Exclusive, // Compared is an exclusive end bound
//! );
//!
//! assert_eq!(
//!     ambiguity.disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
//!     DisambiguatedBoundOverlap::Before,
//! );
//! ```

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;

use crate::intervals::meta::BoundInclusivity;

/// Bound overlap ambiguity
///
/// Ambiguities occur when two compared bounds have the same position (time/offset) as the inclusivities of the bounds
/// can result in different interpretations.
///
/// Consider the following:
///
/// ```txt
/// [, ] = inclusive bounds
/// (, ) = exclusive bounds
///
/// reference:     [------]
/// compared:  [---)
/// ```
///
/// Should we consider those two intervals as overlapping? in the strict mathematical interpretation, no, but if you
/// are uniting those two intervals, then yes, as they don't have a gap in between them.
///
/// That's what the bound overlap ambiguity is for.
///
/// The first contained [`BoundInclusivity`] should always be the reference, the second should always be the compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum BoundOverlapAmbiguity {
    /// Inclusivities come from two start bounds
    BothStarts(BoundInclusivity, BoundInclusivity),
    /// Inclusivities come from two end bounds
    BothEnds(BoundInclusivity, BoundInclusivity),
    /// Inclusivities come from a start bound (reference) and an end bound (compared)
    StartEnd(BoundInclusivity, BoundInclusivity),
    /// Inclusivities come from an end bound (reference) and a start bound (compared)
    EndStart(BoundInclusivity, BoundInclusivity),
}

impl BoundOverlapAmbiguity {
    /// Whether it is of the [`BothStarts`](BoundOverlapAmbiguity::BothStarts) variant
    #[must_use]
    pub fn is_both_starts(&self) -> bool {
        matches!(self, Self::BothStarts(..))
    }

    /// Whether it is of the [`BothEnds`](BoundOverlapAmbiguity::BothEnds) variant
    #[must_use]
    pub fn is_both_ends(&self) -> bool {
        matches!(self, Self::BothEnds(..))
    }

    /// Whether it is of the [`StartEnd`](BoundOverlapAmbiguity::StartEnd) variant
    #[must_use]
    pub fn is_start_end(&self) -> bool {
        matches!(self, Self::StartEnd(..))
    }

    /// Whether it is of the [`EndStart`](BoundOverlapAmbiguity::EndStart) variant
    #[must_use]
    pub fn is_end_start(&self) -> bool {
        matches!(self, Self::EndStart(..))
    }

    /// Disambiguates the ambiguity using the given [`BoundOverlapDisambiguationRuleSet`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
    /// # };
    /// let ambiguity = BoundOverlapAmbiguity::StartEnd(
    ///     BoundInclusivity::Inclusive, // Reference is an inclusive start bound
    ///     BoundInclusivity::Exclusive, // Compared is an exclusive end bound
    /// );
    ///
    /// assert_eq!(
    ///     ambiguity.disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
    ///     DisambiguatedBoundOverlap::Before,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: BoundOverlapDisambiguationRuleSet) -> DisambiguatedBoundOverlap {
        rule_set.disambiguate(self)
    }

    /// Disambiguates the ambiguity using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, DisambiguatedBoundOverlap,
    /// # };
    /// let ambiguity = BoundOverlapAmbiguity::StartEnd(
    ///     BoundInclusivity::Inclusive, // Reference is an inclusive start bound
    ///     BoundInclusivity::Exclusive, // Compared is an exclusive end bound
    /// );
    ///
    /// let disambiguation_closure = |amb: BoundOverlapAmbiguity| -> DisambiguatedBoundOverlap {
    ///     match amb {
    ///         BoundOverlapAmbiguity::StartEnd(ref_incl, comp_incl) => {
    ///             if matches!(
    ///                 (ref_incl, comp_incl),
    ///                 (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive),
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
    ///     ambiguity.disambiguate_using(disambiguation_closure),
    ///     DisambiguatedBoundOverlap::Before,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate_using<F>(self, f: F) -> DisambiguatedBoundOverlap
    where
        F: FnOnce(Self) -> DisambiguatedBoundOverlap,
    {
        (f)(self)
    }
}

/// Rule sets to disambiguate a [`BoundOverlapAmbiguity`]
///
/// Rule sets are common strategies to resolve ambiguities.
/// If you require a custom disambiguation, see [`BoundOverlapAmbiguity::disambiguate_using`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum BoundOverlapDisambiguationRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bound inclusivities.
    ///
    /// Two bounds possessing the same point in time need to be inclusive in order to be counted as equal.
    ///
    /// This rule set is often used for overlap checks.
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// Two bounds possessing the same point in time need to be either inclusive or at least one of them
    /// needs to be exclusive (not both!) in order to be counted as equal.
    ///
    /// This rule set if often used for interval unions.
    Lenient,
    /// Very lenient rule set
    ///
    /// Two bounds possessing the same point in time are counted as equal, regardless of the inclusivity.
    VeryLenient,
    /// Continuous to future rule set
    ///
    /// Follows the same principles as [`BoundOverlapDisambiguationRuleSet::Strict`], but adds an exception:
    /// if an exclusive end bound is adjacent to an inclusive start bound, it also counts as equal.
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Follows the same principles as [`BoundOverlapDisambiguationRuleSet::Strict`], but adds an exception:
    /// if an exclusive start bound is adjacent to an inclusive end bound, it also counts as equal.
    ContinuousToPast,
}

impl BoundOverlapDisambiguationRuleSet {
    /// Uses the rule set to disambiguate a [`BoundOverlapAmbiguity`]
    ///
    /// Preferably use [`BoundOverlapAmbiguity::disambiguate_using_rule_set`] instead.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::bound_overlap_ambiguity::{
    /// #     BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
    /// # };
    /// let ambiguity = BoundOverlapAmbiguity::StartEnd(
    ///     BoundInclusivity::Inclusive, // Reference is an inclusive start bound
    ///     BoundInclusivity::Exclusive, // Compared is an exclusive end bound
    /// );
    ///
    /// assert_eq!(
    ///     BoundOverlapDisambiguationRuleSet::Strict.disambiguate(ambiguity),
    ///     DisambiguatedBoundOverlap::Before,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate(&self, ambiguity: BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap {
        match self {
            Self::Strict => strict_bound_overlap_disambiguation(ambiguity),
            Self::Lenient => lenient_bound_overlap_disambiguation(ambiguity),
            Self::VeryLenient => very_lenient_bound_overlap_disambiguation(ambiguity),
            Self::ContinuousToFuture => continuous_to_future_bound_overlap_disambiguation(ambiguity),
            Self::ContinuousToPast => continuous_to_past_bound_overlap_disambiguation(ambiguity),
        }
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`] using [the strict rule set](BoundOverlapDisambiguationRuleSet::Strict)
#[must_use]
pub fn strict_bound_overlap_disambiguation(ambiguity: BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap {
    type Boa = BoundOverlapAmbiguity;
    type Bi = BoundInclusivity;

    match ambiguity {
        Boa::BothStarts(Bi::Exclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Exclusive, Bi::Inclusive | Bi::Exclusive) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothStarts(Bi::Exclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive, Bi::Inclusive) => DisambiguatedBoundOverlap::Equal,
        Boa::BothStarts(Bi::Inclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive, Bi::Exclusive)
        | Boa::EndStart(Bi::Exclusive, Bi::Inclusive | Bi::Exclusive) => DisambiguatedBoundOverlap::After,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`] using [the lenient rule set](BoundOverlapDisambiguationRuleSet::Lenient)
#[must_use]
pub fn lenient_bound_overlap_disambiguation(ambiguity: BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap {
    type Boa = BoundOverlapAmbiguity;
    type Bi = BoundInclusivity;

    match ambiguity {
        Boa::StartEnd(Bi::Exclusive, Bi::Exclusive) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(Bi::Inclusive | Bi::Exclusive, Bi::Inclusive | Bi::Exclusive)
        | Boa::BothEnds(Bi::Inclusive | Bi::Exclusive, Bi::Inclusive | Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Inclusive | Bi::Exclusive)
        | Boa::StartEnd(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive, Bi::Inclusive | Bi::Exclusive)
        | Boa::EndStart(Bi::Exclusive, Bi::Inclusive) => DisambiguatedBoundOverlap::Equal,
        Boa::EndStart(Bi::Exclusive, Bi::Exclusive) => DisambiguatedBoundOverlap::After,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`]
/// using [the very lenient rule set](BoundOverlapDisambiguationRuleSet::VeryLenient)
#[must_use]
pub fn very_lenient_bound_overlap_disambiguation(_ambiguity: BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap {
    DisambiguatedBoundOverlap::Equal
}

/// Disambiguates a [`BoundOverlapAmbiguity`]
/// using [the continuous to future rule set](BoundOverlapDisambiguationRuleSet::ContinuousToFuture)
#[must_use]
pub fn continuous_to_future_bound_overlap_disambiguation(
    ambiguity: BoundOverlapAmbiguity,
) -> DisambiguatedBoundOverlap {
    type Boa = BoundOverlapAmbiguity;
    type Bi = BoundInclusivity;

    match ambiguity {
        Boa::BothStarts(Bi::Exclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Exclusive, Bi::Inclusive | Bi::Exclusive) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothStarts(Bi::Exclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Inclusive | Bi::Exclusive)
        | Boa::EndStart(Bi::Inclusive | Bi::Exclusive, Bi::Inclusive) => DisambiguatedBoundOverlap::Equal,
        Boa::BothStarts(Bi::Inclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive | Bi::Exclusive, Bi::Exclusive) => DisambiguatedBoundOverlap::After,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`]
/// using [the continuous to past rule set](BoundOverlapDisambiguationRuleSet::ContinuousToPast)
#[must_use]
pub fn continuous_to_past_bound_overlap_disambiguation(ambiguity: BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap {
    type Boa = BoundOverlapAmbiguity;
    type Bi = BoundInclusivity;

    match ambiguity {
        Boa::BothStarts(Bi::Exclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive | Bi::Exclusive, Bi::Exclusive) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothStarts(Bi::Exclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive | Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive, Bi::Inclusive | Bi::Exclusive) => DisambiguatedBoundOverlap::Equal,
        Boa::BothStarts(Bi::Inclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Exclusive, Bi::Inclusive | Bi::Exclusive) => DisambiguatedBoundOverlap::After,
    }
}

/// Resolved bound overlap
///
/// Represents a disambiguated [`BoundOverlapAmbiguity`], indicating the position of the compared bound
/// relative to the reference bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum DisambiguatedBoundOverlap {
    /// Compared bound is before the reference bound
    Before,
    /// Compared bound is equal to the reference bound
    Equal,
    /// Compared bound is after the reference bound
    After,
}

//! Bound inclusivity overlap ambiguity
//!
//! TODO: Make time containment positioning and overlap positioning use `Option<BoundOverlapAmbiguity>` for consistency.

use crate::intervals::meta::BoundInclusivity;

/// Ambiguity in bound overlap
///
/// If an interval bound's position is the same as a compared interval bound's position, an ambiguity is created
/// as this overlap can be interpreted in different ways.
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
/// are uniting those two intervals, then yes (as they leave no gap in between).
///
/// That's what the bound overlap ambiguity is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundOverlapAmbiguity {
    /// Inclusivities come from two start bounds
    BothStarts(BoundInclusivity, BoundInclusivity),
    /// Inclusivities come from two end bounds
    BothEnds(BoundInclusivity, BoundInclusivity),
    /// Inclusivities come from a start bound and an end bound
    StartEnd(BoundInclusivity, BoundInclusivity),
    /// Inclusivities come from an end bound and a start bound
    EndStart(BoundInclusivity, BoundInclusivity),
}

impl BoundOverlapAmbiguity {
    /// Whether the [`BoundOverlapAmbiguity`] is of the [`BothStarts`](BoundOverlapAmbiguity::BothStarts) variant
    #[must_use]
    pub fn is_both_starts(&self) -> bool {
        matches!(self, Self::BothStarts(..))
    }

    /// Whether the [`BoundOverlapAmbiguity`] is of the [`BothEnds`](BoundOverlapAmbiguity::BothEnds) variant
    #[must_use]
    pub fn is_both_ends(&self) -> bool {
        matches!(self, Self::BothEnds(..))
    }

    /// Whether the [`BoundOverlapAmbiguity`] is of the [`StartEnd`](BoundOverlapAmbiguity::StartEnd) variant
    #[must_use]
    pub fn is_start_end(&self) -> bool {
        matches!(self, Self::StartEnd(..))
    }

    /// Whether the [`BoundOverlapAmbiguity`] is of the [`EndStart`](BoundOverlapAmbiguity::EndStart) variant
    #[must_use]
    pub fn is_end_start(&self) -> bool {
        matches!(self, Self::EndStart(..))
    }

    /// Disambiguates the ambiguity using the given [`BoundOverlapDisambiguationRuleSet`]
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: BoundOverlapDisambiguationRuleSet) -> DisambiguatedBoundOverlap {
        rule_set.disambiguate(self)
    }

    /// Disambiguates the ambiguity using the given closure
    #[must_use]
    pub fn disambiguate_using<F>(self, f: F) -> DisambiguatedBoundOverlap
    where
        F: FnOnce(Self) -> DisambiguatedBoundOverlap,
    {
        (f)(self)
    }
}

/// Rule sets to disambiguate a [`BoundOverlapAmbiguity`]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum BoundOverlapDisambiguationRuleSet {
    /// Strict mathematical interpretation of bound inclusivities
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// An inclusive bound meeting an exclusive bound counts as equal
    Lenient,
    /// Very lenient rule set
    ///
    /// Even two exclusive bounds are considered equal
    VeryLenient,
    /// Continuous to future rule set
    ///
    /// Like [`Strict`](BoundOverlapDisambiguationRuleSet::Strict) but considers equal an exclusive end bound meeting
    /// an inclusive start bound
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Like [`Strict`](BoundOverlapDisambiguationRuleSet::Strict) but considers equal an exclusive start bound meeting
    /// an inclusive end bound
    ContinuousToPast,
}

impl BoundOverlapDisambiguationRuleSet {
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
        Boa::BothStarts(Bi::Inclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive, Bi::Exclusive)
        | Boa::EndStart(Bi::Exclusive, _) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothStarts(Bi::Exclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive, Bi::Inclusive) => DisambiguatedBoundOverlap::Equal,
        Boa::BothStarts(Bi::Exclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Exclusive, _) => DisambiguatedBoundOverlap::After,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`] using [the lenient rule set](BoundOverlapDisambiguationRuleSet::Lenient)
#[must_use]
pub fn lenient_bound_overlap_disambiguation(ambiguity: BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap {
    type Boa = BoundOverlapAmbiguity;
    type Bi = BoundInclusivity;

    match ambiguity {
        Boa::EndStart(Bi::Exclusive, Bi::Exclusive) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(..)
        | Boa::BothEnds(..)
        | Boa::StartEnd(Bi::Inclusive, _)
        | Boa::StartEnd(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Inclusive, _)
        | Boa::EndStart(Bi::Exclusive, Bi::Inclusive) => DisambiguatedBoundOverlap::Equal,
        Boa::StartEnd(Bi::Exclusive, Bi::Exclusive) => DisambiguatedBoundOverlap::After,
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
        Boa::BothStarts(Bi::Inclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(_, Bi::Exclusive) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothStarts(Bi::Exclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Inclusive)
        | Boa::EndStart(_, Bi::Inclusive) => DisambiguatedBoundOverlap::Equal,
        Boa::BothStarts(Bi::Exclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Exclusive, _) => DisambiguatedBoundOverlap::After,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`]
/// using [the continuous to past rule set](BoundOverlapDisambiguationRuleSet::ContinuousToPast)
#[must_use]
pub fn continuous_to_past_bound_overlap_disambiguation(ambiguity: BoundOverlapAmbiguity) -> DisambiguatedBoundOverlap {
    type Boa = BoundOverlapAmbiguity;
    type Bi = BoundInclusivity;

    match ambiguity {
        Boa::BothStarts(Bi::Inclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Inclusive)
        | Boa::EndStart(Bi::Exclusive, _) => DisambiguatedBoundOverlap::Before,
        Boa::BothStarts(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothStarts(Bi::Exclusive, Bi::Exclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Exclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Inclusive, _)
        | Boa::EndStart(Bi::Inclusive, _) => DisambiguatedBoundOverlap::Equal,
        Boa::BothStarts(Bi::Exclusive, Bi::Inclusive)
        | Boa::BothEnds(Bi::Inclusive, Bi::Exclusive)
        | Boa::StartEnd(Bi::Exclusive, _) => DisambiguatedBoundOverlap::After,
    }
}

/// Disambiguated [`BoundOverlapAmbiguity`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DisambiguatedBoundOverlap {
    /// First bound was before the second bound
    Before,
    /// First bound was equal to the second bound
    Equal,
    /// First bound was after the second bound
    After,
}

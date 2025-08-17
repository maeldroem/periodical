//! Interval overlap positioning

use std::cmp::Ordering;
use std::convert::Infallible;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HalfOpenAbsoluteInterval, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::Interval;
use crate::intervals::ops::bound_overlap_ambiguity::{
    BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet, DisambiguatedBoundOverlap,
};
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, HasEmptiableRelativeBounds, RelativeBounds, RelativeEndBound,
    RelativeFiniteBound, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{AbsoluteInterval, ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};

/// Where the current time interval was found relative to the other time interval
///
/// See [`overlap_position`](CanPositionOverlap::overlap_position) for more information
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum OverlapPosition {
    /// The current time interval was found before the given other time interval
    OutsideBefore,
    /// The current time interval was found after the given other time interval
    OutsideAfter,
    /// The current time interval was found outside the given other time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The current time interval was found ending on the beginning of the given other time interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the contained [`BoundOverlapAmbiguity`].
    /// The first contained bound is the reference, the second is the compared one.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    EndsOnStart(BoundOverlapAmbiguity),
    /// The current time interval was found starting on the end of the given other time interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the contained [`BoundOverlapAmbiguity`].
    /// The first contained bound is the reference, the second is the compared one.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    StartsOnEnd(BoundOverlapAmbiguity),
    /// The current interval is crossing the start of the compared one (starting outside, ending inside)
    CrossesStart,
    /// The current interval is crossing the end of the compared one (starting inside, ending outside)
    CrossesEnd,
    /// The current time interval was found completely inside the given other time interval
    Inside,
    /// The current time interval was found beginning on the start of the given other time interval and ending inside
    /// that time interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the contained [`BoundOverlapAmbiguity`].
    /// The first contained bound is the reference, the second is the compared one.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), hence the [`BoundOverlapAmbiguity`]
    /// wrapped in an [`Option`].
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    InsideAndSameStart(Option<BoundOverlapAmbiguity>),
    /// The current time interval was found beginning inside the given other time interval and ending at the end of
    /// that time interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the contained [`BoundOverlapAmbiguity`].
    /// The first contained bound is the reference, the second is the compared one.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), hence the [`BoundOverlapAmbiguity`]
    /// wrapped in an [`Option`].
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    InsideAndSameEnd(Option<BoundOverlapAmbiguity>),
    /// The current time interval was found beginning and ending at the same times as the given other time interval
    ///
    /// Since two pairs of bounds are overlapping, this creates an ambiguity, hence the contained [`BoundOverlapAmbiguity`].
    /// The first contained bound of each pair is the reference, the second of each pair is the compared one.
    ///
    /// Since half-open intervals only have a single defined bound, the second element is an [`Option`].
    /// Also, when you compare two open intervals, they don't have defined bounds but still are equal, so all elements
    /// are [`Option`]s in the end.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    Equal(Option<BoundOverlapAmbiguity>, Option<BoundOverlapAmbiguity>),
    /// The current time interval was found beginning on the same point as the given other time interval and ending
    /// after that time interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the contained [`BoundOverlapAmbiguity`].
    /// The first contained bound is the reference, the second is the compared one.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), the [`BoundOverlapAmbiguity`] is wrapped
    /// in an [`Option`].
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    ContainsAndSameStart(Option<BoundOverlapAmbiguity>),
    /// The current time interval was found beginning before the given other time interval and ending at the same time
    /// as that time interval
    ///
    /// Since two bounds are overlapping, this creates an ambiguity, hence the contained [`BoundOverlapAmbiguity`].
    /// The first contained bound is the reference, the second is the compared one.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), the [`BoundOverlapAmbiguity`] is wrapped
    /// in an [`Option`].
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    ContainsAndSameEnd(Option<BoundOverlapAmbiguity>),
    /// The current time interval was found beginning before the given other time interval's start
    /// and ending after that time interval's end
    Contains,
}

impl OverlapPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn strip(self) -> DisambiguatedOverlapPosition {
        match self {
            OverlapPosition::OutsideBefore => DisambiguatedOverlapPosition::OutsideBefore,
            OverlapPosition::OutsideAfter => DisambiguatedOverlapPosition::OutsideAfter,
            OverlapPosition::Outside => DisambiguatedOverlapPosition::Outside,
            OverlapPosition::EndsOnStart(..) => DisambiguatedOverlapPosition::EndsOnStart,
            OverlapPosition::StartsOnEnd(..) => DisambiguatedOverlapPosition::StartsOnEnd,
            OverlapPosition::CrossesStart => DisambiguatedOverlapPosition::CrossesStart,
            OverlapPosition::CrossesEnd => DisambiguatedOverlapPosition::CrossesEnd,
            OverlapPosition::Inside => DisambiguatedOverlapPosition::Inside,
            OverlapPosition::InsideAndSameStart(..) => DisambiguatedOverlapPosition::InsideAndSameStart,
            OverlapPosition::InsideAndSameEnd(..) => DisambiguatedOverlapPosition::InsideAndSameEnd,
            OverlapPosition::Equal(..) => DisambiguatedOverlapPosition::Equal,
            OverlapPosition::ContainsAndSameStart(..) => DisambiguatedOverlapPosition::ContainsAndSameStart,
            OverlapPosition::ContainsAndSameEnd(..) => DisambiguatedOverlapPosition::ContainsAndSameEnd,
            OverlapPosition::Contains => DisambiguatedOverlapPosition::Contains,
        }
    }

    /// Uses a rule set to transform the overlap position into a disambiguated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: OverlapRuleSet) -> DisambiguatedOverlapPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`OverlapPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum DisambiguatedOverlapPosition {
    /// See [`OverlapPosition::OutsideBefore`]
    OutsideBefore,
    /// See [`OverlapPosition::OutsideAfter`]
    OutsideAfter,
    /// See [`OverlapPosition::Outside`]
    Outside,
    /// See [`OverlapPosition::EndsOnStart`]
    EndsOnStart,
    /// See [`OverlapPosition::StartsOnEnd`]
    StartsOnEnd,
    /// See [`OverlapPosition::CrossesStart`]
    CrossesStart,
    /// See [`OverlapPosition::CrossesEnd`]
    CrossesEnd,
    /// See [`OverlapPosition::Inside`]
    Inside,
    /// See [`OverlapPosition::InsideAndSameStart`]
    InsideAndSameStart,
    /// See [`OverlapPosition::InsideAndSameEnd`]
    InsideAndSameEnd,
    /// See [`OverlapPosition::Equal`]
    Equal,
    /// See [`OverlapPosition::ContainsAndSameStart`]
    ContainsAndSameStart,
    /// See [`OverlapPosition::ContainsAndSameEnd`]
    ContainsAndSameEnd,
    /// See [`OverlapPosition::Contains`]
    Contains,
}

/// Different rule sets for determining whether different [`OverlapPosition`]s are considered as overlapping or not.
///
/// See [`Interval::overlaps_using_rule_set`] for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum OverlapRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds. Here's a table of interactions for ambiguous cases:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:                 [-------]
    /// OutsideBefore              :       (-----]
    /// OutsideAfter        [------)       :
    /// ContainsAndSameStart       [-------)
    /// ContainsAndSameEnd         (-------]
    /// Contains                   (-------)
    /// InsideAndSameStart         [----------)
    /// InsideAndSameEnd        (----------]
    ///
    /// Reference:                 (-------)
    /// OutsideBefore              :       [-----]
    /// OutsideAfter        [------]       :
    /// Inside                     [-------]
    /// InsideAndSameStart         (-------]
    /// InsideAndSameEnd           [-------)
    /// Inside                   [---------]
    /// Inside                     [----------]
    /// ```
    #[default]
    Strict,
    /// Continuous to future rule set
    ///
    /// Like the [strict rule set](OverlapRuleSet::Strict), but counts as [`StartsOnEnd`](OverlapPosition::StartsOnEnd)
    /// when the reference interval's inclusive start bound meets the compared interval's end bound, regardless of its
    /// inclusivity, and counts as [`EndsOnStart`](OverlapPosition::EndsOnStart) when the reference interval's
    /// end bound, regardless of its inclusivity, meets the compared interval's inclusive start bound.
    /// Here's a table to illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            [------)
    /// StartsOnEnd      [----)      :
    /// StartsOnEnd      [----]      :
    /// EndsOnStart           :      [-----]
    /// OutsideBefore         :      (-----]
    ///
    /// Reference:            (------]
    /// OutsideAfter     [----]      :
    /// OutsideAfter     [----)      :
    /// EndsOnStart           :      [-----]
    /// OutsideBefore         :      (-----)
    /// ```
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Like the [strict rule set](OverlapRuleSet::Strict), but counts as [`StartsOnEnd`](OverlapPosition::StartsOnEnd)
    /// when the reference interval's start bound, regardless of its inclusivity, meets the compared interval's
    /// inclusive end bound, and counts as [`EndsOnStart`](OverlapPosition::EndsOnStart) when the reference interval's
    /// inclusive end bound meets the compared interval's start bound, regardless of its inclusivity.
    /// Here's a table to illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            (------]
    /// StartsOnEnd      [----]      :
    /// OutsideAfter     [----)      :
    /// EndsOnStart           :      [-----]
    /// EndsOnStart           :      (-----)
    ///
    /// Reference:            [------)
    /// OutsideAfter     [----)      :
    /// StartsOnEnd      [----]      :
    /// OutsideBefore         :      [-----]
    /// OutsideBefore         :      (-----]
    /// ```
    ContinuousToPast,
    /// Lenient rule set
    ///
    /// Allows interactions that would count as not overlapping (or not overlapping _as much_) under the strict rule set
    /// but doesn't allow cases where two exclusive bounds of opposite source (start/end) meet. Here's a table to
    /// illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:                [------]
    /// StartsOnEnd         [-----)      :
    /// EndsOnStart               :      (-----]
    /// Equal                     (------]
    /// Equal                     [------)
    /// Equal                     (------)
    /// ContainsAndSameStart      (---]  :
    /// ContainsAndSameEnd        :  [---)
    /// InsideAndSameStart        (----------]
    /// InsideAndSameEnd      [----------)
    ///
    /// Reference:                (------)
    /// StartsOnEnd         [-----]      :
    /// EndsOnStart               :      [-----]
    /// Equal                     [------]
    /// Equal                     (------]
    /// Equal                     [------)
    /// ContainsAndSameStart      [---]  :
    /// ContainsAndSameEnd        :  [---]
    /// InsideAndSameStart        [---------]
    /// InsideAndSameEnd       [---------]
    /// ```
    Lenient,
    /// Very lenient rule set
    ///
    /// Same as the [lenient rule set](OverlapRuleSet::Lenient), but allows cases where two exclusive bounds of
    /// opposite source (start/end) meet.
    VeryLenient,
}

impl OverlapRuleSet {
    /// Disambiguates an overlap position according to the rule set
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate(&self, overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
        type Bodrs = BoundOverlapDisambiguationRuleSet;

        match self {
            Self::Strict => overlap_position_disambiguation(overlap_position, Bodrs::Strict),
            Self::ContinuousToFuture => overlap_position_disambiguation(overlap_position, Bodrs::ContinuousToFuture),
            Self::ContinuousToPast => overlap_position_disambiguation(overlap_position, Bodrs::ContinuousToPast),
            Self::Lenient => overlap_position_disambiguation(overlap_position, Bodrs::Lenient),
            Self::VeryLenient => overlap_position_disambiguation(overlap_position, Bodrs::VeryLenient),
        }
    }
}

/// Disambiguates an [`OverlapPosition`] using the given [`BoundOverlapDisambiguationRuleSet`]
#[must_use]
pub fn overlap_position_disambiguation(
    overlap_position: OverlapPosition,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Dbo = DisambiguatedBoundOverlap;

    match overlap_position {
        Op::Outside => Dop::Outside,
        Op::OutsideBefore => Dop::OutsideBefore,
        Op::OutsideAfter => Dop::OutsideAfter,
        Op::EndsOnStart(ambiguity) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::CrossesStart,
                Dbo::Equal => Dop::EndsOnStart,
                Dbo::After => Dop::OutsideBefore,
            }
        },
        Op::StartsOnEnd(ambiguity) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::OutsideAfter,
                Dbo::Equal => Dop::StartsOnEnd,
                Dbo::After => Dop::CrossesEnd,
            }
        },
        Op::CrossesStart => Dop::CrossesStart,
        Op::CrossesEnd => Dop::CrossesEnd,
        Op::Inside => Dop::Inside,
        Op::InsideAndSameStart(None) => Dop::InsideAndSameStart,
        Op::InsideAndSameStart(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::Inside,
                Dbo::Equal => Dop::InsideAndSameStart,
                Dbo::After => Dop::CrossesStart,
            }
        },
        Op::Equal(None, None) => Dop::Equal,
        Op::Equal(Some(ambiguity), None) => overlap_position_bound_ambiguity_disambiguation_equal_half_open(
            ambiguity,
            bound_overlap_disambiguation_rule_set,
        ),
        Op::Equal(None, Some(_)) => {
            unreachable!(
                "When there is a bound ambiguity for an equal position for comparing two half-open intervals, \
                which produces a single bound ambiguity, the bound ambiguity is never stored in the second element \
                of the `OverlapPosition::Equal` variant"
            );
        },
        Op::Equal(Some(start_ambiguity), Some(end_ambiguity)) => {
            overlap_position_bound_ambiguity_disambiguation_equal_closed(
                start_ambiguity,
                end_ambiguity,
                bound_overlap_disambiguation_rule_set,
            )
        },
        Op::InsideAndSameEnd(None) => Dop::InsideAndSameEnd,
        Op::InsideAndSameEnd(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::CrossesEnd,
                Dbo::Equal => Dop::InsideAndSameEnd,
                Dbo::After => Dop::Inside,
            }
        },
        Op::ContainsAndSameStart(None) => Dop::ContainsAndSameStart,
        Op::ContainsAndSameStart(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::CrossesEnd,
                Dbo::Equal => Dop::ContainsAndSameStart,
                Dbo::After => Dop::Contains,
            }
        },
        Op::ContainsAndSameEnd(None) => Dop::ContainsAndSameEnd,
        Op::ContainsAndSameEnd(Some(ambiguity)) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::Contains,
                Dbo::Equal => Dop::ContainsAndSameEnd,
                Dbo::After => Dop::CrossesStart,
            }
        },
        Op::Contains => Dop::Contains,
    }
}

/// Disambiguates a [`BoundOverlapAmbiguity`] for the [`Equal`](OverlapPosition::Equal) position
/// of two half-open intervals
#[must_use]
pub fn overlap_position_bound_ambiguity_disambiguation_equal_half_open(
    ambiguity: BoundOverlapAmbiguity,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Dbo = DisambiguatedBoundOverlap;
    type Dop = DisambiguatedOverlapPosition;

    match ambiguity {
        BoundOverlapAmbiguity::BothStarts(..) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::InsideAndSameEnd,
                Dbo::Equal => Dop::Equal,
                Dbo::After => Dop::ContainsAndSameEnd,
            }
        },
        BoundOverlapAmbiguity::BothEnds(..) => {
            match ambiguity.disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set) {
                Dbo::Before => Dop::ContainsAndSameStart,
                Dbo::Equal => Dop::Equal,
                Dbo::After => Dop::InsideAndSameStart,
            }
        },
        BoundOverlapAmbiguity::StartEnd(..) | BoundOverlapAmbiguity::EndStart(..) => {
            unreachable!(
                "When there is a bound ambiguity for an equal position for comparing two half-open intervals, \
                which produces a single bound ambiguity, the bound ambiguity is always either BothStarts or \
                BothEnds, but never StartEnd nor EndStart"
            );
        },
    }
}

/// Disambiguates two [`BoundOverlapAmbiguity`] for the [`Equal`](OverlapPosition::Equal) position
/// of two closed intervals
#[must_use]
pub fn overlap_position_bound_ambiguity_disambiguation_equal_closed(
    start_ambiguity: BoundOverlapAmbiguity,
    end_ambiguity: BoundOverlapAmbiguity,
    bound_overlap_disambiguation_rule_set: BoundOverlapDisambiguationRuleSet,
) -> DisambiguatedOverlapPosition {
    type Dbo = DisambiguatedBoundOverlap;
    type Dop = DisambiguatedOverlapPosition;

    let disambiguated_start_bound = start_ambiguity
        .disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set);
    let disambiguated_end_bound = end_ambiguity
        .disambiguate_using_rule_set(bound_overlap_disambiguation_rule_set);

    match (disambiguated_start_bound, disambiguated_end_bound) {
        (Dbo::Before, Dbo::Before) => Dop::CrossesEnd,
        (Dbo::Before, Dbo::Equal) => Dop::InsideAndSameEnd,
        (Dbo::Before, Dbo::After) => Dop::Inside,
        (Dbo::Equal, Dbo::Before) => Dop::ContainsAndSameStart,
        (Dbo::Equal, Dbo::Equal) => Dop::Equal,
        (Dbo::Equal, Dbo::After) => Dop::InsideAndSameStart,
        (Dbo::After, Dbo::Before) => Dop::Contains,
        (Dbo::After, Dbo::Equal) => Dop::ContainsAndSameEnd,
        (Dbo::After, Dbo::After) => Dop::CrossesStart,
    }
}

/// Default overlap rules
pub const DEFAULT_OVERLAP_RULES: [OverlapRule; 1] = [OverlapRule::AllowAdjacency];

/// All rules for determining what counts as overlapping
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum OverlapRule {
    /// Counts adjacent / "touching" intervals as overlapping
    AllowAdjacency,
    /// Counts interval as overlapping if it is adjacent only in the past compared to the reference interval
    AllowPastAdjacency,
    /// Counts interval as overlapping if it is adjacent only in the future compared to the reference interval
    AllowFutureAdjacency,
    /// Doesn't count adjacent / "touching" intervals as overlapping
    DenyAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent only in the past compared to the reference interval
    DenyPastAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent only in the future compared to the reference interval
    DenyFutureAdjacency,
}

impl OverlapRule {
    /// Returns the next state of the running overlap decision, given the current one and
    /// the disambiguated containment position
    #[must_use]
    pub fn counts_as_overlap(&self, running: bool, disambiguated_pos: DisambiguatedOverlapPosition) -> bool {
        match self {
            Self::AllowAdjacency => allow_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::AllowPastAdjacency => allow_past_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::AllowFutureAdjacency => {
                allow_future_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos)
            },
            Self::DenyAdjacency => deny_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::DenyPastAdjacency => deny_past_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos),
            Self::DenyFutureAdjacency => {
                deny_future_adjacency_overlap_rule_counts_as_overlap(running, disambiguated_pos)
            },
        }
    }
}

/// Checks all the given rules and returns the final boolean regarding overlap
#[must_use]
pub fn check_overlap_rules<'a, RI>(disambiguated_overlap_position: DisambiguatedOverlapPosition, rules: RI) -> bool
where
    RI: IntoIterator<Item = &'a OverlapRule>,
{
    let common = matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::CrossesStart
            | DisambiguatedOverlapPosition::CrossesEnd
            | DisambiguatedOverlapPosition::Inside
            | DisambiguatedOverlapPosition::InsideAndSameStart
            | DisambiguatedOverlapPosition::InsideAndSameEnd
            | DisambiguatedOverlapPosition::Equal
            | DisambiguatedOverlapPosition::ContainsAndSameStart
            | DisambiguatedOverlapPosition::ContainsAndSameEnd
            | DisambiguatedOverlapPosition::Contains,
    );

    rules.into_iter().fold(common, |is_overlapping, rule| {
        rule.counts_as_overlap(is_overlapping, disambiguated_overlap_position)
    })
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow adjacency' rule](OverlapRule::AllowAdjacency)
#[must_use]
pub fn allow_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running
        || matches!(
            disambiguated_pos,
            DisambiguatedOverlapPosition::EndsOnStart | DisambiguatedOverlapPosition::StartsOnEnd
        )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow past adjacency' rule](OverlapRule::AllowPastAdjacency)
#[must_use]
pub fn allow_past_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedOverlapPosition::EndsOnStart)
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow future adjacency' rule](OverlapRule::AllowFutureAdjacency)
#[must_use]
pub fn allow_future_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedOverlapPosition::StartsOnEnd)
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'deny adjacency' rule](OverlapRule::DenyAdjacency)
#[must_use]
pub fn deny_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running
        && !matches!(
            disambiguated_pos,
            DisambiguatedOverlapPosition::EndsOnStart | DisambiguatedOverlapPosition::StartsOnEnd,
        )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'deny past adjacency' rule](OverlapRule::DenyPastAdjacency)
#[must_use]
pub fn deny_past_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedOverlapPosition::EndsOnStart)
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'deny future adjacency' rule](OverlapRule::DenyFutureAdjacency)
#[must_use]
pub fn deny_future_adjacency_overlap_rule_counts_as_overlap(
    running: bool,
    disambiguated_pos: DisambiguatedOverlapPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedOverlapPosition::StartsOnEnd)
}

/// Capacity to position an overlap from a given [`HasEmptiableAbsoluteBounds`] implementor
pub trait CanPositionOverlap<Rhs = Self> {
    /// Error type if the overlap positioning failed
    type Error;

    /// Returns the overlap position of the given interval
    ///
    /// The current interval is compared to the other interval, that means that if you, for example, compare
    /// a closed absolute interval (instance) with an open interval (given interval), you will get
    /// [`OverlapPosition::Inside`] as the closed absolute interval _is contained_ by an open interval.
    ///
    /// An empty interval is always outside, even if compared against an open interval, as an empty interval is a
    /// concept-value (like infinity) rather than an actual value.
    ///
    /// # Bound inclusivity
    ///
    /// When checking the overlap position, the all bound inclusivities are considered as inclusive.
    /// Then, on cases where the result could be ambiguous (e.g. if the compared interval's start ends up on
    /// the reference interval's start but the reference's inclusivity of this bound is exclusive, or maybe both
    /// intervals' concerned bound are exclusive, does it qualify as [`OverlapPosition::EndsOnStart`]?),
    /// we simply include the inclusivity of the concerned bound and let the receiver make the call on whether
    /// it counts or not.
    ///
    /// This way, we can guarantee maximum flexibility of this process.
    ///
    /// Ambiguous overlap positions contains the reference interval concerned bound's inclusivity first,
    /// then the compared interval concerned bound's inclusivity second.
    ///
    /// The only exception to that is [`OverlapPosition::Equal`], where its first tuple is the bound inclusivities for
    /// the reference interval, and its second tuple is the bound inclusivities for the compared interval.
    ///
    /// Since half-open and open intervals are also subject to the overlap position check, most ambiguous overlap
    /// positions have one or all of their elements as [`Option`]s. Those elements are set to [`None`] only when
    /// there is no bound to speak of. The order of the elements remains the same though: first the reference, then
    /// the compared.
    ///
    /// In the case of a pair of half-open intervals being compared, since they only have one bound, the second element
    /// of each tuple will be [`None`].
    /// In the case of a pair of open intervals being compared, since they have no bounds but still are equal, all
    /// elements will be [`None`].
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error>;

    /// Returns the disambiguated overlap position of the given interval using a given rule set
    ///
    /// See [`CanPositionOverlap::overlap_position`] for more details about overlap position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionOverlap::Error).
    fn disambiguated_overlap_position(
        &self,
        rhs: &Rhs,
        rule_set: OverlapRuleSet,
    ) -> Result<DisambiguatedOverlapPosition, Self::Error> {
        self.overlap_position(rhs)
            .map(|overlap_position| rule_set.disambiguate(overlap_position))
    }

    /// Returns whether the given other interval overlaps the current one using predetermined rules
    ///
    /// Uses the [default rule set](OverlapRuleSet::default) with the default rules,
    ///
    /// Those have been chosen because they are the closest to how we mathematically and humanly interpret overlaps.
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see [`CanPositionOverlap::overlaps`].
    ///
    /// If you want even more granular control, see [`CanPositionOverlap::overlaps_using_simple`].
    #[must_use]
    fn simple_overlaps(&self, rhs: &Rhs) -> bool {
        self.overlaps(rhs, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
    }

    /// Returns whether the given other interval overlaps the current one using the given [overlap rules](`OverlapRule`)
    ///
    /// This method uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position). If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the [`OverlapRule`]s are checked. This method returns true only if all provided
    /// [`OverlapRule`]s are respected (i.e. returned true when calling [`OverlapRule::counts_as_overlap`]).
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for overlap, see [`simple_overlaps`](CanPositionOverlap::simple_overlaps).
    ///
    /// If you are looking for more control over what counts as overlap, see [`overlaps_using_simple`](CanPositionOverlap::overlaps_using_simple).
    ///
    /// If you want extremely granular control over what counts as overlap, see [`overlaps_using`](CanPositionOverlap::overlaps_using).
    #[must_use]
    fn overlaps<'a, RI>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a OverlapRule>,
    {
        self.disambiguated_overlap_position(rhs, rule_set)
            .map(|disambiguated_overlap_position| check_overlap_rules(disambiguated_overlap_position, rules))
            .unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using the given closure
    ///
    /// This method uses [`CanPositionOverlap::overlap_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`OverlapPosition`]
    /// given by [`CanPositionOverlap::overlap_position`] counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as overlapping but still want
    /// predetermined [`DisambiguatedOverlapPosition`]s, see [`CanPositionOverlap::overlaps_using_simple`].
    ///
    /// If you are looking for predetermined decisions on what's considered as overlapping, see [`CanPositionOverlap::overlaps`].
    #[must_use]
    fn overlaps_using<F>(&self, rhs: &Rhs, f: F) -> bool
    where
        F: FnOnce(OverlapPosition) -> bool,
    {
        self.overlap_position(rhs).map(f).unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using the given closure
    /// with a disambiguated position
    ///
    /// This method uses [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position). If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`DisambiguatedOverlapPosition`]
    /// given by [`disambiguated_overlap_position`](CanPositionOverlap::disambiguated_overlap_position) counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as overlapping, see [`CanPositionOverlap::overlaps_using`].
    ///
    /// If you are looking for predetermined decisions on what's considered as overlapping, see [`CanPositionOverlap::overlaps`].
    #[must_use]
    fn overlaps_using_disambiguated<F>(&self, rhs: &Rhs, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedOverlapPosition) -> bool,
    {
        self.disambiguated_overlap_position(rhs, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

// Note: the impls below could be shorten by a lot when non-overlapping trait bounds (and overlapping ones?)
// become stable

impl<Rhs> CanPositionOverlap<Rhs> for AbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptiableAbsoluteBounds
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for AbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for ClosedAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for HalfOpenAbsoluteInterval
where
    Rhs: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for RelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptiableRelativeBounds
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for RelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for ClosedRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for HalfOpenRelativeInterval
where
    Rhs: HasEmptiableRelativeBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_rel_bounds(self, rhs))
    }
}

impl CanPositionOverlap<AbsoluteBounds> for OpenInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &AbsoluteBounds) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<EmptiableAbsoluteBounds> for OpenInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &EmptiableAbsoluteBounds) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<AbsoluteInterval> for OpenInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &AbsoluteInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<ClosedAbsoluteInterval> for OpenInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &ClosedAbsoluteInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<HalfOpenAbsoluteInterval> for OpenInterval {
    type Error = Infallible;

    fn overlap_position(&self, rhs: &HalfOpenAbsoluteInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(self, rhs))
    }
}

impl CanPositionOverlap<OpenInterval> for OpenInterval {
    type Error = Infallible;

    fn overlap_position(&self, _rhs: &OpenInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(OverlapPosition::Equal(None, None))
    }
}

impl CanPositionOverlap<EmptyInterval> for OpenInterval {
    type Error = Infallible;

    fn overlap_position(&self, _rhs: &EmptyInterval) -> Result<OverlapPosition, Self::Error> {
        Ok(OverlapPosition::Outside)
    }
}

impl<Rhs> CanPositionOverlap<Rhs> for EmptyInterval
where
    Rhs: Interval,
{
    type Error = Infallible;

    fn overlap_position(&self, _rhs: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(OverlapPosition::Outside)
    }
}

/// Positions the overlap between two [`AbsoluteBounds`]
#[must_use]
pub fn overlap_position_abs_bounds(og: &AbsoluteBounds, other: &AbsoluteBounds) -> OverlapPosition {
    type Sb = AbsoluteStartBound;
    type Eb = AbsoluteEndBound;
    type Op = OverlapPosition;

    match ((og.start(), og.end()), (other.start(), other.end())) {
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => {
            Op::Equal(None, None)
        },
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(..))) => {
            Op::ContainsAndSameStart(None)
        },
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::Finite(..), Eb::InfiniteFuture)) => {
            Op::ContainsAndSameEnd(None)
        },
        ((Sb::InfinitePast, Eb::InfiniteFuture), _) => Op::Contains,
        ((Sb::InfinitePast, Eb::Finite(..)), (Sb::InfinitePast, Eb::InfiniteFuture)) => {
            Op::InsideAndSameStart(None)
        },
        ((Sb::Finite(..), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => {
            Op::InsideAndSameEnd(None)
        },
        (_, (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::Inside,
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_end.time().cmp(&other_end.time()) {
                Ordering::Less => Op::InsideAndSameStart(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())),
                    None,
                ),
                Ordering::Greater => Op::ContainsAndSameStart(None),
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_start.time().cmp(&other_start.time()) {
                Ordering::Less => Op::ContainsAndSameEnd(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())),
                    None,
                ),
                Ordering::Greater => Op::InsideAndSameEnd(None),
            }
        },
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_end.time().cmp(&other_start.time()) {
                Ordering::Less => Op::OutsideBefore,
                Ordering::Equal => Op::EndsOnStart(
                    BoundOverlapAmbiguity::EndStart(og_end.inclusivity(), other_start.inclusivity())
                ),
                Ordering::Greater => Op::CrossesStart,
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_start.time().cmp(&other_end.time()) {
                Ordering::Less => Op::CrossesStart,
                Ordering::Equal => Op::StartsOnEnd(
                    BoundOverlapAmbiguity::StartEnd(og_start.inclusivity(), other_end.inclusivity())
                ),
                Ordering::Greater => Op::OutsideAfter,
            }
        },
        ((Sb::InfinitePast, Eb::Finite(ref_bound)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_abs_half_open_past_closed(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref_bound), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_abs_half_open_future_closed(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(ref_bound))) => {
            overlap_position_abs_closed_half_open_past(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(ref_bound), Eb::InfiniteFuture)) => {
            overlap_position_abs_closed_half_open_future(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_abs_closed_pair(og_start, og_end, other_start, other_end)
        },
    }
}

/// Positions the overlap between a half-open interval going to the past and a closed interval
#[must_use]
pub fn overlap_position_abs_half_open_past_closed(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::EndsOnStart(
            BoundOverlapAmbiguity::EndStart(ref_bound.inclusivity(), other_start.inclusivity())
        ),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(ref_bound.inclusivity(), other_end.inclusivity())
        )),
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between a half-open interval going to the future and a closed interval
#[must_use]
pub fn overlap_position_abs_half_open_future_closed(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(ref_bound.inclusivity(), other_start.inclusivity())
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::StartsOnEnd(
            BoundOverlapAmbiguity::StartEnd(ref_bound.inclusivity(), other_end.inclusivity())
        ),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the past
#[must_use]
pub fn overlap_position_abs_closed_half_open_past(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::StartsOnEnd(
            BoundOverlapAmbiguity::StartEnd(og_start.inclusivity(), ref_bound.inclusivity())
        ),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), ref_bound.inclusivity())
        )),
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the future
#[must_use]
pub fn overlap_position_abs_closed_half_open_future(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), ref_bound.inclusivity())
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::EndsOnStart(
            BoundOverlapAmbiguity::EndStart(og_end.inclusivity(), ref_bound.inclusivity())
        ),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two closed intervals
#[must_use]
pub fn overlap_position_abs_closed_pair(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    let og_start_cmp = (
        og_start.time().cmp(&other_start.time()),
        og_start.time().cmp(&other_end.time()),
    );
    let og_end_cmp = (
        og_end.time().cmp(&other_start.time()),
        og_end.time().cmp(&other_end.time()),
    );

    match (og_start_cmp, og_end_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::EndsOnStart(
            BoundOverlapAmbiguity::EndStart(og_end.inclusivity(), other_start.inclusivity())
        ),
        ((_, Ordering::Equal), _) => OverlapPosition::StartsOnEnd(
            BoundOverlapAmbiguity::StartEnd(og_start.inclusivity(), other_end.inclusivity())
        ),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())
        )),
        ((Ordering::Greater, _), (_, Ordering::Equal)) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())
        )),
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())),
            Some(BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())
        )),
        ((Ordering::Less, _), (_, Ordering::Equal)) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())
        )),
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between two implementors of [`HasEmptiableAbsoluteBounds`]
#[must_use]
pub fn overlap_position_emptiable_abs_bounds<T, U>(og: &T, other: &U) -> OverlapPosition
where
    T: HasEmptiableAbsoluteBounds,
    U: HasEmptiableAbsoluteBounds,
{
    match (og.emptiable_abs_bounds(), other.emptiable_abs_bounds()) {
        (_, EmptiableAbsoluteBounds::Empty) | (EmptiableAbsoluteBounds::Empty, _) => OverlapPosition::Outside,
        (EmptiableAbsoluteBounds::Bound(ref og_bounds), EmptiableAbsoluteBounds::Bound(ref other_bounds)) => {
            overlap_position_abs_bounds(og_bounds, other_bounds)
        },
    }
}

/// Positions the overlap between two [`RelativeBounds`]
#[must_use]
pub fn overlap_position_rel_bounds(og: &RelativeBounds, other: &RelativeBounds) -> OverlapPosition {
    type Sb = RelativeStartBound;
    type Eb = RelativeEndBound;
    type Op = OverlapPosition;

    match ((og.start(), og.end()), (other.start(), other.end())) {
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => {
            Op::Equal(None, None)
        },
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(..))) => {
            Op::ContainsAndSameStart(None)
        },
        ((Sb::InfinitePast, Eb::InfiniteFuture), (Sb::Finite(..), Eb::InfiniteFuture)) => {
            Op::ContainsAndSameEnd(None)
        },
        ((Sb::InfinitePast, Eb::InfiniteFuture), _) => Op::Contains,
        ((Sb::InfinitePast, Eb::Finite(..)), (Sb::InfinitePast, Eb::InfiniteFuture)) => {
            Op::InsideAndSameStart(None)
        },
        ((Sb::Finite(..), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::InfiniteFuture)) => {
            Op::InsideAndSameEnd(None)
        },
        (_, (Sb::InfinitePast, Eb::InfiniteFuture)) => Op::Inside,
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_end.offset().cmp(&other_end.offset()) {
                Ordering::Less => Op::InsideAndSameStart(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())),
                    None,
                ),
                Ordering::Greater => Op::ContainsAndSameStart(None),
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_start.offset().cmp(&other_start.offset()) {
                Ordering::Less => Op::ContainsAndSameEnd(None),
                Ordering::Equal => Op::Equal(
                    Some(BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())),
                    None,
                ),
                Ordering::Greater => Op::InsideAndSameEnd(None),
            }
        },
        ((Sb::InfinitePast, Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::InfiniteFuture)) => {
            match og_end.offset().cmp(&other_start.offset()) {
                Ordering::Less => Op::OutsideBefore,
                Ordering::Equal => Op::EndsOnStart(
                    BoundOverlapAmbiguity::EndStart(og_end.inclusivity(), other_start.inclusivity())
                ),
                Ordering::Greater => Op::CrossesStart,
            }
        },
        ((Sb::Finite(og_start), Eb::InfiniteFuture), (Sb::InfinitePast, Eb::Finite(other_end))) => {
            match og_start.offset().cmp(&other_end.offset()) {
                Ordering::Less => Op::CrossesStart,
                Ordering::Equal => Op::StartsOnEnd(
                    BoundOverlapAmbiguity::StartEnd(og_start.inclusivity(), other_end.inclusivity())
                ),
                Ordering::Greater => Op::OutsideAfter,
            }
        },
        ((Sb::InfinitePast, Eb::Finite(ref_bound)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_rel_half_open_past_closed(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(ref_bound), Eb::InfiniteFuture), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_rel_half_open_future_closed(ref_bound, other_start, other_end)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::InfinitePast, Eb::Finite(ref_bound))) => {
            overlap_position_rel_closed_half_open_past(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(ref_bound), Eb::InfiniteFuture)) => {
            overlap_position_rel_closed_half_open_future(og_start, og_end, ref_bound)
        },
        ((Sb::Finite(og_start), Eb::Finite(og_end)), (Sb::Finite(other_start), Eb::Finite(other_end))) => {
            overlap_position_rel_closed_pair(og_start, og_end, other_start, other_end)
        },
    }
}

/// Positions the overlap between a half-open interval going to the past and a closed interval
#[must_use]
pub fn overlap_position_rel_half_open_past_closed(
    ref_bound: &RelativeFiniteBound,
    other_start: &RelativeFiniteBound,
    other_end: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&other_start.offset()),
        ref_bound.offset().cmp(&other_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::EndsOnStart(
            BoundOverlapAmbiguity::EndStart(ref_bound.inclusivity(), other_start.inclusivity())
        ),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(ref_bound.inclusivity(), other_end.inclusivity())
        )),
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between a half-open interval going to the future and a closed interval
#[must_use]
pub fn overlap_position_rel_half_open_future_closed(
    ref_bound: &RelativeFiniteBound,
    other_start: &RelativeFiniteBound,
    other_end: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&other_start.offset()),
        ref_bound.offset().cmp(&other_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(ref_bound.inclusivity(), other_start.inclusivity())
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::StartsOnEnd(
            BoundOverlapAmbiguity::StartEnd(ref_bound.inclusivity(), other_end.inclusivity())
        ),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the past
#[must_use]
pub fn overlap_position_rel_closed_half_open_past(
    og_start: &RelativeFiniteBound,
    og_end: &RelativeFiniteBound,
    ref_bound: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&og_start.offset()),
        ref_bound.offset().cmp(&og_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::StartsOnEnd(
            BoundOverlapAmbiguity::StartEnd(og_start.inclusivity(), ref_bound.inclusivity())
        ),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), ref_bound.inclusivity())
        )),
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the future
#[must_use]
pub fn overlap_position_rel_closed_half_open_future(
    og_start: &RelativeFiniteBound,
    og_end: &RelativeFiniteBound,
    ref_bound: &RelativeFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.offset().cmp(&og_start.offset()),
        ref_bound.offset().cmp(&og_end.offset()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), ref_bound.inclusivity())
        )),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::EndsOnStart(
            BoundOverlapAmbiguity::EndStart(og_end.inclusivity(), ref_bound.inclusivity())
        ),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two closed intervals
#[must_use]
pub fn overlap_position_rel_closed_pair(
    og_start: &RelativeFiniteBound,
    og_end: &RelativeFiniteBound,
    other_start: &RelativeFiniteBound,
    other_end: &RelativeFiniteBound,
) -> OverlapPosition {
    let og_start_cmp = (
        og_start.offset().cmp(&other_start.offset()),
        og_start.offset().cmp(&other_end.offset()),
    );
    let og_end_cmp = (
        og_end.offset().cmp(&other_start.offset()),
        og_end.offset().cmp(&other_end.offset()),
    );

    match (og_start_cmp, og_end_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::EndsOnStart(
            BoundOverlapAmbiguity::EndStart(og_end.inclusivity(), other_start.inclusivity())
        ),
        ((_, Ordering::Equal), _) => OverlapPosition::StartsOnEnd(
            BoundOverlapAmbiguity::StartEnd(og_start.inclusivity(), other_end.inclusivity())
        ),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => OverlapPosition::InsideAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())
        )),
        ((Ordering::Greater, _), (_, Ordering::Equal)) => OverlapPosition::InsideAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())
        )),
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())),
            Some(BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => OverlapPosition::ContainsAndSameStart(Some(
            BoundOverlapAmbiguity::BothStarts(og_start.inclusivity(), other_start.inclusivity())
        )),
        ((Ordering::Less, _), (_, Ordering::Equal)) => OverlapPosition::ContainsAndSameEnd(Some(
            BoundOverlapAmbiguity::BothEnds(og_end.inclusivity(), other_end.inclusivity())
        )),
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between two implementors of [`HasEmptiableRelativeBounds`]
#[must_use]
pub fn overlap_position_emptiable_rel_bounds<T, U>(og: &T, other: &U) -> OverlapPosition
where
    T: HasEmptiableRelativeBounds,
    U: HasEmptiableRelativeBounds,
{
    match (og.emptiable_rel_bounds(), other.emptiable_rel_bounds()) {
        (_, EmptiableRelativeBounds::Empty) | (EmptiableRelativeBounds::Empty, _) => OverlapPosition::Outside,
        (EmptiableRelativeBounds::Bound(ref og_bounds), EmptiableRelativeBounds::Bound(ref other_bounds)) => {
            overlap_position_rel_bounds(og_bounds, other_bounds)
        },
    }
}

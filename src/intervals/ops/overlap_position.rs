//! Interval overlap positioning

use std::cmp::Ordering;
use std::convert::Infallible;

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;

/// Where the current time interval was found relative to the other time interval
///
/// See [`overlap_position`](CanPositionOverlap::overlap_position) for more information
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapPosition {
    /// The current time interval was found before the given other time interval
    OutsideBefore,
    /// The current time interval was found after the given other time interval
    OutsideAfter,
    /// The current time interval was found outside the given other time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The current time interval was found ending on the beginning of the given other time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    OnStart(BoundInclusivity, BoundInclusivity),
    /// The current time interval was found starting on the end of the given other time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    OnEnd(BoundInclusivity, BoundInclusivity),
    /// The current time interval was found beginning outside the given other time interval but ending inside
    CrossesStart,
    /// The current time interval was found beginning inside the given other time interval but ending outside
    CrossesEnd,
    /// The current time interval was found completely inside the given other time interval
    Inside,
    /// The current time interval was found beginning on the start of the given other time interval and ending inside
    /// that time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    InsideAndSameStart(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning inside the given other time interval and ending at the end of
    /// that time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    InsideAndSameEnd(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning and ending at the same times as the given other time interval
    ///
    /// The contained bound inclusivities define the reference interval's start and end inclusivities (first tuple),
    /// and the compared interval's start and end inclusivities (second tuple).
    ///
    /// Since half-open intervals only have a single defined bound, the second element of each tuple is an [`Option`].
    /// Also, when you compare two open intervals, they don't have defined bounds but still are equal, so all elements
    /// are [`Option`]s in the end.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    Equal(
        (Option<BoundInclusivity>, Option<BoundInclusivity>),
        (Option<BoundInclusivity>, Option<BoundInclusivity>),
    ),
    /// The current time interval was found beginning on the same point as the given other time interval and ending
    /// after that time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    ContainsAndSameStart(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning before the given other time interval and ending at the same time
    /// as that time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`overlap_position`](CanPositionOverlap::overlap_position) for more details.
    ContainsAndSameEnd(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The current time interval was found beginning before the given other time interval's start
    /// and ending after that time interval's end
    Contains,
}

impl OverlapPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple(self) -> DisambiguatedOverlapPosition {
        match self {
            OverlapPosition::OutsideBefore => DisambiguatedOverlapPosition::OutsideBefore,
            OverlapPosition::OutsideAfter => DisambiguatedOverlapPosition::OutsideAfter,
            OverlapPosition::Outside => DisambiguatedOverlapPosition::Outside,
            OverlapPosition::OnStart(..) => DisambiguatedOverlapPosition::OnStart,
            OverlapPosition::OnEnd(..) => DisambiguatedOverlapPosition::OnEnd,
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

    /// Uses a rule set to transform the overlap position into a simple but opinionated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple_using_rule_set(self, rule_set: OverlapRuleSet) -> DisambiguatedOverlapPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`OverlapPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DisambiguatedOverlapPosition {
    /// See [`OverlapPosition::OutsideBefore`]
    OutsideBefore,
    /// See [`OverlapPosition::OutsideAfter`]
    OutsideAfter,
    /// See [`OverlapPosition::Outside`]
    Outside,
    /// See [`OverlapPosition::OnStart`]
    OnStart,
    /// See [`OverlapPosition::OnEnd`]
    OnEnd,
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
pub enum OverlapRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds. Here's a table of interactions for ambiguous cases:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:                 [-------]
    /// OutsideBefore       [------)       :
    /// OutsideAfter               :       (-----]
    /// InsideAndSameEnd           (-------]
    /// InsideAndSameStart         [-------)
    /// Inside                     (-------)
    /// CrossesStart            [----------)
    /// CrossesEnd                 (----------]
    ///
    /// Reference:                 (-------)
    /// OutsideBefore       [------]       :
    /// OutsideAfter               :       [-----]
    /// Contains                   [-------]
    /// ContainsAndSameStart       (-------]
    /// ContainsAndSameEnd         [-------)
    /// Contains                 [---------]
    /// Contains                   [----------]
    /// ```
    #[default]
    Strict,
    /// Continuous to future rule set
    ///
    /// Like the [strict rule set](OverlapRuleSet::Strict), but counts as [`OnStart`](OverlapPosition::OnStart) when
    /// the reference interval's inclusive start bound meets the compared interval's exclusive end bound, and counts as
    /// [`OnEnd`](OverlapPosition::OnEnd) when the reference interval's exclusive end bound meets the compared
    /// interval's inclusive start bound. Here's a table to illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            [------)
    /// OnStart          [----)      :
    /// OnEnd                 :      [-----]
    /// ```
    ContinuousToFuture,
    /// Continuous to past rule set
    ///
    /// Like the [strict rule set](OverlapRuleSet::Strict), but counts as [`OnStart`](OverlapPosition::OnStart) when
    /// the reference interval's exclusive start bound meets the compared interval's inclusive end bound, and counts as
    /// [`OnEnd`](OverlapPosition::OnEnd) when the reference interval's inclusive end bound meets the compared
    /// interval's exclusive start bound. Here's a table to illustrate it:
    ///
    /// ```txt
    /// [] = inclusive bounds, () = exclusive bounds
    ///
    /// Reference:            (------]
    /// OnStart          [----]      :
    /// OnEnd                 :      (-----]
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
    /// OnStart             [-----)      :
    /// OnEnd                     :      (-----]
    /// Equal                     (------]
    /// Equal                     [------)
    /// Equal                     (------)
    /// InsideAndSameStart        (---]  :
    /// InsideAndSameEnd          :  [---)
    /// ContainsAndSameStart      (----------]
    /// ContainsAndSameEnd    [----------)
    ///
    /// Reference:                (------)
    /// OnStart             [-----]      :
    /// OnEnd                     :      [-----]
    /// Equal                     [------]
    /// Equal                     (------]
    /// Equal                     [------)
    /// InsideAndSameStart        [---]  :
    /// InsideAndSameEnd          :  [---]
    /// ContainsAndSameStart      [---------]
    /// ContainsAndSameEnd     [---------]
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
        match self {
            Self::Strict => strict_overlap_rule_set_disambiguation(overlap_position),
            Self::ContinuousToFuture => continuous_to_future_overlap_rule_set_disambiguation(overlap_position),
            Self::ContinuousToPast => continuous_to_past_overlap_rule_set_disambiguation(overlap_position),
            Self::Lenient => lenient_overlap_rule_set_disambiguation(overlap_position),
            Self::VeryLenient => very_lenient_overlap_rule_set_disambiguation(overlap_position),
        }
    }
}

/// Disambiguates an [`OverlapPosition`] using [the strict rule set](OverlapRuleSet::Strict)
#[must_use]
pub fn strict_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::Outside => Dop::Outside,
        Op::OnStart(Bi::Inclusive, Bi::Inclusive) => Dop::OnStart,
        Op::OnStart(..) | Op::OutsideBefore => Dop::OutsideBefore,
        Op::OnEnd(Bi::Inclusive, Bi::Inclusive) => Dop::OnEnd,
        Op::OnEnd(..) | Op::OutsideAfter => Dop::OutsideAfter,
        Op::CrossesStart
        | Op::InsideAndSameStart(Some(Bi::Exclusive), Some(Bi::Inclusive))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Inclusive)), (Some(Bi::Inclusive), Some(Bi::Exclusive)))
        | Op::ContainsAndSameEnd(Some(Bi::Inclusive), Some(Bi::Exclusive)) => Dop::CrossesStart,
        Op::CrossesEnd
        | Op::Equal((Some(Bi::Inclusive), Some(Bi::Exclusive)), (Some(Bi::Exclusive), Some(Bi::Inclusive)))
        | Op::ContainsAndSameStart(Some(Bi::Inclusive), Some(Bi::Exclusive)) => Dop::CrossesEnd,
        Op::Inside
        | Op::InsideAndSameStart(Some(Bi::Inclusive), Some(Bi::Exclusive))
        | Op::Equal((Some(Bi::Inclusive), Some(Bi::Inclusive)), (Some(Bi::Exclusive), Some(Bi::Exclusive))) => {
            Dop::Inside
        },
        Op::InsideAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::InsideAndSameStart,
        Op::InsideAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::InsideAndSameEnd,
        Op::Equal((incl_ref_from, incl_ref_to), (incl_comp_from, incl_comp_to))
            if incl_ref_from == incl_comp_from && incl_ref_to == incl_comp_to =>
        {
            Dop::Equal
        },
        Op::Equal((Some(Bi::Inclusive), Some(Bi::Inclusive)), (Some(Bi::Inclusive), Some(Bi::Exclusive)))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Inclusive)), (Some(Bi::Exclusive), Some(Bi::Exclusive))) => {
            Dop::InsideAndSameStart
        },
        Op::Equal((Some(Bi::Inclusive), Some(Bi::Inclusive)), (Some(Bi::Exclusive), Some(Bi::Inclusive)))
        | Op::Equal((Some(Bi::Inclusive), Some(Bi::Exclusive)), (Some(Bi::Exclusive), Some(Bi::Exclusive))) => {
            Dop::InsideAndSameEnd
        },
        Op::Equal((Some(Bi::Inclusive), Some(Bi::Exclusive)), (Some(Bi::Inclusive), Some(Bi::Inclusive)))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Exclusive)), (Some(Bi::Exclusive), Some(Bi::Inclusive))) => {
            Dop::ContainsAndSameStart
        },
        Op::Equal((Some(Bi::Exclusive), Some(Bi::Inclusive)), (Some(Bi::Inclusive), Some(Bi::Inclusive)))
        | Op::Equal((Some(Bi::Exclusive), Some(Bi::Exclusive)), (Some(Bi::Inclusive), Some(Bi::Exclusive))) => {
            Dop::ContainsAndSameEnd
        },
        Op::Equal((Some(Bi::Exclusive), Some(Bi::Exclusive)), (Some(Bi::Inclusive), Some(Bi::Inclusive)))
        | Op::ContainsAndSameStart(Some(Bi::Exclusive), Some(Bi::Inclusive))
        | Op::ContainsAndSameEnd(Some(Bi::Exclusive), Some(Bi::Inclusive))
        | Op::Contains => Dop::Contains,
        Op::ContainsAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::ContainsAndSameStart,
        Op::ContainsAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => Dop::ContainsAndSameEnd,
        Op::InsideAndSameStart(None, Some(_)) | Op::InsideAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        Op::InsideAndSameEnd(None, Some(_)) | Op::InsideAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        Op::ContainsAndSameStart(None, Some(_)) | Op::ContainsAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        Op::ContainsAndSameEnd(None, Some(_)) | Op::ContainsAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        Op::InsideAndSameStart(..)
        | Op::InsideAndSameEnd(..)
        | Op::Equal(..)
        | Op::ContainsAndSameStart(..)
        | Op::ContainsAndSameEnd(..) => unreachable!("Already handled dynamically"),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the 'continuous to future' rule set](OverlapRuleSet::ContinuousToFuture)
#[must_use]
pub fn continuous_to_future_overlap_rule_set_disambiguation(
    overlap_position: OverlapPosition,
) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::OnStart(Bi::Inclusive, _) => Dop::OnStart,
        Op::OnStart(..) => Dop::OutsideBefore,
        Op::OnEnd(_, Bi::Inclusive) => Dop::OnEnd,
        Op::OnEnd(..) => Dop::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the 'continuous to past' rule set](OverlapRuleSet::ContinuousToPast)
#[must_use]
pub fn continuous_to_past_overlap_rule_set_disambiguation(
    overlap_position: OverlapPosition,
) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::OnStart(_, Bi::Inclusive) => Dop::OnStart,
        Op::OnStart(..) => Dop::OutsideBefore,
        Op::OnEnd(Bi::Inclusive, _) => Dop::OnEnd,
        Op::OnEnd(..) => Dop::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

/// Disambiguates an [`OverlapPosition`] using [the lenient rule set](OverlapRuleSet::Lenient)
#[must_use]
pub fn lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
    type Op = OverlapPosition;
    type Dop = DisambiguatedOverlapPosition;
    type Bi = BoundInclusivity;

    match overlap_position {
        Op::OutsideBefore | Op::OnStart(Bi::Exclusive, Bi::Exclusive) => Dop::OutsideBefore,
        Op::OutsideAfter | Op::OnEnd(Bi::Exclusive, Bi::Exclusive) => Dop::OutsideAfter,
        Op::Outside => Dop::Outside,
        Op::OnStart(..) => Dop::OnStart,
        Op::OnEnd(..) => Dop::OnEnd,
        Op::CrossesStart => Dop::CrossesStart,
        Op::CrossesEnd => Dop::CrossesEnd,
        Op::Inside => Dop::Inside,
        Op::InsideAndSameStart(..) => Dop::InsideAndSameStart,
        Op::InsideAndSameEnd(..) => Dop::InsideAndSameEnd,
        Op::Equal(..) => Dop::Equal,
        Op::Contains => Dop::Contains,
        Op::ContainsAndSameStart(..) => Dop::ContainsAndSameStart,
        Op::ContainsAndSameEnd(..) => Dop::ContainsAndSameEnd,
    }
}

/// Disambiguates an [`OverlapPosition`] using [the very lenient rule set](OverlapRuleSet::VeryLenient)
#[must_use]
pub fn very_lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> DisambiguatedOverlapPosition {
    overlap_position.to_simple()
}

/// Default overlap rules
pub const DEFAULT_OVERLAP_RULES: [OverlapRule; 1] = [OverlapRule::DenyAdjacency];

/// All rules for overlapping by converting a [`DisambiguatedOverlapPosition`] into a [`bool`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverlapRule {
    /// Counts adjacent / "touching" intervals as overlapping
    AllowAdjacency,
    /// Doesn't count adjacent / "touching" intervals as overlapping
    DenyAdjacency,
    /// Counts interval as overlapping if it is adjacent only in the past compared to the reference interval
    AllowPastAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent only in the past compared to the reference interval
    ///
    /// Same as [`OverlapRule::AllowFutureAdjacency`]
    DenyPastAdjacency,
    /// Counts interval as overlapping if it is adjacent only in the future compared to the reference interval
    AllowFutureAdjacency,
    /// Doesn't count interval as overlapping if it is adjacent only in the future compared to the reference interval
    ///
    /// Same as [`OverlapRule::AllowPastAdjacency`]
    DenyFutureAdjacency,
}

impl OverlapRule {
    /// Returns whether the given [`DisambiguatedOverlapPosition`] counts as overlap
    #[must_use]
    pub fn counts_as_overlap(&self, disambiguated_overlap_position: DisambiguatedOverlapPosition) -> bool {
        match self {
            Self::AllowAdjacency => allow_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position),
            Self::DenyAdjacency => deny_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position),
            Self::AllowPastAdjacency | Self::DenyFutureAdjacency => {
                allow_past_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position)
            },
            Self::AllowFutureAdjacency | Self::DenyPastAdjacency => {
                allow_future_adjacency_overlap_rules_counts_as_overlap(disambiguated_overlap_position)
            },
        }
    }
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow adjacency' rule](OverlapRule::AllowAdjacency)
#[must_use]
pub fn allow_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
    )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'deny adjacency' rule](OverlapRule::DenyAdjacency)
#[must_use]
pub fn deny_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
            | DisambiguatedOverlapPosition::OnStart
            | DisambiguatedOverlapPosition::OnEnd
    )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow past adjacency' rule](OverlapRule::AllowPastAdjacency)
#[must_use]
pub fn allow_past_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
            | DisambiguatedOverlapPosition::OnEnd
    )
}

/// Checks whether the given [`DisambiguatedOverlapPosition`] respects [the 'allow future adjacency' rule](OverlapRule::AllowFutureAdjacency)
#[must_use]
pub fn allow_future_adjacency_overlap_rules_counts_as_overlap(
    disambiguated_overlap_position: DisambiguatedOverlapPosition,
) -> bool {
    !matches!(
        disambiguated_overlap_position,
        DisambiguatedOverlapPosition::OutsideBefore
            | DisambiguatedOverlapPosition::OutsideAfter
            | DisambiguatedOverlapPosition::Outside
            | DisambiguatedOverlapPosition::OnStart
    )
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
    /// intervals' concerned bound are exclusive, does it qualify as [`OverlapPosition::OnStart`]?),
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
    fn overlap_position(&self, other: &Rhs) -> Result<OverlapPosition, Self::Error>;

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
    fn simple_overlaps(&self, other: &Rhs) -> bool {
        self.overlaps(other, OverlapRuleSet::default(), &DEFAULT_OVERLAP_RULES)
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
    fn overlaps<'a, RI>(&self, other: &Rhs, rule_set: OverlapRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a OverlapRule>,
    {
        self.disambiguated_overlap_position(other, rule_set)
            .map(|disambiguated_overlap_position| {
                rules
                    .into_iter()
                    .all(|rule| rule.counts_as_overlap(disambiguated_overlap_position))
            })
            .unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using a custom function
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
    fn overlaps_using<F>(&self, other: &Rhs, f: F) -> bool
    where
        F: FnOnce(OverlapPosition) -> bool,
    {
        self.overlap_position(other).map(f).unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using a custom function
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
    fn overlaps_using_simple<F>(&self, other: &Rhs, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedOverlapPosition) -> bool,
    {
        self.disambiguated_overlap_position(other, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

impl<T, Rhs> CanPositionOverlap<Rhs> for T
where
    Rhs: HasEmptiableAbsoluteBounds,
    T: HasEmptiableAbsoluteBounds,
{
    type Error = Infallible;

    fn overlap_position(&self, other: &Rhs) -> Result<OverlapPosition, Self::Error> {
        Ok(overlap_position_emptiable_abs_bounds(
            &self.emptiable_abs_bounds(),
            &other.emptiable_abs_bounds(),
        ))
    }
}

/// Positions the overlap between two implementors of [`HasEmptiableAbsoluteBounds`]
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

/// Positions the overlap between two [`AbsoluteBounds`]
#[must_use]
pub fn overlap_position_abs_bounds(og: &AbsoluteBounds, other: &AbsoluteBounds) -> OverlapPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;
    type OP = OverlapPosition;

    match ((og.start(), og.end()), (other.start(), other.end())) {
        ((StartB::InfinitePast, EndB::InfiniteFuture), (StartB::InfinitePast, EndB::InfiniteFuture)) => {
            OP::Equal((None, None), (None, None))
        },
        ((StartB::InfinitePast, EndB::InfiniteFuture), (StartB::InfinitePast, EndB::Finite(..))) => {
            OP::ContainsAndSameStart(None, None)
        },
        ((StartB::InfinitePast, EndB::InfiniteFuture), (StartB::Finite(..), EndB::InfiniteFuture)) => {
            OP::ContainsAndSameEnd(None, None)
        },
        ((StartB::InfinitePast, EndB::InfiniteFuture), _) => OP::Contains,
        ((StartB::InfinitePast, EndB::Finite(..)), (StartB::InfinitePast, EndB::InfiniteFuture)) => {
            OP::InsideAndSameStart(None, None)
        },
        ((StartB::Finite(..), EndB::InfiniteFuture), (StartB::InfinitePast, EndB::InfiniteFuture)) => {
            OP::InsideAndSameEnd(None, None)
        },
        (_, (StartB::InfinitePast, EndB::InfiniteFuture)) => OP::Inside,
        ((StartB::InfinitePast, EndB::Finite(og_end)), (StartB::InfinitePast, EndB::Finite(other_end))) => {
            match og_end.time().cmp(&other_end.time()) {
                Ordering::Less => OP::InsideAndSameStart(None, None),
                Ordering::Equal => OP::Equal(
                    (None, Some(og_end.inclusivity())),
                    (None, Some(other_end.inclusivity())),
                ),
                Ordering::Greater => OP::ContainsAndSameStart(None, None),
            }
        },
        ((StartB::Finite(og_start), EndB::InfiniteFuture), (StartB::Finite(other_start), EndB::InfiniteFuture)) => {
            match og_start.time().cmp(&other_start.time()) {
                Ordering::Less => OP::ContainsAndSameEnd(None, None),
                Ordering::Equal => OP::Equal(
                    (Some(og_start.inclusivity()), None),
                    (Some(other_start.inclusivity()), None),
                ),
                Ordering::Greater => OP::InsideAndSameEnd(None, None),
            }
        },
        ((StartB::InfinitePast, EndB::Finite(og_end)), (StartB::Finite(other_start), EndB::InfiniteFuture)) => {
            match og_end.time().cmp(&other_start.time()) {
                Ordering::Less => OP::OutsideBefore,
                Ordering::Equal => OP::OnStart(og_end.inclusivity(), other_start.inclusivity()),
                Ordering::Greater => OP::CrossesStart,
            }
        },
        ((StartB::Finite(og_start), EndB::InfiniteFuture), (StartB::InfinitePast, EndB::Finite(other_end))) => {
            match og_start.time().cmp(&other_end.time()) {
                Ordering::Less => OP::CrossesStart,
                Ordering::Equal => OP::OnEnd(og_start.inclusivity(), other_end.inclusivity()),
                Ordering::Greater => OP::OutsideAfter,
            }
        },
        ((StartB::InfinitePast, EndB::Finite(ref_bound)), (StartB::Finite(other_start), EndB::Finite(other_end))) => {
            overlap_position_half_open_past_closed(ref_bound, other_start, other_end)
        },
        ((StartB::Finite(ref_bound), EndB::InfiniteFuture), (StartB::Finite(other_start), EndB::Finite(other_end))) => {
            overlap_position_half_open_future_closed(ref_bound, other_start, other_end)
        },
        ((StartB::Finite(og_start), EndB::Finite(og_end)), (StartB::InfinitePast, EndB::Finite(ref_bound))) => {
            overlap_position_closed_half_open_past(og_start, og_end, ref_bound)
        },
        ((StartB::Finite(og_start), EndB::Finite(og_end)), (StartB::Finite(ref_bound), EndB::InfiniteFuture)) => {
            overlap_position_closed_half_open_future(og_start, og_end, ref_bound)
        },
        ((StartB::Finite(og_start), EndB::Finite(og_end)), (StartB::Finite(other_start), EndB::Finite(other_end))) => {
            overlap_position_closed_pair(og_start, og_end, other_start, other_end)
        },
    }
}

/// Positions the overlap between a half-open interval going to the past and a closed interval
#[must_use]
pub fn overlap_position_half_open_past_closed(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideBefore,
        (Ordering::Equal, _) => OverlapPosition::OnStart(ref_bound.inclusivity(), other_start.inclusivity()),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => {
            OverlapPosition::ContainsAndSameEnd(Some(ref_bound.inclusivity()), Some(other_end.inclusivity()))
        },
        (_, Ordering::Greater) => OverlapPosition::Contains,
    }
}

/// Positions the overlap between a half-open interval going to the future and a closed interval
#[must_use]
pub fn overlap_position_half_open_future_closed(
    ref_bound: &AbsoluteFiniteBound,
    other_start: &AbsoluteFiniteBound,
    other_end: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&other_start.time()),
        ref_bound.time().cmp(&other_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Contains,
        (Ordering::Equal, _) => {
            OverlapPosition::ContainsAndSameStart(Some(ref_bound.inclusivity()), Some(other_start.inclusivity()))
        },
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => OverlapPosition::OnEnd(ref_bound.inclusivity(), other_end.inclusivity()),
        (_, Ordering::Greater) => OverlapPosition::OutsideAfter,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the past
#[must_use]
pub fn overlap_position_closed_half_open_past(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _) => OverlapPosition::OnEnd(og_start.inclusivity(), ref_bound.inclusivity()),
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesEnd,
        (_, Ordering::Equal) => {
            OverlapPosition::InsideAndSameEnd(Some(og_end.inclusivity()), Some(ref_bound.inclusivity()))
        },
        (_, Ordering::Greater) => OverlapPosition::Inside,
    }
}

/// Positions the overlap between a closed interval and a half-open interval going to the future
#[must_use]
pub fn overlap_position_closed_half_open_future(
    og_start: &AbsoluteFiniteBound,
    og_end: &AbsoluteFiniteBound,
    ref_bound: &AbsoluteFiniteBound,
) -> OverlapPosition {
    match (
        ref_bound.time().cmp(&og_start.time()),
        ref_bound.time().cmp(&og_end.time()),
    ) {
        (Ordering::Less, _) => OverlapPosition::Inside,
        (Ordering::Equal, _) => {
            OverlapPosition::InsideAndSameStart(Some(og_start.inclusivity()), Some(ref_bound.inclusivity()))
        },
        (Ordering::Greater, Ordering::Less) => OverlapPosition::CrossesStart,
        (_, Ordering::Equal) => OverlapPosition::OnStart(og_end.inclusivity(), ref_bound.inclusivity()),
        (_, Ordering::Greater) => OverlapPosition::OutsideBefore,
    }
}

/// Positions the overlap between two closed intervals
#[must_use]
pub fn overlap_position_closed_pair(
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
        (_, (Ordering::Equal, _)) => OverlapPosition::OnStart(og_end.inclusivity(), other_start.inclusivity()),
        ((_, Ordering::Equal), _) => OverlapPosition::OnEnd(og_start.inclusivity(), other_end.inclusivity()),
        ((Ordering::Less, _), (Ordering::Greater, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, Ordering::Less), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => {
            OverlapPosition::InsideAndSameStart(Some(og_start.inclusivity()), Some(other_start.inclusivity()))
        },
        ((Ordering::Greater, _), (_, Ordering::Equal)) => {
            OverlapPosition::InsideAndSameEnd(Some(og_end.inclusivity()), Some(other_end.inclusivity()))
        },
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            (Some(og_start.inclusivity()), Some(og_end.inclusivity())),
            (Some(other_start.inclusivity()), Some(other_end.inclusivity())),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => {
            OverlapPosition::ContainsAndSameStart(Some(og_start.inclusivity()), Some(other_start.inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Equal)) => {
            OverlapPosition::ContainsAndSameEnd(Some(og_end.inclusivity()), Some(other_end.inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    }
}

//! Interval comparisons
//!
//! Comparisons with intervals are implemented here. You will find methods like
//!
//! - `contains`
//! - `overlaps`
//!
//! You will also find things that touch to precision of interval bounds as well as rule sets to decide what counts
//! as overlapping and what doesn't.

use std::cmp::Ordering;

use chrono::{DateTime, Duration, Utc};

use crate::intervals::Interval;
use crate::intervals::interval::{ClosedAbsoluteInterval, HalfOpenAbsoluteInterval};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};

/// Time precision used for comparisons
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Precision {
    /// Rounds the compared times to the given duration (e.g. if the duration is 1 second, the times will be rounded to the nearest second)
    ToNearest(Duration),
    /// Floors the compared times to the given duration (e.g. if the duration is 5 minutes, the times will be floored to the 5-minutes part they are in)
    ToPast(Duration),
    /// Ceils the compared times to the given duration
    ToFuture(Duration),
}

/// Where the given time was found relative to a time interval
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContainmentPosition {
    /// The given time was found before the time interval's beginning
    OutsideBefore,
    /// The given time was found after the time interval's end
    OutsideAfter,
    /// The given time was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given time was found exactly on the start of the time interval
    ///
    /// The contained bound inclusivity indicates the bound inclusivity of the start bound.
    ///
    /// See [`Interval::containment_position`] for more details.
    OnStart(BoundInclusivity),
    /// The given time was found exactly on the end of the time interval
    ///
    /// The contained bound inclusivity indicates the bound inclusivity of the end bound.
    ///
    /// See [`Interval::containment_position`] for more details.
    OnEnd(BoundInclusivity),
    /// The given time was found within the time interval
    Inside,
}

impl ContainmentPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple(self) -> SimpleContainmentPosition {
        match self {
            Self::OutsideBefore => SimpleContainmentPosition::OutsideBefore,
            Self::OutsideAfter => SimpleContainmentPosition::OutsideAfter,
            Self::Outside => SimpleContainmentPosition::Outside,
            Self::OnStart(_) => SimpleContainmentPosition::OnStart,
            Self::OnEnd(_) => SimpleContainmentPosition::OnEnd,
            Self::Inside => SimpleContainmentPosition::Inside,
        }
    }

    /// Uses a rule set to transform the containment position into a simple but opinionated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple_using_rule_set(self, rule_set: ContainmentRuleSet) -> SimpleContainmentPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`ContainmentPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SimpleContainmentPosition {
    /// See [`ContainmentPosition::OutsideBefore`]
    OutsideBefore,
    /// See [`ContainmentPosition::OutsideAfter`]
    OutsideAfter,
    /// See [`ContainmentPosition::Outside`]
    Outside,
    /// See [`ContainmentPosition::OnStart`]
    OnStart,
    /// See [`ContainmentPosition::OnEnd`]
    OnEnd,
    /// See [`ContainmentPosition::Inside`]
    Inside,
}

/// Errors that can happen when computing the containment position of some time inside an interval
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContainmentPositionError {
    /// The interval is relative, therefore we can't determine the containment position of the given time
    RelativeInterval,
    /// The interval was malformed, therefore we can't determine the containment position of the given time safely
    MalformedInterval,
}

/// Different rule sets for determining whether different [`ContainmentPosition`]s are considered as containing or not.
///
/// See [`Interval::contains_using_rule_set`] for more.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContainmentRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds, so the time needs to fall on an inclusive bound in order to be counted
    /// as contained.
    Strict,
    /// Lenient rule set
    ///
    /// If the time falls on an exclusive bound, it is still counted as contained.
    Lenient,
}

impl ContainmentRuleSet {
    /// Disambiguates a containment position according to the rule set
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate(&self, containment_position: ContainmentPosition) -> SimpleContainmentPosition {
        match self {
            Self::Strict => strict_containment_rule_set_disambiguation(containment_position),
            Self::Lenient => lenient_containment_rule_set_disambiguation(containment_position),
        }
    }
}

fn strict_containment_rule_set_disambiguation(containment_position: ContainmentPosition) -> SimpleContainmentPosition {
    match containment_position {
        ContainmentPosition::OutsideBefore | ContainmentPosition::OnStart(BoundInclusivity::Exclusive) => {
            SimpleContainmentPosition::OutsideBefore
        },
        ContainmentPosition::OutsideAfter | ContainmentPosition::OnEnd(BoundInclusivity::Exclusive) => {
            SimpleContainmentPosition::OutsideAfter
        },
        ContainmentPosition::Outside => SimpleContainmentPosition::Outside,
        ContainmentPosition::OnStart(BoundInclusivity::Inclusive) => SimpleContainmentPosition::OnStart,
        ContainmentPosition::OnEnd(BoundInclusivity::Inclusive) => SimpleContainmentPosition::OnEnd,
        ContainmentPosition::Inside => SimpleContainmentPosition::Inside,
    }
}

fn lenient_containment_rule_set_disambiguation(containment_position: ContainmentPosition) -> SimpleContainmentPosition {
    match containment_position {
        ContainmentPosition::OutsideBefore => SimpleContainmentPosition::OutsideBefore,
        ContainmentPosition::OutsideAfter => SimpleContainmentPosition::OutsideAfter,
        ContainmentPosition::Outside => SimpleContainmentPosition::Outside,
        ContainmentPosition::OnStart(_) => SimpleContainmentPosition::OnStart,
        ContainmentPosition::OnEnd(_) => SimpleContainmentPosition::OnEnd,
        ContainmentPosition::Inside => SimpleContainmentPosition::Inside,
    }
}

/// Where the other time interval was found relative to the current time interval
///
/// See [`Interval::overlap_position`] for more information
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapPosition {
    /// The given other time interval was found before the time interval
    OutsideBefore,
    /// The given other time interval was found after the time interval
    OutsideAfter,
    /// The given other time interval was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given other time interval was found ending on the beginning of the time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// See [`Interval::overlap_position`] for more details.
    OnStart(BoundInclusivity, BoundInclusivity),
    /// The given other time interval was found starting on the end of the time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// See [`Interval::overlap_position`] for more details.
    OnEnd(BoundInclusivity, BoundInclusivity),
    /// The given other time interval was found beginning outside the time interval but ending inside
    CrossesStart,
    /// The given other time interval was found beginning inside the time interval but ending outside
    CrossesEnd,
    /// The given other time interval was found completely inside the time interval
    Inside,
    /// The given other time interval was found beginning on the start of the time interval and ending inside
    /// the time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`Interval::overlap_position`] for more details.
    InsideAndSameStart(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The given other time interval was found beginning inside the time interval and ending at the end of
    /// the time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// Since when comparing an open interval with a half-open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`Interval::overlap_position`] for more details.
    InsideAndSameEnd(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The given other time interval was found beginning and ending at the same times as the time interval
    ///
    /// The contained bound inclusivities define the reference interval's start and end inclusivities (first tuple),
    /// and the compared interval's start and end inclusivities (second tuple).
    ///
    /// Since half-open intervals only have a single defined bound, the second element of each tuple is an [`Option`].
    /// Also, when you compare two open intervals, they don't have defined bounds but still are equal, so all elements
    /// are [`Option`]s in the end.
    ///
    /// See [`Interval::overlap_position`] for more details.
    Equal(
        (Option<BoundInclusivity>, Option<BoundInclusivity>),
        (Option<BoundInclusivity>, Option<BoundInclusivity>),
    ),
    /// The given other time interval was found beginning on the same point as the time interval and ending after
    /// the time interval
    ///
    /// The contained bound inclusivities define the reference interval's start inclusivity and the compared interval's
    /// start inclusivity.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`Interval::overlap_position`] for more details.
    ContainsAndSameStart(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The given other time interval was found beginning before the time interval and ending at the same time as
    /// the time interval
    ///
    /// The contained bound inclusivities define the reference interval's end inclusivity and the compared interval's
    /// end inclusivity.
    ///
    /// Since when comparing an half-open interval with an open one can result in such an overlap position but no
    /// defined bound is involved (i.e. the bound is infinity), both the reference and compared inclusivity are
    /// [`Option`]s.
    ///
    /// See [`Interval::overlap_position`] for more details.
    ContainsAndSameEnd(Option<BoundInclusivity>, Option<BoundInclusivity>),
    /// The given other time interval was found beginning before the time interval's start and ending after the time interval's end
    Contains,
}

impl OverlapPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple(self) -> SimpleOverlapPosition {
        match self {
            OverlapPosition::OutsideBefore => SimpleOverlapPosition::OutsideBefore,
            OverlapPosition::OutsideAfter => SimpleOverlapPosition::OutsideAfter,
            OverlapPosition::Outside => SimpleOverlapPosition::Outside,
            OverlapPosition::OnStart(..) => SimpleOverlapPosition::OnStart,
            OverlapPosition::OnEnd(..) => SimpleOverlapPosition::OnEnd,
            OverlapPosition::CrossesStart => SimpleOverlapPosition::CrossesStart,
            OverlapPosition::CrossesEnd => SimpleOverlapPosition::CrossesEnd,
            OverlapPosition::Inside => SimpleOverlapPosition::Inside,
            OverlapPosition::InsideAndSameStart(..) => SimpleOverlapPosition::InsideAndSameStart,
            OverlapPosition::InsideAndSameEnd(..) => SimpleOverlapPosition::InsideAndSameEnd,
            OverlapPosition::Equal(..) => SimpleOverlapPosition::Equal,
            OverlapPosition::ContainsAndSameStart(..) => SimpleOverlapPosition::ContainsAndSameStart,
            OverlapPosition::ContainsAndSameEnd(..) => SimpleOverlapPosition::ContainsAndSameEnd,
            OverlapPosition::Contains => SimpleOverlapPosition::Contains,
        }
    }

    /// Uses a rule set to transform the overlap position into a simple but opinionated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn to_simple_using_rule_set(self, rule_set: OverlapRuleSet) -> SimpleOverlapPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`OverlapPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SimpleOverlapPosition {
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

/// Errors that can happen when computing the overlap position of two intervals
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapPositionError {
    /// One interval was relative, therefore we can't determine the overlap position of the given time
    RelativeInterval,
    /// One interval was malformed, therefore we can't determine the overlap position of the given time safely
    MalformedInterval,
}

/// Different rule sets for determining whether different [`OverlapPosition`]s are considered as overlapping or not.
///
/// See [`Interval::overlaps_using_rule_set`] for more.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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
    pub fn disambiguate(&self, overlap_position: OverlapPosition) -> SimpleOverlapPosition {
        match self {
            Self::Strict => strict_overlap_rule_set_disambiguation(overlap_position),
            Self::ContinuousToFuture => continuous_to_future_overlap_rule_set_disambiguation(overlap_position),
            Self::ContinuousToPast => continuous_to_past_overlap_rule_set_disambiguation(overlap_position),
            Self::Lenient => lenient_overlap_rule_set_disambiguation(overlap_position),
            Self::VeryLenient => very_lenient_overlap_rule_set_disambiguation(overlap_position),
        }
    }
}

fn strict_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::Outside => SimpleOP::Outside,
        OP::OnStart(BI::Inclusive, BI::Inclusive) => SimpleOP::OnStart,
        OP::OnStart(..) | OP::OutsideBefore => SimpleOP::OutsideBefore,
        OP::OnEnd(BI::Inclusive, BI::Inclusive) => SimpleOP::OnEnd,
        OP::OnEnd(..) | OP::OutsideAfter => SimpleOP::OutsideAfter,
        OP::CrossesStart
        | OP::InsideAndSameStart(Some(BI::Exclusive), Some(BI::Inclusive))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Inclusive)), (Some(BI::Inclusive), Some(BI::Exclusive)))
        | OP::ContainsAndSameEnd(Some(BI::Inclusive), Some(BI::Exclusive)) => SimpleOP::CrossesStart,
        OP::CrossesEnd
        | OP::Equal((Some(BI::Inclusive), Some(BI::Exclusive)), (Some(BI::Exclusive), Some(BI::Inclusive)))
        | OP::ContainsAndSameStart(Some(BI::Inclusive), Some(BI::Exclusive)) => SimpleOP::CrossesEnd,
        OP::Inside
        | OP::InsideAndSameStart(Some(BI::Inclusive), Some(BI::Exclusive))
        | OP::Equal((Some(BI::Inclusive), Some(BI::Inclusive)), (Some(BI::Exclusive), Some(BI::Exclusive))) => {
            SimpleOP::Inside
        },
        OP::InsideAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::InsideAndSameStart,
        OP::InsideAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::InsideAndSameEnd,
        OP::Equal((incl_ref_from, incl_ref_to), (incl_comp_from, incl_comp_to))
            if incl_ref_from == incl_comp_from && incl_ref_to == incl_comp_to =>
        {
            SimpleOP::Equal
        },
        OP::Equal((Some(BI::Inclusive), Some(BI::Inclusive)), (Some(BI::Inclusive), Some(BI::Exclusive)))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Inclusive)), (Some(BI::Exclusive), Some(BI::Exclusive))) => {
            SimpleOP::InsideAndSameStart
        },
        OP::Equal((Some(BI::Inclusive), Some(BI::Inclusive)), (Some(BI::Exclusive), Some(BI::Inclusive)))
        | OP::Equal((Some(BI::Inclusive), Some(BI::Exclusive)), (Some(BI::Exclusive), Some(BI::Exclusive))) => {
            SimpleOP::InsideAndSameEnd
        },
        OP::Equal((Some(BI::Inclusive), Some(BI::Exclusive)), (Some(BI::Inclusive), Some(BI::Inclusive)))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Exclusive)), (Some(BI::Exclusive), Some(BI::Inclusive))) => {
            SimpleOP::ContainsAndSameStart
        },
        OP::Equal((Some(BI::Exclusive), Some(BI::Inclusive)), (Some(BI::Inclusive), Some(BI::Inclusive)))
        | OP::Equal((Some(BI::Exclusive), Some(BI::Exclusive)), (Some(BI::Inclusive), Some(BI::Exclusive))) => {
            SimpleOP::ContainsAndSameEnd
        },
        OP::Equal((Some(BI::Exclusive), Some(BI::Exclusive)), (Some(BI::Inclusive), Some(BI::Inclusive)))
        | OP::ContainsAndSameStart(Some(BI::Exclusive), Some(BI::Inclusive))
        | OP::ContainsAndSameEnd(Some(BI::Exclusive), Some(BI::Inclusive))
        | OP::Contains => SimpleOP::Contains,
        OP::ContainsAndSameStart(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::ContainsAndSameStart,
        OP::ContainsAndSameEnd(incl_ref, incl_comp) if incl_ref == incl_comp => SimpleOP::ContainsAndSameEnd,
        OP::InsideAndSameStart(None, Some(_)) | OP::InsideAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        OP::InsideAndSameEnd(None, Some(_)) | OP::InsideAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::InsideAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        OP::ContainsAndSameStart(None, Some(_)) | OP::ContainsAndSameStart(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameStart can't be created from a defined bound and an infinite bound"
            )
        },
        OP::ContainsAndSameEnd(None, Some(_)) | OP::ContainsAndSameEnd(Some(_), None) => {
            unreachable!(
                "OverlapPosition::ContainsAndSameEnd can't be created from a defined bound and an infinite bound"
            )
        },
        OP::InsideAndSameStart(..)
        | OP::InsideAndSameEnd(..)
        | OP::Equal(..)
        | OP::ContainsAndSameStart(..)
        | OP::ContainsAndSameEnd(..) => unreachable!("Already handled dynamically"),
    }
}

fn continuous_to_future_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::OnStart(BI::Inclusive, _) => SimpleOP::OnStart,
        OP::OnStart(..) => SimpleOP::OutsideBefore,
        OP::OnEnd(_, BI::Inclusive) => SimpleOP::OnEnd,
        OP::OnEnd(..) => SimpleOP::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

fn continuous_to_past_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::OnStart(_, BI::Inclusive) => SimpleOP::OnStart,
        OP::OnStart(..) => SimpleOP::OutsideBefore,
        OP::OnEnd(BI::Inclusive, _) => SimpleOP::OnEnd,
        OP::OnEnd(..) => SimpleOP::OutsideAfter,
        _ => strict_overlap_rule_set_disambiguation(overlap_position),
    }
}

fn lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    type OP = OverlapPosition;
    type SimpleOP = SimpleOverlapPosition;
    type BI = BoundInclusivity;

    match overlap_position {
        OP::OutsideBefore | OP::OnStart(BI::Exclusive, BI::Exclusive) => SimpleOP::OutsideBefore,
        OP::OutsideAfter | OP::OnEnd(BI::Exclusive, BI::Exclusive) => SimpleOP::OutsideAfter,
        OP::Outside => SimpleOP::Outside,
        OP::OnStart(..) => SimpleOP::OnStart,
        OP::OnEnd(..) => SimpleOP::OnEnd,
        OP::CrossesStart => SimpleOP::CrossesStart,
        OP::CrossesEnd => SimpleOP::CrossesEnd,
        OP::Inside => SimpleOP::Inside,
        OP::InsideAndSameStart(..) => SimpleOP::InsideAndSameStart,
        OP::InsideAndSameEnd(..) => SimpleOP::InsideAndSameEnd,
        OP::Equal(..) => SimpleOP::Equal,
        OP::Contains => SimpleOP::Contains,
        OP::ContainsAndSameStart(..) => SimpleOP::ContainsAndSameStart,
        OP::ContainsAndSameEnd(..) => SimpleOP::ContainsAndSameEnd,
    }
}

fn very_lenient_overlap_rule_set_disambiguation(overlap_position: OverlapPosition) -> SimpleOverlapPosition {
    overlap_position.to_simple()
}

/// All rules for overlapping by converting a [`SimpleOverlapPosition`] into a [`bool`]
///
/// All variants take an [`OverlapRuleSet`], but also describe or contain more information about how to determine
/// what counts as overlapping and what doesn't.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OverlapRule {
    /// Counts adjacent / "touching" intervals as overlapping
    AllowAdjacency,
    /// Doesn't count adjacent / "touching" intervals as overlapping
    DenyAdjacency,
}

impl OverlapRule {
    /// Returns whether the given [`SimpleOverlapPosition`] counts as overlap
    #[must_use]
    pub fn counts_as_overlap(&self, simple_overlap_position: SimpleOverlapPosition) -> bool {
        match self {
            Self::AllowAdjacency => allow_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position),
            Self::DenyAdjacency => deny_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position),
        }
    }
}

fn allow_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore | SimpleOverlapPosition::OutsideAfter | SimpleOverlapPosition::Outside
    )
}

fn deny_adjacency_overlap_rules_counts_as_overlap(simple_overlap_position: SimpleOverlapPosition) -> bool {
    !matches!(
        simple_overlap_position,
        SimpleOverlapPosition::OutsideBefore
            | SimpleOverlapPosition::OutsideAfter
            | SimpleOverlapPosition::Outside
            | SimpleOverlapPosition::OnStart
            | SimpleOverlapPosition::OnEnd
    )
}

impl Interval {
    /// Returns the containment position of the given time
    ///
    /// # Bound inclusivity
    ///
    /// When checking the containment position, the reference interval's bound inclusivities are considered
    /// as inclusive. Then, on cases where the result could be ambiguous (e.g. if the time ends up on the reference
    /// interval's start but the inclusivity of this bound is exclusive, does it qualify
    /// as [`ContainmentPosition::OnStart`]?), we simply include the inclusivity of the concerned bound and let the
    /// receiver make the call on whether it counts or not.
    ///
    /// This way, we can guarantee maximum flexibility of this process.
    ///
    /// # Errors
    ///
    /// - Returns [`RelativeInterval`](ContainmentPositionError::RelativeInterval) if the interval the operation
    ///   is done on is relative
    /// - Returns [`MalformedInterval`](ContainmentPositionError::MalformedInterval) if the interval is malformed
    ///   (see [`ClosedAbsoluteInterval::is_malformed`](crate::intervals::interval::ClosedAbsoluteInterval::is_malformed))
    pub fn containment_position(&self, time: DateTime<Utc>) -> Result<ContainmentPosition, ContainmentPositionError> {
        match self {
            Self::ClosedRelative(_) | Self::HalfOpenRelative(_) => Err(ContainmentPositionError::RelativeInterval),
            Self::ClosedAbsolute(interval) => containment_position_closed(interval, time),
            Self::HalfOpenAbsolute(interval) => Ok(containment_position_half_open(interval, time)),
            Self::Empty(_) => Ok(ContainmentPosition::Outside),
            Self::Open(_) => Ok(ContainmentPosition::Inside),
        }
    }

    /// Returns the simple containment position of the given time using a given [containment rule set](ContainmentRuleSet)
    ///
    /// See [`Interval::containment_position`] for more details about containment position.
    ///
    /// # Errors
    ///
    /// - Returns [`RelativeInterval`](ContainmentPositionError::RelativeInterval) if the interval the operation
    ///   is done on is relative
    /// - Returns [`MalformedInterval`](ContainmentPositionError::MalformedInterval) if the interval is malformed
    ///   (see [`ClosedAbsoluteInterval::is_malformed`](crate::intervals::interval::ClosedAbsoluteInterval::is_malformed))
    pub fn simple_containment_position(
        &self,
        time: DateTime<Utc>,
        rule_set: ContainmentRuleSet,
    ) -> Result<SimpleContainmentPosition, ContainmentPositionError> {
        self.containment_position(time)
            .map(|containment_position| rule_set.disambiguate(containment_position))
    }

    /// Returns whether a certain time is contained in the interval
    ///
    /// This method uses [`Interval::containment_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`ContainmentPosition`]
    /// given by [`Interval::containment_position`] counts as the passed time being contained in the interval.
    ///
    /// If instead you want predetermined decisions on whether some positions count as contained or not,
    /// check out [`Interval::contains_using_rule_set`].
    #[must_use]
    pub fn contains<F>(&self, time: DateTime<Utc>, f: F) -> bool
    where
        F: FnOnce(ContainmentPosition) -> bool,
    {
        self.containment_position(time).map(f).unwrap_or(false)
    }

    /// TODO
    #[must_use]
    pub fn contains_using_rule_set(&self, time: DateTime<Utc>, rule_set: ContainmentRuleSet) -> bool {
        todo!();
    }

    /// Returns the overlap position of the given interval
    ///
    /// The other interval is compared to the current interval, that means that if you, for example, compare
    /// a closed absolute interval (instance) with an open interval (given interval), you will get
    /// [`OverlapPosition::Contains`] as the open interval _contains_ any closed absolute interval.
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
    /// - Returns [`OverlapPositionError::RelativeInterval`] if the current or given interval is relative.
    /// - Returns [`OverlapPositionError::MalformedInterval`] if the current or given interval is malformed in any way
    ///   (see [`ClosedAbsoluteInterval::is_malformed`](crate::intervals::interval::ClosedAbsoluteInterval::is_malformed))
    pub fn overlap_position(&self, other: &Self) -> Result<OverlapPosition, OverlapPositionError> {
        match (self, other) {
            (Self::ClosedRelative(_) | Self::HalfOpenRelative(_), _)
            | (_, Self::ClosedRelative(_) | Self::HalfOpenRelative(_)) => Err(OverlapPositionError::RelativeInterval),
            (Self::ClosedAbsolute(interval), Self::ClosedAbsolute(other_interval)) => {
                overlap_position_closed_pair(interval, other_interval)
            },
            (Self::ClosedAbsolute(interval), Self::HalfOpenAbsolute(other_interval)) => {
                overlap_position_closed_half_open(interval, other_interval)
            },
            (Self::HalfOpenAbsolute(interval), Self::ClosedAbsolute(other_interval)) => {
                overlap_position_half_open_closed(interval, other_interval)
            },
            (Self::HalfOpenAbsolute(interval), Self::HalfOpenAbsolute(other_interval)) => {
                Ok(overlap_position_half_open_pair(interval, other_interval))
            },
            // empty intervals are not comparable through time as they don't have a specific time frame
            (Self::Empty(_), _) | (_, Self::Empty(_)) => Ok(OverlapPosition::Outside),
            (Self::Open(_), Self::Open(_)) => Ok(OverlapPosition::Equal((None, None), (None, None))),
            (Self::Open(_), Self::HalfOpenAbsolute(half_open_interval)) => {
                match half_open_interval.opening_direction() {
                    OpeningDirection::ToPast => Ok(OverlapPosition::InsideAndSameStart(None, None)),
                    OpeningDirection::ToFuture => Ok(OverlapPosition::InsideAndSameEnd(None, None)),
                }
            },
            (Self::Open(_), Self::ClosedAbsolute(_)) => Ok(OverlapPosition::Inside),
            (Self::HalfOpenAbsolute(half_open_interval), Self::Open(_)) => {
                match half_open_interval.opening_direction() {
                    OpeningDirection::ToPast => Ok(OverlapPosition::ContainsAndSameStart(None, None)),
                    OpeningDirection::ToFuture => Ok(OverlapPosition::ContainsAndSameEnd(None, None)),
                }
            },
            (Self::ClosedAbsolute(_), Self::Open(_)) => Ok(OverlapPosition::Contains),
        }
    }

    /// Returns the simple overlap position of the given interval using a given rule set
    ///
    /// See [`Interval::overlap_position`] for more details about overlap position.
    ///
    /// # Errors
    ///
    /// - Returns [`OverlapPositionError::RelativeInterval`] if the current or given interval is relative.
    /// - Returns [`OverlapPositionError::MalformedInterval`] if the current or given interval is malformed in any way
    ///   (see [`ClosedAbsoluteInterval::is_malformed`](crate::intervals::interval::ClosedAbsoluteInterval::is_malformed))
    pub fn simple_overlap_position(
        &self,
        other: &Self,
        rule_set: OverlapRuleSet,
    ) -> Result<SimpleOverlapPosition, OverlapPositionError> {
        self.overlap_position(other)
            .map(|overlap_position| rule_set.disambiguate(overlap_position))
    }

    /// Returns whether the given other interval overlaps the current one using predetermined rules
    ///
    /// Uses the [`Strict` rule set](OverlapRuleSet::Strict) with the following additional rules:
    ///
    /// - [`DenyAdjacency`](OverlapRule::DenyAdjacency)
    ///
    /// Those have been chosen because they are the closest to how we mathematically and humanly interpret overlaps.
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see [`Interval::overlaps`].
    ///
    /// If you want even more granular control, see [`Interval::overlaps_using_simple`].
    #[must_use]
    pub fn simple_overlaps(&self, other: &Self) -> bool {
        self.overlaps(other, OverlapRuleSet::Strict, [OverlapRule::DenyAdjacency])
    }

    /// Returns whether the given other interval overlaps the current one using the given [overlap rules](`OverlapRule`)
    ///
    /// This method uses [`Interval::simple_overlap_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the [`OverlapRule`]s are checked. This method returns true only if all provided
    /// [`OverlapRule`]s are respected (i.e. returned true when calling [`OverlapRule::counts_as_overlap`]).
    ///
    /// # See also
    ///
    /// If you are looking for the most simple way of checking for overlap, see [`Interval::simple_overlaps`].
    ///
    /// If you are looking for more control over what counts as overlap, see [`Interval::overlaps_using_simple`].
    ///
    /// If you want extremely granular control over what counts as overlap, see [`Interval::overlaps_using`].
    #[must_use]
    pub fn overlaps(
        &self,
        other: &Self,
        rule_set: OverlapRuleSet,
        rules: impl IntoIterator<Item = OverlapRule>,
    ) -> bool {
        self.simple_overlap_position(other, rule_set)
            .map(|simple_overlap_position| {
                rules
                    .into_iter()
                    .all(|rule| rule.counts_as_overlap(simple_overlap_position))
            })
            .unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using a custom function
    ///
    /// This method uses [`Interval::overlap_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`OverlapPosition`]
    /// given by [`Interval::overlap_position`] counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as overlapping but still want
    /// predetermined [`SimpleOverlapPosition`]s, see [`Interval::overlaps_using_simple`].
    ///
    /// If you are looking for predetermined decisions on what's considered as overlapping, see [`Interval::overlaps`].
    #[must_use]
    pub fn overlaps_using<F>(&self, other: &Self, f: F) -> bool
    where
        F: FnOnce(OverlapPosition) -> bool,
    {
        self.overlap_position(other).map(f).unwrap_or(false)
    }

    /// Returns whether the given other interval overlaps the current interval using a custom function
    ///
    /// This method uses [`Interval::simple_overlap_position`]. If this aforementioned method returns an [`Err`],
    /// then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`SimpleOverlapPosition`]
    /// given by [`Interval::simple_overlap_position`] counts as overlapping or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as overlapping, see [`Interval::overlaps_using`].
    ///
    /// If you are looking for predetermined decisions on what's considered as overlapping, see [`Interval::overlaps`].
    #[must_use]
    pub fn overlaps_using_simple<F>(&self, other: &Self, rule_set: OverlapRuleSet, f: F) -> bool
    where
        F: FnOnce(SimpleOverlapPosition) -> bool,
    {
        self.simple_overlap_position(other, rule_set).map(f).unwrap_or(false)
    }
}

fn containment_position_closed(
    interval: &ClosedAbsoluteInterval,
    time: DateTime<Utc>,
) -> Result<ContainmentPosition, ContainmentPositionError> {
    if interval.is_malformed() {
        return Err(ContainmentPositionError::MalformedInterval);
    }

    let containment_position = match (time.cmp(interval.from()), time.cmp(interval.to())) {
        (Ordering::Less, _) => ContainmentPosition::OutsideBefore,
        (_, Ordering::Greater) => ContainmentPosition::OutsideAfter,
        (Ordering::Equal, _) => ContainmentPosition::OnStart(interval.from_inclusivity()),
        (_, Ordering::Equal) => ContainmentPosition::OnEnd(interval.to_inclusivity()),
        (Ordering::Greater, Ordering::Less) => ContainmentPosition::Inside,
    };

    Ok(containment_position)
}

fn containment_position_half_open(interval: &HalfOpenAbsoluteInterval, time: DateTime<Utc>) -> ContainmentPosition {
    match (time.cmp(interval.reference_time()), interval.opening_direction()) {
        (Ordering::Less, OpeningDirection::ToPast) | (Ordering::Greater, OpeningDirection::ToFuture) => {
            ContainmentPosition::Inside
        },
        (Ordering::Equal, OpeningDirection::ToPast) => {
            ContainmentPosition::OnEnd(interval.reference_time_inclusivity())
        },
        (Ordering::Greater, OpeningDirection::ToPast) => ContainmentPosition::OutsideAfter,
        (Ordering::Less, OpeningDirection::ToFuture) => ContainmentPosition::OutsideBefore,
        (Ordering::Equal, OpeningDirection::ToFuture) => {
            ContainmentPosition::OnStart(interval.reference_time_inclusivity())
        },
    }
}

fn overlap_position_closed_pair(
    a: &ClosedAbsoluteInterval,
    b: &ClosedAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if a.is_malformed() || b.is_malformed() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let b_from_cmp = (b.from().cmp(a.from()), b.from().cmp(a.to()));
    let b_to_cmp = (b.to().cmp(a.from()), b.to().cmp(a.to()));

    let overlap_position = match (b_from_cmp, b_to_cmp) {
        (_, (Ordering::Less, _)) => OverlapPosition::OutsideBefore,
        ((_, Ordering::Greater), _) => OverlapPosition::OutsideAfter,
        (_, (Ordering::Equal, _)) => OverlapPosition::OnStart(a.from_inclusivity(), b.to_inclusivity()),
        ((_, Ordering::Equal), _) => OverlapPosition::OnEnd(a.to_inclusivity(), b.from_inclusivity()),
        ((Ordering::Less, _), (_, Ordering::Less)) => OverlapPosition::CrossesStart,
        ((Ordering::Greater, _), (_, Ordering::Greater)) => OverlapPosition::CrossesEnd,
        ((Ordering::Greater, _), (_, Ordering::Less)) => OverlapPosition::Inside,
        ((Ordering::Equal, _), (_, Ordering::Less)) => {
            OverlapPosition::InsideAndSameStart(Some(a.from_inclusivity()), Some(b.from_inclusivity()))
        },
        ((Ordering::Greater, _), (_, Ordering::Equal)) => {
            OverlapPosition::InsideAndSameEnd(Some(a.to_inclusivity()), Some(b.to_inclusivity()))
        },
        ((Ordering::Equal, _), (_, Ordering::Equal)) => OverlapPosition::Equal(
            (Some(a.from_inclusivity()), Some(a.to_inclusivity())),
            (Some(b.from_inclusivity()), Some(b.to_inclusivity())),
        ),
        ((Ordering::Equal, _), (_, Ordering::Greater)) => {
            OverlapPosition::ContainsAndSameStart(Some(a.from_inclusivity()), Some(b.from_inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Equal)) => {
            OverlapPosition::ContainsAndSameEnd(Some(a.to_inclusivity()), Some(b.to_inclusivity()))
        },
        ((Ordering::Less, _), (_, Ordering::Greater)) => OverlapPosition::Contains,
    };

    Ok(overlap_position)
}

fn overlap_position_closed_half_open(
    a: &ClosedAbsoluteInterval,
    b: &HalfOpenAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if a.is_malformed() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let overlap_position = match (
        b.reference_time().cmp(a.from()),
        b.reference_time().cmp(a.to()),
        b.opening_direction(),
    ) {
        (Ordering::Less, _, OpeningDirection::ToPast) => OverlapPosition::OutsideBefore,
        (_, Ordering::Greater, OpeningDirection::ToFuture) => OverlapPosition::OutsideAfter,
        (Ordering::Equal, _, OpeningDirection::ToPast) => {
            OverlapPosition::OnStart(a.from_inclusivity(), b.reference_time_inclusivity())
        },
        (_, Ordering::Equal, OpeningDirection::ToFuture) => {
            OverlapPosition::OnEnd(a.to_inclusivity(), b.reference_time_inclusivity())
        },
        (Ordering::Greater, Ordering::Less, OpeningDirection::ToPast) => OverlapPosition::CrossesStart,
        (Ordering::Greater, Ordering::Less, OpeningDirection::ToFuture) => OverlapPosition::CrossesEnd,
        (Ordering::Equal, _, OpeningDirection::ToFuture) => {
            OverlapPosition::ContainsAndSameStart(Some(a.from_inclusivity()), Some(b.reference_time_inclusivity()))
        },
        (_, Ordering::Equal, OpeningDirection::ToPast) => {
            OverlapPosition::ContainsAndSameEnd(Some(a.to_inclusivity()), Some(b.reference_time_inclusivity()))
        },
        (Ordering::Less, _, OpeningDirection::ToFuture) | (_, Ordering::Greater, OpeningDirection::ToPast) => {
            OverlapPosition::Contains
        },
    };

    Ok(overlap_position)
}

fn overlap_position_half_open_closed(
    a: &HalfOpenAbsoluteInterval,
    b: &ClosedAbsoluteInterval,
) -> Result<OverlapPosition, OverlapPositionError> {
    if b.is_malformed() {
        return Err(OverlapPositionError::MalformedInterval);
    }

    let overlap_position = match (
        b.from().cmp(a.reference_time()),
        b.to().cmp(a.reference_time()),
        a.opening_direction(),
    ) {
        (_, Ordering::Less, OpeningDirection::ToFuture) => OverlapPosition::OutsideBefore,
        (Ordering::Greater, _, OpeningDirection::ToPast) => OverlapPosition::OutsideAfter,
        (_, Ordering::Equal, OpeningDirection::ToFuture) => {
            OverlapPosition::OnStart(a.reference_time_inclusivity(), b.to_inclusivity())
        },
        (Ordering::Equal, _, OpeningDirection::ToPast) => {
            OverlapPosition::OnEnd(a.reference_time_inclusivity(), b.from_inclusivity())
        },
        (Ordering::Less, Ordering::Greater, OpeningDirection::ToFuture) => OverlapPosition::CrossesStart,
        (Ordering::Less, Ordering::Greater, OpeningDirection::ToPast) => OverlapPosition::CrossesEnd,
        (Ordering::Less, Ordering::Less, OpeningDirection::ToPast)
        | (Ordering::Greater, Ordering::Greater, OpeningDirection::ToFuture) => OverlapPosition::Inside,
        (Ordering::Equal, Ordering::Greater, OpeningDirection::ToFuture) => {
            OverlapPosition::InsideAndSameStart(Some(a.reference_time_inclusivity()), Some(b.from_inclusivity()))
        },
        (Ordering::Less, Ordering::Equal, OpeningDirection::ToPast) => {
            OverlapPosition::InsideAndSameEnd(Some(a.reference_time_inclusivity()), Some(b.to_inclusivity()))
        },
    };

    Ok(overlap_position)
}

fn overlap_position_half_open_pair(a: &HalfOpenAbsoluteInterval, b: &HalfOpenAbsoluteInterval) -> OverlapPosition {
    match (
        b.reference_time().cmp(a.reference_time()),
        a.opening_direction(),
        b.opening_direction(),
    ) {
        (Ordering::Less, OpeningDirection::ToPast, OpeningDirection::ToPast) => OverlapPosition::InsideAndSameStart(
            Some(a.reference_time_inclusivity()),
            Some(b.reference_time_inclusivity()),
        ),
        (Ordering::Less, OpeningDirection::ToPast, OpeningDirection::ToFuture) => OverlapPosition::CrossesEnd,
        (Ordering::Less, OpeningDirection::ToFuture, OpeningDirection::ToPast) => OverlapPosition::OutsideBefore,
        (Ordering::Less, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => {
            OverlapPosition::ContainsAndSameEnd(
                Some(a.reference_time_inclusivity()),
                Some(b.reference_time_inclusivity()),
            )
        },
        (Ordering::Equal, OpeningDirection::ToPast, OpeningDirection::ToPast)
        | (Ordering::Equal, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => OverlapPosition::Equal(
            (Some(a.reference_time_inclusivity()), None),
            (Some(b.reference_time_inclusivity()), None),
        ),
        (Ordering::Equal, OpeningDirection::ToPast, OpeningDirection::ToFuture) => {
            OverlapPosition::OnEnd(a.reference_time_inclusivity(), b.reference_time_inclusivity())
        },
        (Ordering::Equal, OpeningDirection::ToFuture, OpeningDirection::ToPast) => {
            OverlapPosition::OnStart(a.reference_time_inclusivity(), b.reference_time_inclusivity())
        },
        (Ordering::Greater, OpeningDirection::ToPast, OpeningDirection::ToPast) => {
            OverlapPosition::ContainsAndSameStart(
                Some(a.reference_time_inclusivity()),
                Some(b.reference_time_inclusivity()),
            )
        },
        (Ordering::Greater, OpeningDirection::ToPast, OpeningDirection::ToFuture) => OverlapPosition::OutsideAfter,
        (Ordering::Greater, OpeningDirection::ToFuture, OpeningDirection::ToPast) => OverlapPosition::CrossesStart,
        (Ordering::Greater, OpeningDirection::ToFuture, OpeningDirection::ToFuture) => {
            OverlapPosition::InsideAndSameEnd(
                Some(a.reference_time_inclusivity()),
                Some(b.reference_time_inclusivity()),
            )
        },
    }
}

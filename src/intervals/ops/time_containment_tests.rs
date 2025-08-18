use chrono::Utc;

use super::time_containment::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::prelude::BoundOverlapAmbiguity;
use crate::test_utils::date;

#[test]
fn time_containment_position_strip() {
    assert_eq!(
        TimeContainmentPosition::OutsideBefore.strip(),
        DisambiguatedTimeContainmentPosition::OutsideBefore
    );
    assert_eq!(
        TimeContainmentPosition::OutsideAfter.strip(),
        DisambiguatedTimeContainmentPosition::OutsideAfter
    );
    assert_eq!(
        TimeContainmentPosition::Outside.strip(),
        DisambiguatedTimeContainmentPosition::Outside
    );
    assert_eq!(
        TimeContainmentPosition::OnStart(BoundInclusivity::Inclusive).strip(),
        DisambiguatedTimeContainmentPosition::OnStart,
    );
    assert_eq!(
        TimeContainmentPosition::OnEnd(BoundInclusivity::Exclusive).strip(),
        DisambiguatedTimeContainmentPosition::OnEnd,
    );
    assert_eq!(
        TimeContainmentPosition::Inside.strip(),
        DisambiguatedTimeContainmentPosition::Inside
    );
}

#[test]
fn time_containment_position_strict_disambiguation_outside_before() {
    assert_eq!(
        TimeContainmentPosition::OutsideBefore.disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::OutsideBefore,
    );
}

#[test]
fn time_containment_position_strict_disambiguation_outside_after() {
    assert_eq!(
        TimeContainmentPosition::OutsideAfter.disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::OutsideAfter,
    );
}

#[test]
fn time_containment_position_strict_disambiguation_outside() {
    assert_eq!(
        TimeContainmentPosition::Outside.disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::Outside,
    );
}

#[test]
fn time_containment_position_strict_disambiguation_on_start_inclusive() {
    assert_eq!(
        TimeContainmentPosition::OnStart(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::OnStart,
    );
}

#[test]
fn time_containment_position_strict_disambiguation_on_start_exclusive() {
    assert_eq!(
        TimeContainmentPosition::OnStart(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::OutsideBefore,
    );
}

#[test]
fn time_containment_position_strict_disambiguation_on_end_inclusive() {
    assert_eq!(
        TimeContainmentPosition::OnEnd(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::OnEnd,
    );
}

#[test]
fn time_containment_position_strict_disambiguation_on_end_exclusive() {
    assert_eq!(
        TimeContainmentPosition::OnEnd(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::OutsideAfter,
    );
}

#[test]
fn time_containment_position_strict_disambiguation_inside() {
    assert_eq!(
        TimeContainmentPosition::Inside.disambiguate_using_rule_set(TimeContainmentRuleSet::Strict),
        DisambiguatedTimeContainmentPosition::Inside,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_outside_before() {
    assert_eq!(
        TimeContainmentPosition::OutsideBefore.disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::OutsideBefore,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_outside_after() {
    assert_eq!(
        TimeContainmentPosition::OutsideAfter.disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::OutsideAfter,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_outside() {
    assert_eq!(
        TimeContainmentPosition::Outside.disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::Outside,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_on_start_inclusive() {
    assert_eq!(
        TimeContainmentPosition::OnStart(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::OnStart,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_on_start_exclusive() {
    assert_eq!(
        TimeContainmentPosition::OnStart(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::OnStart,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_on_end_inclusive() {
    assert_eq!(
        TimeContainmentPosition::OnEnd(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::OnEnd,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_on_end_exclusive() {
    assert_eq!(
        TimeContainmentPosition::OnEnd(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::OnEnd,
    );
}

#[test]
fn time_containment_position_lenient_disambiguation_inside() {
    assert_eq!(
        TimeContainmentPosition::Inside.disambiguate_using_rule_set(TimeContainmentRuleSet::Lenient),
        DisambiguatedTimeContainmentPosition::Inside,
    );
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_start_true_on_start() {
    assert!(TimeContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnStart));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_start_true_on_end() {
    assert!(TimeContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_start_true_outside() {
    assert!(TimeContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedTimeContainmentPosition::Outside));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_start_false_on_start() {
    assert!(
        TimeContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnStart)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_start_false_on_end() {
    assert!(!TimeContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_start_false_outside() {
    assert!(
        !TimeContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedTimeContainmentPosition::Outside)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_end_true_on_start() {
    assert!(TimeContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnStart));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_end_true_on_end() {
    assert!(TimeContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_end_true_outside() {
    assert!(TimeContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedTimeContainmentPosition::Outside));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_end_false_on_start() {
    assert!(!TimeContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnStart));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_end_false_on_end() {
    assert!(TimeContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_end_false_outside() {
    assert!(!TimeContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedTimeContainmentPosition::Outside));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_bounds_true_on_start() {
    assert!(
        TimeContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnStart)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_bounds_true_on_end() {
    assert!(TimeContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_bounds_true_outside() {
    assert!(
        TimeContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedTimeContainmentPosition::Outside)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_bounds_false_on_start() {
    assert!(
        TimeContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnStart)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_bounds_false_on_end() {
    assert!(TimeContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_allow_on_bounds_false_outside() {
    assert!(
        !TimeContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedTimeContainmentPosition::Outside)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_start_true_on_start() {
    assert!(!TimeContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnStart));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_start_true_on_end() {
    assert!(TimeContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_start_true_outside() {
    assert!(TimeContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedTimeContainmentPosition::Outside));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_start_false_on_start() {
    assert!(
        !TimeContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnStart)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_start_false_on_end() {
    assert!(!TimeContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_start_false_outside() {
    assert!(
        !TimeContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedTimeContainmentPosition::Outside)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_end_true_on_start() {
    assert!(TimeContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnStart));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_end_true_on_end() {
    assert!(!TimeContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_end_true_outside() {
    assert!(TimeContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedTimeContainmentPosition::Outside));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_end_false_on_start() {
    assert!(!TimeContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnStart));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_end_false_on_end() {
    assert!(!TimeContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_end_false_outside() {
    assert!(!TimeContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedTimeContainmentPosition::Outside));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_bounds_true_on_start() {
    assert!(
        !TimeContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnStart)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_bounds_true_on_end() {
    assert!(!TimeContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_bounds_true_outside() {
    assert!(TimeContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedTimeContainmentPosition::Outside));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_bounds_false_on_start() {
    assert!(
        !TimeContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnStart)
    );
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_bounds_false_on_end() {
    assert!(!TimeContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedTimeContainmentPosition::OnEnd));
}

#[test]
fn time_containment_rule_counts_as_contained_deny_on_bounds_false_outside() {
    assert!(
        !TimeContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedTimeContainmentPosition::Outside)
    );
}

use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;

use super::bound_containment::*;

#[test]
fn disambiguate_bound_position() {
    assert_eq!(BoundPosition::OutsideBefore.disambiguate(), DisambiguatedBoundPosition::OutsideBefore);
    assert_eq!(BoundPosition::OutsideAfter.disambiguate(), DisambiguatedBoundPosition::OutsideAfter);
    assert_eq!(BoundPosition::Outside.disambiguate(), DisambiguatedBoundPosition::Outside);
    assert_eq!(BoundPosition::OnStart(None).disambiguate(), DisambiguatedBoundPosition::OnStart);
    assert_eq!(
        BoundPosition::OnStart(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive))
        ).disambiguate(),
        DisambiguatedBoundPosition::OnStart,
    );
    assert_eq!(BoundPosition::OnEnd(None).disambiguate(), DisambiguatedBoundPosition::OnEnd);
    assert_eq!(
        BoundPosition::OnEnd(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive))
        ).disambiguate(),
        DisambiguatedBoundPosition::OnEnd,
    );
    assert_eq!(BoundPosition::Equal.disambiguate(), DisambiguatedBoundPosition::Equal);
    assert_eq!(BoundPosition::Inside.disambiguate(), DisambiguatedBoundPosition::Inside);
}

#[test]
fn disambiguate_position_on_start_no_ambiguity() {
    assert_eq!(
        BoundPosition::OnStart(None).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::OnStart,
    );
}

#[test]
fn disambiguate_position_on_start_bound_before() {
    assert_eq!(
        BoundPosition::OnStart(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive))
        ).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::OutsideBefore,
    );
}

#[test]
fn disambiguate_position_on_start_bound_equal() {
    assert_eq!(
        BoundPosition::OnStart(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)),
        ).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::OnStart,
    );
}

#[test]
fn disambiguate_position_on_start_bound_after() {
    assert_eq!(
        BoundPosition::OnStart(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)),
        ).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::Inside,
    );
}

#[test]
fn disambiguate_position_on_end_no_ambiguity() {
    assert_eq!(
        BoundPosition::OnEnd(None).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::OnEnd,
    );
}

#[test]
fn disambiguate_position_on_end_bound_before() {
    assert_eq!(
        BoundPosition::OnEnd(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive))
        ).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::Inside,
    );
}

#[test]
fn disambiguate_position_on_end_bound_equal() {
    assert_eq!(
        BoundPosition::OnEnd(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive))
        ).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::OnEnd,
    );
}

#[test]
fn disambiguate_position_on_end_bound_after() {
    assert_eq!(
        BoundPosition::OnEnd(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive))
        ).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundPosition::OutsideAfter,
    );
}

#[test]
fn counts_as_contained_allow_on_start_from_true_on_start() {
    assert!(BoundContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_allow_on_start_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_start_from_false_on_start() {
    assert!(BoundContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_allow_on_start_from_false_on_end() {
    assert!(!BoundContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_end_from_true_on_start() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_allow_on_end_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_end_from_false_on_start() {
    assert!(!BoundContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_allow_on_end_from_false_on_end() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_on_start() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_outside() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundPosition::Outside));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_on_start() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_on_end() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_outside() {
    assert!(!BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundPosition::Outside));
}

#[test]
fn counts_as_contained_deny_on_start_from_true_on_start() {
    assert!(!BoundContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_deny_on_start_from_true_on_end() {
    assert!(BoundContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_start_from_false_on_start() {
    assert!(!BoundContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_deny_on_start_from_false_on_end() {
    assert!(!BoundContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_end_from_true_on_start() {
    assert!(BoundContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_deny_on_end_from_true_on_end() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_end_from_false_on_start() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_deny_on_end_from_false_on_end() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_on_start() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_on_end() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_outside() {
    assert!(BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundPosition::Outside));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_on_start() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundPosition::OnStart));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_on_end() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_outside() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundPosition::Outside));
}

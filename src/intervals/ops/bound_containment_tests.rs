use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;

use super::bound_containment::*;

#[test]
fn strip_bound_position() {
    assert_eq!(
        BoundContainmentPosition::OutsideBefore.strip(),
        DisambiguatedBoundContainmentPosition::OutsideBefore
    );
    assert_eq!(
        BoundContainmentPosition::OutsideAfter.strip(),
        DisambiguatedBoundContainmentPosition::OutsideAfter
    );
    assert_eq!(
        BoundContainmentPosition::Outside.strip(),
        DisambiguatedBoundContainmentPosition::Outside
    );
    assert_eq!(
        BoundContainmentPosition::OnStart(None).strip(),
        DisambiguatedBoundContainmentPosition::OnStart
    );
    assert_eq!(
        BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )))
        .strip(),
        DisambiguatedBoundContainmentPosition::OnStart,
    );
    assert_eq!(
        BoundContainmentPosition::OnEnd(None).strip(),
        DisambiguatedBoundContainmentPosition::OnEnd
    );
    assert_eq!(
        BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )))
        .strip(),
        DisambiguatedBoundContainmentPosition::OnEnd,
    );
    assert_eq!(
        BoundContainmentPosition::Equal.strip(),
        DisambiguatedBoundContainmentPosition::Equal
    );
    assert_eq!(
        BoundContainmentPosition::Inside.strip(),
        DisambiguatedBoundContainmentPosition::Inside
    );
}

#[test]
fn disambiguate_position_on_start_no_ambiguity() {
    assert_eq!(
        BoundContainmentPosition::OnStart(None).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::OnStart,
    );
}

#[test]
fn disambiguate_position_on_start_bound_before() {
    assert_eq!(
        BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::OutsideBefore,
    );
}

#[test]
fn disambiguate_position_on_start_bound_equal() {
    assert_eq!(
        BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )),)
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::OnStart,
    );
}

#[test]
fn disambiguate_position_on_start_bound_after() {
    assert_eq!(
        BoundContainmentPosition::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive
        )),)
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::Inside,
    );
}

#[test]
fn disambiguate_position_on_end_no_ambiguity() {
    assert_eq!(
        BoundContainmentPosition::OnEnd(None).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::OnEnd,
    );
}

#[test]
fn disambiguate_position_on_end_bound_before() {
    assert_eq!(
        BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::Inside,
    );
}

#[test]
fn disambiguate_position_on_end_bound_equal() {
    assert_eq!(
        BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::OnEnd,
    );
}

#[test]
fn disambiguate_position_on_end_bound_after() {
    assert_eq!(
        BoundContainmentPosition::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPosition::OutsideAfter,
    );
}

#[test]
fn counts_as_contained_allow_on_start_from_true_on_start() {
    assert!(
        BoundContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_allow_on_start_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_start_from_false_on_start() {
    assert!(
        BoundContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_allow_on_start_from_false_on_end() {
    assert!(
        !BoundContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnEnd)
    );
}

#[test]
fn counts_as_contained_allow_on_end_from_true_on_start() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnStart));
}

#[test]
fn counts_as_contained_allow_on_end_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_end_from_false_on_start() {
    assert!(
        !BoundContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_allow_on_end_from_false_on_end() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_on_start() {
    assert!(
        BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_on_end() {
    assert!(
        BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnEnd)
    );
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_outside() {
    assert!(
        BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPosition::Outside)
    );
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_on_start() {
    assert!(
        BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_on_end() {
    assert!(
        BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnEnd)
    );
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_outside() {
    assert!(
        !BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPosition::Outside)
    );
}

#[test]
fn counts_as_contained_deny_on_start_from_true_on_start() {
    assert!(
        !BoundContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_deny_on_start_from_true_on_end() {
    assert!(BoundContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_start_from_false_on_start() {
    assert!(
        !BoundContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_deny_on_start_from_false_on_end() {
    assert!(
        !BoundContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnEnd)
    );
}

#[test]
fn counts_as_contained_deny_on_end_from_true_on_start() {
    assert!(BoundContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnStart));
}

#[test]
fn counts_as_contained_deny_on_end_from_true_on_end() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_end_from_false_on_start() {
    assert!(
        !BoundContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_deny_on_end_from_false_on_end() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_on_start() {
    assert!(
        !BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_on_end() {
    assert!(
        !BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPosition::OnEnd)
    );
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_outside() {
    assert!(
        BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPosition::Outside)
    );
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_on_start() {
    assert!(
        !BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnStart)
    );
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_on_end() {
    assert!(
        !BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPosition::OnEnd)
    );
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_outside() {
    assert!(
        !BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPosition::Outside)
    );
}

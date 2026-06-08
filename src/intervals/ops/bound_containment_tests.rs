use super::bound_containment::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;

#[test]
fn strip_bound_position() {
    assert_eq!(
        BoundContainmentPos::OutsideBefore.strip(),
        DisambiguatedBoundContainmentPos::OutsideBefore
    );
    assert_eq!(
        BoundContainmentPos::OutsideAfter.strip(),
        DisambiguatedBoundContainmentPos::OutsideAfter
    );
    assert_eq!(
        BoundContainmentPos::Outside.strip(),
        DisambiguatedBoundContainmentPos::Outside
    );
    assert_eq!(
        BoundContainmentPos::OnStart(None).strip(),
        DisambiguatedBoundContainmentPos::OnStart
    );
    assert_eq!(
        BoundContainmentPos::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )))
        .strip(),
        DisambiguatedBoundContainmentPos::OnStart,
    );
    assert_eq!(
        BoundContainmentPos::OnEnd(None).strip(),
        DisambiguatedBoundContainmentPos::OnEnd
    );
    assert_eq!(
        BoundContainmentPos::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )))
        .strip(),
        DisambiguatedBoundContainmentPos::OnEnd,
    );
    assert_eq!(
        BoundContainmentPos::Equal.strip(),
        DisambiguatedBoundContainmentPos::Equal
    );
    assert_eq!(
        BoundContainmentPos::Inside.strip(),
        DisambiguatedBoundContainmentPos::Inside
    );
}

#[test]
fn disambiguate_position_on_start_no_ambiguity() {
    assert_eq!(
        BoundContainmentPos::OnStart(None).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::OnStart,
    );
}

#[test]
fn disambiguate_position_on_start_bound_before() {
    assert_eq!(
        BoundContainmentPos::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::OutsideBefore,
    );
}

#[test]
fn disambiguate_position_on_start_bound_equal() {
    assert_eq!(
        BoundContainmentPos::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )),)
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::OnStart,
    );
}

#[test]
fn disambiguate_position_on_start_bound_after() {
    assert_eq!(
        BoundContainmentPos::OnStart(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive
        )),)
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::Inside,
    );
}

#[test]
fn disambiguate_position_on_end_no_ambiguity() {
    assert_eq!(
        BoundContainmentPos::OnEnd(None).disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::OnEnd,
    );
}

#[test]
fn disambiguate_position_on_end_bound_before() {
    assert_eq!(
        BoundContainmentPos::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::Inside,
    );
}

#[test]
fn disambiguate_position_on_end_bound_equal() {
    assert_eq!(
        BoundContainmentPos::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::OnEnd,
    );
}

#[test]
fn disambiguate_position_on_end_bound_after() {
    assert_eq!(
        BoundContainmentPos::OnEnd(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive
        )))
        .disambiguate_using_rule_set(BoundContainmentRuleSet::Strict),
        DisambiguatedBoundContainmentPos::OutsideAfter,
    );
}

#[test]
fn counts_as_contained_allow_on_start_from_true_on_start() {
    assert!(BoundContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_allow_on_start_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_start_from_false_on_start() {
    assert!(BoundContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_allow_on_start_from_false_on_end() {
    assert!(!BoundContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_end_from_true_on_start() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_allow_on_end_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_end_from_false_on_start() {
    assert!(!BoundContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_allow_on_end_from_false_on_end() {
    assert!(BoundContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_on_start() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_on_end() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_true_outside() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPos::Outside));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_on_start() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_on_end() {
    assert!(BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_allow_on_bounds_from_false_outside() {
    assert!(!BoundContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPos::Outside));
}

#[test]
fn counts_as_contained_deny_on_start_from_true_on_start() {
    assert!(!BoundContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_deny_on_start_from_true_on_end() {
    assert!(BoundContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_start_from_false_on_start() {
    assert!(!BoundContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_deny_on_start_from_false_on_end() {
    assert!(!BoundContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_end_from_true_on_start() {
    assert!(BoundContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_deny_on_end_from_true_on_end() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_end_from_false_on_start() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_deny_on_end_from_false_on_end() {
    assert!(!BoundContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_on_start() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_on_end() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_true_outside() {
    assert!(BoundContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedBoundContainmentPos::Outside));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_on_start() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnStart));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_on_end() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPos::OnEnd));
}

#[test]
fn counts_as_contained_deny_on_bounds_from_false_outside() {
    assert!(!BoundContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedBoundContainmentPos::Outside));
}

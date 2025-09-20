use chrono::Utc;

use super::point_containment::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;
use crate::test_utils::date;

#[test]
fn point_containment_position_strip() {
    assert_eq!(
        PointContainmentPosition::OutsideBefore.strip(),
        DisambiguatedPointContainmentPosition::OutsideBefore
    );
    assert_eq!(
        PointContainmentPosition::OutsideAfter.strip(),
        DisambiguatedPointContainmentPosition::OutsideAfter
    );
    assert_eq!(
        PointContainmentPosition::Outside.strip(),
        DisambiguatedPointContainmentPosition::Outside
    );
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Inclusive).strip(),
        DisambiguatedPointContainmentPosition::OnStart,
    );
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive).strip(),
        DisambiguatedPointContainmentPosition::OnEnd,
    );
    assert_eq!(
        PointContainmentPosition::Inside.strip(),
        DisambiguatedPointContainmentPosition::Inside
    );
}

#[test]
fn point_containment_position_strict_disambiguation_outside_before() {
    assert_eq!(
        PointContainmentPosition::OutsideBefore.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideBefore,
    );
}

#[test]
fn point_containment_position_strict_disambiguation_outside_after() {
    assert_eq!(
        PointContainmentPosition::OutsideAfter.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideAfter,
    );
}

#[test]
fn point_containment_position_strict_disambiguation_outside() {
    assert_eq!(
        PointContainmentPosition::Outside.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::Outside,
    );
}

#[test]
fn point_containment_position_strict_disambiguation_on_start_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OnStart,
    );
}

#[test]
fn point_containment_position_strict_disambiguation_on_start_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideBefore,
    );
}

#[test]
fn point_containment_position_strict_disambiguation_on_end_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OnEnd,
    );
}

#[test]
fn point_containment_position_strict_disambiguation_on_end_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideAfter,
    );
}

#[test]
fn point_containment_position_strict_disambiguation_inside() {
    assert_eq!(
        PointContainmentPosition::Inside.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::Inside,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_outside_before() {
    assert_eq!(
        PointContainmentPosition::OutsideBefore.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OutsideBefore,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_outside_after() {
    assert_eq!(
        PointContainmentPosition::OutsideAfter.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OutsideAfter,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_outside() {
    assert_eq!(
        PointContainmentPosition::Outside.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::Outside,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_on_start_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnStart,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_on_start_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnStart,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_on_end_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnEnd,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_on_end_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnEnd,
    );
}

#[test]
fn point_containment_position_lenient_disambiguation_inside() {
    assert_eq!(
        PointContainmentPosition::Inside.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::Inside,
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_start_true_on_start() {
    assert!(
        PointContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_start_true_on_end() {
    assert!(PointContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_start_true_outside() {
    assert!(
        PointContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_start_false_on_start() {
    assert!(
        PointContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_start_false_on_end() {
    assert!(
        !PointContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_start_false_outside() {
    assert!(
        !PointContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_end_true_on_start() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart));
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_end_true_on_end() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_end_true_outside() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside));
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_end_false_on_start() {
    assert!(
        !PointContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_end_false_on_end() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_end_false_outside() {
    assert!(
        !PointContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_bounds_true_on_start() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_bounds_true_on_end() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_bounds_true_outside() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_bounds_false_on_start() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_bounds_false_on_end() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_allow_on_bounds_false_outside() {
    assert!(
        !PointContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_start_true_on_start() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_start_true_on_end() {
    assert!(PointContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_start_true_outside() {
    assert!(
        PointContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_start_false_on_start() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_start_false_on_end() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_start_false_outside() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_end_true_on_start() {
    assert!(PointContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart));
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_end_true_on_end() {
    assert!(!PointContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_end_true_outside() {
    assert!(PointContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside));
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_end_false_on_start() {
    assert!(
        !PointContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_end_false_on_end() {
    assert!(!PointContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_end_false_outside() {
    assert!(
        !PointContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_bounds_true_on_start() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_bounds_true_on_end() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_bounds_true_outside() {
    assert!(
        PointContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_bounds_false_on_start() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_bounds_false_on_end() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn point_containment_rule_counts_as_contained_deny_on_bounds_false_outside() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn point_containment_time_outside_before() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position(date(&Utc, 2025, 1, 1)),
        Ok(PointContainmentPosition::OutsideBefore),
    );
}

#[test]
fn point_containment_time_outside_after() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position(date(&Utc, 2025, 1, 4)),
        Ok(PointContainmentPosition::OutsideAfter),
    );
}

#[test]
fn point_containment_time_outside() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.point_containment_position(date(&Utc, 2025, 1, 1)),
        Ok(PointContainmentPosition::Outside),
    );
}

#[test]
fn point_containment_time_on_start_inclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position(date(&Utc, 2025, 1, 2)),
        Ok(PointContainmentPosition::OnStart(BoundInclusivity::Inclusive)),
    );
}

#[test]
fn point_containment_time_on_start_exclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position(date(&Utc, 2025, 1, 2)),
        Ok(PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)),
    );
}

#[test]
fn point_containment_time_on_end_inclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position(date(&Utc, 2025, 1, 3)),
        Ok(PointContainmentPosition::OnEnd(BoundInclusivity::Inclusive)),
    );
}

#[test]
fn point_containment_time_on_end_exclusive() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Exclusive,
            )),
        )
        .point_containment_position(date(&Utc, 2025, 1, 3)),
        Ok(PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive)),
    );
}

#[test]
fn point_containment_time_inside() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position(date(&Utc, 2025, 1, 2)),
        Ok(PointContainmentPosition::Inside),
    );
}

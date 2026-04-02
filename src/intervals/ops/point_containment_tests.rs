use std::error::Error;

use jiff::Zoned;

use super::point_containment::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn position_strip() {
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
fn position_strict_disambiguation_outside_before() {
    assert_eq!(
        PointContainmentPosition::OutsideBefore.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideBefore,
    );
}

#[test]
fn position_strict_disambiguation_outside_after() {
    assert_eq!(
        PointContainmentPosition::OutsideAfter.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideAfter,
    );
}

#[test]
fn position_strict_disambiguation_outside() {
    assert_eq!(
        PointContainmentPosition::Outside.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::Outside,
    );
}

#[test]
fn position_strict_disambiguation_on_start_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OnStart,
    );
}

#[test]
fn position_strict_disambiguation_on_start_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideBefore,
    );
}

#[test]
fn position_strict_disambiguation_on_end_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OnEnd,
    );
}

#[test]
fn position_strict_disambiguation_on_end_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::OutsideAfter,
    );
}

#[test]
fn position_strict_disambiguation_inside() {
    assert_eq!(
        PointContainmentPosition::Inside.disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
        DisambiguatedPointContainmentPosition::Inside,
    );
}

#[test]
fn position_lenient_disambiguation_outside_before() {
    assert_eq!(
        PointContainmentPosition::OutsideBefore.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OutsideBefore,
    );
}

#[test]
fn position_lenient_disambiguation_outside_after() {
    assert_eq!(
        PointContainmentPosition::OutsideAfter.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OutsideAfter,
    );
}

#[test]
fn position_lenient_disambiguation_outside() {
    assert_eq!(
        PointContainmentPosition::Outside.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::Outside,
    );
}

#[test]
fn position_lenient_disambiguation_on_start_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnStart,
    );
}

#[test]
fn position_lenient_disambiguation_on_start_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnStart,
    );
}

#[test]
fn position_lenient_disambiguation_on_end_inclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnEnd,
    );
}

#[test]
fn position_lenient_disambiguation_on_end_exclusive() {
    assert_eq!(
        PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::OnEnd,
    );
}

#[test]
fn position_lenient_disambiguation_inside() {
    assert_eq!(
        PointContainmentPosition::Inside.disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
        DisambiguatedPointContainmentPosition::Inside,
    );
}

#[test]
fn rule_counts_as_contained_allow_on_start_true_on_start() {
    assert!(
        PointContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_start_true_on_end() {
    assert!(PointContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn rule_counts_as_contained_allow_on_start_true_outside() {
    assert!(
        PointContainmentRule::AllowOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_start_false_on_start() {
    assert!(
        PointContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_start_false_on_end() {
    assert!(
        !PointContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_start_false_outside() {
    assert!(
        !PointContainmentRule::AllowOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_end_true_on_start() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart));
}

#[test]
fn rule_counts_as_contained_allow_on_end_true_on_end() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn rule_counts_as_contained_allow_on_end_true_outside() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside));
}

#[test]
fn rule_counts_as_contained_allow_on_end_false_on_start() {
    assert!(
        !PointContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_end_false_on_end() {
    assert!(PointContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn rule_counts_as_contained_allow_on_end_false_outside() {
    assert!(
        !PointContainmentRule::AllowOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_bounds_true_on_start() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_bounds_true_on_end() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_bounds_true_outside() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_bounds_false_on_start() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_bounds_false_on_end() {
    assert!(
        PointContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn rule_counts_as_contained_allow_on_bounds_false_outside() {
    assert!(
        !PointContainmentRule::AllowOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_start_true_on_start() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_start_true_on_end() {
    assert!(PointContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn rule_counts_as_contained_deny_on_start_true_outside() {
    assert!(
        PointContainmentRule::DenyOnStart.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_start_false_on_start() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_start_false_on_end() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_start_false_outside() {
    assert!(
        !PointContainmentRule::DenyOnStart.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_end_true_on_start() {
    assert!(PointContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart));
}

#[test]
fn rule_counts_as_contained_deny_on_end_true_on_end() {
    assert!(!PointContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn rule_counts_as_contained_deny_on_end_true_outside() {
    assert!(PointContainmentRule::DenyOnEnd.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside));
}

#[test]
fn rule_counts_as_contained_deny_on_end_false_on_start() {
    assert!(
        !PointContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_end_false_on_end() {
    assert!(!PointContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd));
}

#[test]
fn rule_counts_as_contained_deny_on_end_false_outside() {
    assert!(
        !PointContainmentRule::DenyOnEnd.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_bounds_true_on_start() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_bounds_true_on_end() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_bounds_true_outside() {
    assert!(
        PointContainmentRule::DenyOnBounds.counts_as_contained(true, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_bounds_false_on_start() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnStart)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_bounds_false_on_end() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::OnEnd)
    );
}

#[test]
fn rule_counts_as_contained_deny_on_bounds_false_outside() {
    assert!(
        !PointContainmentRule::DenyOnBounds.counts_as_contained(false, DisambiguatedPointContainmentPosition::Outside)
    );
}

#[test]
fn time_outside_before() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::OutsideBefore),
    );

    Ok(())
}

#[test]
fn time_outside_after() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::OutsideAfter),
    );

    Ok(())
}

#[test]
fn time_outside() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsoluteBoundPair::Empty
            .point_containment_position("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::Outside),
    );

    Ok(())
}

#[test]
fn time_on_start_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::OnStart(BoundInclusivity::Inclusive)),
    );

    Ok(())
}

#[test]
fn time_on_start_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)),
    );

    Ok(())
}

#[test]
fn time_on_end_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::OnEnd(BoundInclusivity::Inclusive)),
    );

    Ok(())
}

#[test]
fn time_on_end_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        )
        .point_containment_position("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive)),
    );

    Ok(())
}

#[test]
fn time_inside() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )),
        )
        .point_containment_position("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
        Ok(PointContainmentPosition::Inside),
    );

    Ok(())
}

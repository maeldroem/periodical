use crate::intervals::meta::BoundInclusivity;

use super::bound_overlap_ambiguity::*;

#[test]
fn ambiguity_is_both_starts() {
    assert!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_starts()
    );
    assert!(
        !BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_starts()
    );
    assert!(
        !BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_starts()
    );
    assert!(
        !BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_starts()
    );
}

#[test]
fn ambiguity_is_both_ends() {
    assert!(
        !BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_ends()
    );
    assert!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_ends()
    );
    assert!(
        !BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_ends()
    );
    assert!(
        !BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_both_ends()
    );
}

#[test]
fn ambiguity_is_start_end() {
    assert!(
        !BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_start_end()
    );
    assert!(
        !BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_start_end()
    );
    assert!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_start_end()
    );
    assert!(
        !BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_start_end()
    );
}

#[test]
fn ambiguity_is_end_start() {
    assert!(
        !BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_end_start()
    );
    assert!(
        !BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_end_start()
    );
    assert!(
        !BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_end_start()
    );
    assert!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .is_end_start()
    );
}

#[test]
fn strict_disambiguation_both_starts_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn strict_disambiguation_both_starts_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn strict_disambiguation_both_starts_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn strict_disambiguation_both_starts_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn strict_disambiguation_both_ends_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn strict_disambiguation_both_ends_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn strict_disambiguation_both_ends_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn strict_disambiguation_both_ends_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn strict_disambiguation_start_end_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn strict_disambiguation_start_end_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn strict_disambiguation_start_end_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn strict_disambiguation_start_end_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn strict_disambiguation_end_start_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn strict_disambiguation_end_start_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn strict_disambiguation_end_start_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn strict_disambiguation_end_start_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn lenient_disambiguation_both_starts_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_both_starts_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_both_starts_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_both_starts_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_both_ends_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_both_ends_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_both_ends_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_both_ends_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_start_end_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_start_end_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_start_end_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_start_end_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn lenient_disambiguation_end_start_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_end_start_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_end_start_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn lenient_disambiguation_end_start_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Lenient),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn very_lenient_disambiguation_both_starts_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_both_starts_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_both_starts_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_both_starts_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_both_ends_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_both_ends_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_both_ends_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_both_ends_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_start_end_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_start_end_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_start_end_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_start_end_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_end_start_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_end_start_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_end_start_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn very_lenient_disambiguation_end_start_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::VeryLenient),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_starts_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_starts_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_starts_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_starts_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_ends_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_ends_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_ends_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn continuous_to_future_disambiguation_both_ends_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_start_end_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_start_end_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_start_end_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_future_disambiguation_start_end_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_future_disambiguation_end_start_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_end_start_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn continuous_to_future_disambiguation_end_start_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_future_disambiguation_end_start_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToFuture),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_starts_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_starts_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_starts_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_starts_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_ends_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_ends_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_ends_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn continuous_to_past_disambiguation_both_ends_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_start_end_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_start_end_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_past_disambiguation_start_end_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_start_end_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::StartEnd(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Before,
    );
}

#[test]
fn continuous_to_past_disambiguation_end_start_inclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_end_start_inclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::Equal,
    );
}

#[test]
fn continuous_to_past_disambiguation_end_start_exclusive_inclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::After,
    );
}

#[test]
fn continuous_to_past_disambiguation_end_start_exclusive_exclusive() {
    assert_eq!(
        BoundOverlapAmbiguity::EndStart(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::ContinuousToPast),
        DisambiguatedBoundOverlap::After,
    );
}

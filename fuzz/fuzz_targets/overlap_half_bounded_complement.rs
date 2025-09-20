#![no_main]

use libfuzzer_sys::fuzz_target;
use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
use periodical::prelude::*;

fuzz_target!(|data: (HalfBoundedAbsoluteInterval, OverlapRuleSet)| {
    let (source_half_bounded, rule_set) = data;

    let complement_half_bounded = source_half_bounded
        .complement()
        .single()
        .expect("A half-bounded interval always produces a single complement");

    let overlap_position = source_half_bounded
        .disambiguated_overlap_position(&complement_half_bounded, rule_set)
        .expect("Somehow the overlap position produced an Err?");

    match (
        source_half_bounded.opening_direction(),
        source_half_bounded.reference_inclusivity(),
        rule_set,
    ) {
        (
            OpeningDirection::ToFuture,
            BoundInclusivity::Exclusive,
            OverlapRuleSet::ContinuousToFuture | OverlapRuleSet::Strict,
        )
        | (
            OpeningDirection::ToFuture,
            BoundInclusivity::Inclusive,
            OverlapRuleSet::ContinuousToPast | OverlapRuleSet::Strict,
        ) => {
            assert_eq!(
                overlap_position,
                DisambiguatedOverlapPosition::OutsideAfter,
                "Overlap position was different than expected. Complement is {:#?}",
                &complement_half_bounded,
            );
        },
        (OpeningDirection::ToFuture, ..) => {
            assert_eq!(
                overlap_position,
                DisambiguatedOverlapPosition::StartsOnEnd,
                "Overlap position was different than expected. Complement is {:#?}",
                &complement_half_bounded,
            );
        },
        (
            OpeningDirection::ToPast,
            BoundInclusivity::Exclusive,
            OverlapRuleSet::ContinuousToPast | OverlapRuleSet::Strict,
        )
        | (
            OpeningDirection::ToPast,
            BoundInclusivity::Inclusive,
            OverlapRuleSet::ContinuousToFuture | OverlapRuleSet::Strict,
        ) => {
            assert_eq!(
                overlap_position,
                DisambiguatedOverlapPosition::OutsideBefore,
                "Overlap position was different than expected. Complement is {:#?}",
                &complement_half_bounded,
            );
        },
        (OpeningDirection::ToPast, ..) => {
            assert_eq!(
                overlap_position,
                DisambiguatedOverlapPosition::EndsOnStart,
                "Overlap position was different than expected. Complement is {:#?}",
                &complement_half_bounded,
            );
        },
    }
});

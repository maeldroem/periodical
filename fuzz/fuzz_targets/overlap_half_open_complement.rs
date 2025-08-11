#![no_main]

use libfuzzer_sys::fuzz_target;
use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
use periodical::prelude::*;

fuzz_target!(|data: (HalfOpenAbsoluteInterval, OverlapRuleSet)| {
    let (source_half_open, rule_set) = data;

    let complement_half_open = source_half_open
        .complement()
        .single()
        .expect("A half-open interval always produces a single complement");

    let overlap_position = source_half_open
        .disambiguated_overlap_position(&complement_half_open, rule_set)
        .expect("Somehow the overlap position produced an Err?");

    match (
        source_half_open.opening_direction(),
        source_half_open.reference_time_inclusivity(),
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
                &complement_half_open,
            );
        },
        (OpeningDirection::ToFuture, ..) => {
            assert_eq!(
                overlap_position,
                DisambiguatedOverlapPosition::StartsOnEnd,
                "Overlap position was different than expected. Complement is {:#?}",
                &complement_half_open,
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
                &complement_half_open,
            );
        },
        (OpeningDirection::ToPast, ..) => {
            assert_eq!(
                overlap_position,
                DisambiguatedOverlapPosition::EndsOnStart,
                "Overlap position was different than expected. Complement is {:#?}",
                &complement_half_open,
            );
        },
    }
});

use std::error::Error;

use jiff::Zoned;

use super::absolute::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
use crate::iter::intervals::bounds::AbsBoundsIteratorDispatcher;
use crate::iter::intervals::layered_bounds::abs_state_change::LayeredBoundsStateChangeAtAbsBound;
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

#[test]
fn create() -> Result<(), Box<dyn Error>> {
    let first_layer_data = [
        AbsStartBound::InfinitePast.to_bound(),
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsEndBound::InfiniteFuture.to_bound(),
    ];

    let second_layer_data = [
        AbsStartBound::InfinitePast.to_bound(),
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsEndBound::InfiniteFuture.to_bound(),
    ];

    let _ = LayeredAbsBounds::new(first_layer_data.into_iter(), second_layer_data.into_iter());

    Ok(())
}

#[allow(clippy::too_many_lines)]
#[test]
fn run() -> Result<(), Box<dyn Error>> {
    // first layer:  [--1--]            [--3--]             (--6--]  [--7--] [--9--)(--11-] [-13-]
    // second layer:           [--2--]        (--4--] [--5--]           [--8--] [10)(--12---]
    let first_layer_data = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 7
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 9
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 11
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 13
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
    ];

    let second_layer_data = [
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 8
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 10
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 12
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
    ];

    let mut first_layer_bounds = first_layer_data.abs_bounds_iter().collect::<Vec<_>>();
    let mut second_layer_bounds = second_layer_data.abs_bounds_iter().collect::<Vec<_>>();

    first_layer_bounds.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));
    second_layer_bounds.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));

    // first layer:    [--1--]            [--3--]             (--6--]  [--7--]  [---9--)(--11-] [-13-]
    // second layer:   :     :   [--2--]  :     (--4--] [--5--]     :  :  [---8---] [10)(--12---]
    // change refs:    A     B   C     D  E     F     G H     I     J  K  L  M  N O P  QR     S T    U
    assert_eq!(
        LayeredAbsBounds::new(first_layer_bounds.into_iter(), second_layer_bounds.into_iter(),)
            .collect::<Vec<_>>(),
        vec![
            // A
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // B
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // C
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // D
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // E
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // F
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // G
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // H
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // I
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // J
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsFiniteBoundPos::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // K
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // L
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // M
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsFiniteBoundPos::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // N
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // O
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsFiniteBoundPos::new("2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // P
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // Q
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // R
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsFiniteBoundPos::new("2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // S
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsFiniteBoundPos::new("2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // T1
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // T2
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsFiniteBoundPos::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // U
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsFiniteBoundPos::new("2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
        ],
    );

    Ok(())
}

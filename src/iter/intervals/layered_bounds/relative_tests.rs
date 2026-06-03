use jiff::SignedDuration;

use super::relative::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelStartBound,
};
use crate::iter::intervals::bounds::RelBoundsIteratorDispatcher;
use crate::iter::intervals::layered_bounds::rel_state_change::LayeredBoundsStateChangeAtRelBound;
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

#[test]
fn create() {
    let first_layer_data = [
        RelStartBound::InfinitePast.to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(102))
            .to_end_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(105))
            .to_start_bound()
            .to_bound(),
        RelEndBound::InfiniteFuture.to_bound(),
    ];

    let second_layer_data = [
        RelStartBound::InfinitePast.to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(102))
            .to_end_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(105))
            .to_start_bound()
            .to_bound(),
        RelEndBound::InfiniteFuture.to_bound(),
    ];

    let _ = LayeredRelBounds::new(first_layer_data.into_iter(), second_layer_data.into_iter());
}

#[allow(clippy::too_many_lines)]
#[test]
fn run() {
    // first layer:  [--1--]            [--3--]             (--6--]  [--7--] [--9--)(--11-] [-13-]
    // second layer:           [--2--]        (--4--] [--5--]           [--8--] [10)(--12---]
    let first_layer_data = [
        // 1
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(105)).to_end_bound(),
        ),
        // 3
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(117)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(120)).to_end_bound(),
        ),
        // 6
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_inclusivity(
                SignedDuration::from_hours(205),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(210)).to_end_bound(),
        ),
        // 7
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(215)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(225)).to_end_bound(),
        ),
        // 9
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(226)).to_start_bound(),
            RelFiniteBoundPos::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 11
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(315)).to_end_bound(),
        ),
        // 13
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(320)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(325)).to_end_bound(),
        ),
    ];

    let second_layer_data = [
        // 2
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(110)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(115)).to_end_bound(),
        ),
        // 4
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_inclusivity(
                SignedDuration::from_hours(120),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(125)).to_end_bound(),
        ),
        // 5
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(130)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(205)).to_end_bound(),
        ),
        // 8
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(220)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(301)).to_end_bound(),
        ),
        // 10
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(304)).to_start_bound(),
            RelFiniteBoundPos::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 12
        RelBoundPair::new(
            RelFiniteBoundPos::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(320)).to_end_bound(),
        ),
    ];

    let mut first_layer_bounds = first_layer_data.rel_bounds_iter().collect::<Vec<_>>();
    let mut second_layer_bounds = second_layer_data.rel_bounds_iter().collect::<Vec<_>>();

    first_layer_bounds.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));
    second_layer_bounds.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));

    // first layer:    [--1--]            [--3--]             (--6--]  [--7--]  [---9--)(--11-] [-13-]
    // second layer:   :     :   [--2--]  :     (--4--] [--5--]     :  :  [---8---] [10)(--12---]
    // change refs:    A     B   C     D  E     F     G H     I     J  K  L  M  N O P  QR     S T    U
    assert_eq!(
        LayeredRelBounds::new(first_layer_bounds.into_iter(), second_layer_bounds.into_iter(),)
            .collect::<Vec<_>>(),
        vec![
            // A
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(101),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
            ),
            // B
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(105)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(105),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // C
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(110),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(110)).to_start_bound()),
            ),
            // D
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(115)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(115),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // E
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(117),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(117)).to_start_bound()),
            ),
            // F
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(120)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(120),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // G
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(125)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(125),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // H
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(130),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(130)).to_start_bound()),
            ),
            // I
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(205)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(205),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // J
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(210)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(210),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // K
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(215),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(215)).to_start_bound()),
            ),
            // L
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(220),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(220)).to_start_bound()),
            ),
            // M
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(225)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(225),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // N
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(226),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(226)).to_start_bound()),
            ),
            // O
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(301)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(301),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // P
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(304),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(304)).to_start_bound()),
            ),
            // Q
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(310),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(310)).to_start_bound()),
            ),
            // R
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(310)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(310),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // S
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(315)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(315),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // T1
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(320),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(320)).to_start_bound()),
            ),
            // T2
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(320)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(320),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // U
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(325)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_inclusivity(
                        SignedDuration::from_hours(325),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
        ],
    );
}

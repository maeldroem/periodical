use jiff::SignedDuration;

use super::relative::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    RelativeBound,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};
use crate::iter::intervals::bounds::RelativeBoundsIteratorDispatcher;
use crate::iter::intervals::layered_bounds::rel_state_change::LayeredBoundsStateChangeAtRelativeBound;
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

#[test]
fn create() {
    let first_layer_data = [
        RelativeBound::Start(RelativeStartBound::InfinitePast),
        RelativeBound::Start(RelativeFiniteBound::new(SignedDuration::from_hours(101)).to_start_bound()),
        RelativeBound::End(RelativeFiniteBound::new(SignedDuration::from_hours(102)).to_end_bound()),
        RelativeBound::Start(RelativeFiniteBound::new(SignedDuration::from_hours(105)).to_start_bound()),
        RelativeBound::End(RelativeEndBound::InfiniteFuture),
    ];

    let second_layer_data = [
        RelativeBound::Start(RelativeStartBound::InfinitePast),
        RelativeBound::Start(RelativeFiniteBound::new(SignedDuration::from_hours(101)).to_start_bound()),
        RelativeBound::End(RelativeFiniteBound::new(SignedDuration::from_hours(102)).to_end_bound()),
        RelativeBound::Start(RelativeFiniteBound::new(SignedDuration::from_hours(105)).to_start_bound()),
        RelativeBound::End(RelativeEndBound::InfiniteFuture),
    ];

    let _ = LayeredRelativeBounds::new(first_layer_data.into_iter(), second_layer_data.into_iter());
}

#[allow(clippy::too_many_lines)]
#[test]
fn run() {
    // first layer:  [--1--]            [--3--]             (--6--]  [--7--] [--9--)(--11-] [-13-]
    // second layer:           [--2--]        (--4--] [--5--]           [--8--] [10)(--12---]
    let first_layer_data = [
        // 1
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(101)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(105)).to_end_bound(),
        ),
        // 3
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(117)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(120)).to_end_bound(),
        ),
        // 6
        RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(205), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(210)).to_end_bound(),
        ),
        // 7
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(215)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(225)).to_end_bound(),
        ),
        // 9
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(226)).to_start_bound(),
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(310), BoundInclusivity::Exclusive)
                .to_end_bound(),
        ),
        // 11
        RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(310), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(315)).to_end_bound(),
        ),
        // 13
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(320)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(325)).to_end_bound(),
        ),
    ];

    let second_layer_data = [
        // 2
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(110)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(115)).to_end_bound(),
        ),
        // 4
        RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(120), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(125)).to_end_bound(),
        ),
        // 5
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(130)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(205)).to_end_bound(),
        ),
        // 8
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(220)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(301)).to_end_bound(),
        ),
        // 10
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(304)).to_start_bound(),
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(310), BoundInclusivity::Exclusive)
                .to_end_bound(),
        ),
        // 12
        RelativeBoundPair::new(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(310), BoundInclusivity::Exclusive)
                .to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(320)).to_end_bound(),
        ),
    ];

    let mut first_layer_bounds = first_layer_data.rel_bounds_iter().collect::<Vec<_>>();
    let mut second_layer_bounds = second_layer_data.rel_bounds_iter().collect::<Vec<_>>();

    first_layer_bounds.sort();
    second_layer_bounds.sort();

    // first layer:    [--1--]            [--3--]             (--6--]  [--7--]  [---9--)(--11-] [-13-]
    // second layer:   :     :   [--2--]  :     (--4--] [--5--]     :  :  [---8---] [10)(--12---]
    // change refs:    A     B   C     D  E     F     G H     I     J  K  L  M  N O P  QR     S T    U
    assert_eq!(
        LayeredRelativeBounds::new(first_layer_bounds.into_iter(), second_layer_bounds.into_iter(),)
            .collect::<Vec<_>>(),
        vec![
            // A
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(101),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(101)).to_start_bound()),
            ),
            // B
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(105)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(105),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // C
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(110),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(110)).to_start_bound()),
            ),
            // D
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(115)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(115),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // E
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(117),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(117)).to_start_bound()),
            ),
            // F
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(120)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(120),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // G
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(125)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(125),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // H
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(130),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(130)).to_start_bound()),
            ),
            // I
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(205)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(205),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // J
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(210)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(210),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // K
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(215),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(215)).to_start_bound()),
            ),
            // L
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(220),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(220)).to_start_bound()),
            ),
            // M
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(225)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(225),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // N
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(226),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(226)).to_start_bound()),
            ),
            // O
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(301)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(301),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // P
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(304),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(304)).to_start_bound()),
            ),
            // Q
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(310),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(310)).to_start_bound()),
            ),
            // R
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(310)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(310),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // S
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(315)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(315),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // T1
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(320),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(320)).to_start_bound()),
            ),
            // T2
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(320)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(320),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // U
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeFiniteBound::new(SignedDuration::from_hours(325)).to_end_bound()),
                Some(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(325),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
        ],
    );
}

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
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
            SignedDuration::from_hours(101),
        ))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
            SignedDuration::from_hours(102),
        ))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
            SignedDuration::from_hours(105),
        ))),
        RelativeBound::End(RelativeEndBound::InfiniteFuture),
    ];

    let second_layer_data = [
        RelativeBound::Start(RelativeStartBound::InfinitePast),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
            SignedDuration::from_hours(101),
        ))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
            SignedDuration::from_hours(102),
        ))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
            SignedDuration::from_hours(105),
        ))),
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
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(101))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(105))),
        ),
        // 3
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(117))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(120))),
        ),
        // 6
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(205),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(210))),
        ),
        // 7
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(215))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(225))),
        ),
        // 9
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(226))),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 11
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(315))),
        ),
        // 13
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(320))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(325))),
        ),
    ];

    let second_layer_data = [
        // 2
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(110))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(115))),
        ),
        // 4
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(120),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(125))),
        ),
        // 5
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(130))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(205))),
        ),
        // 8
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(220))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(301))),
        ),
        // 10
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(304))),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 12
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(310),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(320))),
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
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(101)
                ))),
            ),
            // B
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(105)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(105),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // C
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(110),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(110)
                ))),
            ),
            // D
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(115)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(115),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // E
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(117),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(117)
                ))),
            ),
            // F
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(120)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(120),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // G
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(125)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(125),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // H
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(130),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(130)
                ))),
            ),
            // I
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(205)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(205),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // J
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(210)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(210),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // K
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(215),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(215)
                ))),
            ),
            // L
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(220),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(220)
                ))),
            ),
            // M
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(225)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(225),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // N
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(226),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(226)
                ))),
            ),
            // O
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(301)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(301),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // P
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(304),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(304)
                ))),
            ),
            // Q
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(310),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(310)
                ))),
            ),
            // R
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(310)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(310),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // S
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(315)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(315),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // T1
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(320),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(320)
                ))),
            ),
            // T2
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(320)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(320),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // U
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(325)
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(325),
                    BoundInclusivity::Exclusive,
                ))),
            ),
        ],
    );
}

use std::error::Error;

use jiff::Zoned;

use super::absolute::*;
use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
use crate::iter::intervals::layered_bounds::abs_state_change::LayeredBoundsStateChangeAtAbsoluteBound;
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

#[test]
fn create() -> Result<(), Box<dyn Error>> {
    let first_layer_data = [
        AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))),
        AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
    ];

    let second_layer_data = [
        AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
            "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
        ))),
        AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
    ];

    let _ = LayeredAbsoluteBounds::new(first_layer_data.into_iter(), second_layer_data.into_iter());

    Ok(())
}

#[allow(clippy::too_many_lines)]
#[test]
fn run() -> Result<(), Box<dyn Error>> {
    // first layer:  [--1--]            [--3--]             (--6--]  [--7--] [--9--)(--11-] [-13-]
    // second layer:           [--2--]        (--4--] [--5--]           [--8--] [10)(--12---]
    let first_layer_data = [
        // 1
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 7
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 9
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 11
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 13
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
    ];

    let second_layer_data = [
        // 2
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 8
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 10
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 12
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
    ];

    let mut first_layer_bounds = first_layer_data.abs_bounds_iter().collect::<Vec<_>>();
    let mut second_layer_bounds = second_layer_data.abs_bounds_iter().collect::<Vec<_>>();

    first_layer_bounds.sort();
    second_layer_bounds.sort();

    // first layer:    [--1--]            [--3--]             (--6--]  [--7--]  [---9--)(--11-] [-13-]
    // second layer:   :     :   [--2--]  :     (--4--] [--5--]     :  :  [---8---] [10)(--12---]
    // change refs:    A     B   C     D  E     F     G H     I     J  K  L  M  N O P  QR     S T    U
    assert_eq!(
        LayeredAbsoluteBounds::new(first_layer_bounds.into_iter(), second_layer_bounds.into_iter(),)
            .collect::<Vec<_>>(),
        vec![
            // A
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // B
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // C
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // D
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // E
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // F
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // G
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // H
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // I
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // J
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // K
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // L
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // M
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // N
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // O
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // P
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // Q
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // R
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // S
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // T1
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
            ),
            // T2
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // U
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
        ],
    );

    Ok(())
}
